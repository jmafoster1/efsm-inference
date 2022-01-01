import java.nio.file.{ Files, Paths }
import java.io._
import sys.process._
import scala.io.Source
import com.microsoft.z3._
import org.apache.commons.math3.fraction.BigFraction;

import mint.tracedata.types.VariableAssignment;
import mint.tracedata.types.IntegerVariableAssignment;
import mint.tracedata.types.StringVariableAssignment;
import mint.inference.gp.tree.Node;

object Types {
  type Event = (String, (List[Value.value], List[Value.value]))
  type Transition = Transition.transition_ext[Unit]
  type TransitionMatrix = FSet.fset[((Nat.nat, Nat.nat), Transition)]
  type IEFSM = FSet.fset[(List[Nat.nat], ((Nat.nat, Nat.nat), Transition))]
}

object TypeConversion {
  def mkAdd(a: AExp.aexp[VName.vname], b: AExp.aexp[VName.vname]): AExp.aexp[VName.vname] = AExp.Plus(a, b)
  def mkSub(a: AExp.aexp[VName.vname], b: AExp.aexp[VName.vname]): AExp.aexp[VName.vname] = AExp.Minus(a, b)
  def mkMul(a: AExp.aexp[VName.vname], b: AExp.aexp[VName.vname]): AExp.aexp[VName.vname] = AExp.Times(a, b)

  def mkAnd(a: GExp.gexp[VName.vname], b: GExp.gexp[VName.vname]): GExp.gexp[VName.vname] = GExp.gAnd(a, b)
  def mkOr(a: GExp.gexp[VName.vname], b: GExp.gexp[VName.vname]): GExp.gexp[VName.vname] = GExp.gOr(a, b)

  def toAExp(best: Node[VariableAssignment[_]]): AExp.aexp[VName.vname] = {
    val ctx = new com.microsoft.z3.Context()
    val aexp = aexpFromZ3(best.toZ3(ctx))
    ctx.close
    return aexp
  }

  def toGExp(best: Node[VariableAssignment[_]]): GExp.gexp[VName.vname] = {
    val ctx = new com.microsoft.z3.Context()
    val gexp = gexpFromZ3(best.toZ3(ctx))
    ctx.close
    return gexp
  }

  def expandTypeString(t: String): String = {
    if (t == ":S")
      return "String"
    else if (t == ":I")
      return "Int"
    else
      throw new IllegalArgumentException("Type string must be either :I or :S")
  }

  def typeString(v: Value.value): String = v match {
    case Value.Inta(_) => "Int"
    case Value.Str(_) => "String"
  }

  def vnameFromString(name: String):VName.vname = {
    if (name.startsWith("i")) {
        return VName.I(Nat.Nata(name.drop(1).toInt))
      } else if (name.startsWith("r")) {
        return VName.R(Nat.Nata(name.drop(1).toInt))
      }
      else {
        throw new IllegalArgumentException(s"""Cannot convert $name. Variables must be of the form \"(i|r)\\d*\"""")
      }
  }

  def makeBinaryGExp(e: List[Expr], f: (GExp.gexp[VName.vname] => GExp.gexp[VName.vname] => GExp.gexp[VName.vname])): GExp.gexp[VName.vname] = e match {
    case Nil => throw new IllegalArgumentException("Not enough children")
    case (a::b::Nil) => f(gexpFromZ3(a))(gexpFromZ3(b))
    case (a::bs) => f(gexpFromZ3(a))(makeBinaryGExp(bs, f))
  }

  def gexpFromZ3(e: Expr): GExp.gexp[VName.vname] = {
    if (e.isAnd) {
      return makeBinaryGExp(e.getArgs().toList, (mkAnd _).curried)
    }
    if (e.isOr) {
      return makeBinaryGExp(e.getArgs().toList, (mkOr _).curried)
    }
    if (e.isNot) {
      return GExp.gNot(gexpFromZ3(e.getArgs()(0)))
    }
    if (e.isLT) {
      return GExp.Lt(
        aexpFromZ3(e.getArgs()(0)),
        aexpFromZ3(e.getArgs()(1))
      )
    }
    if (e.isGT) {
      return GExp.Gt(
        aexpFromZ3(e.getArgs()(0)),
        aexpFromZ3(e.getArgs()(1))
      )
    }
    if (e.isEq) {
      return GExp.Eq(
        aexpFromZ3(e.getArgs()(0)),
        aexpFromZ3(e.getArgs()(1))
      )
    }
    if (e.isTrue) {
      return GExp.Bc(true)
    }
    if (e.isFalse) {
      return GExp.Bc(false)
    }
    throw new IllegalArgumentException("Couldn't convert from z3 expression "+e)
  }

  def makeBinaryAExp(e: List[Expr], f: (AExp.aexp[VName.vname] => AExp.aexp[VName.vname] => AExp.aexp[VName.vname])): AExp.aexp[VName.vname] = e match {
    case Nil => throw new IllegalArgumentException("Not enough children")
    case (a::b::Nil) => f(aexpFromZ3(a))(aexpFromZ3(b))
    case (a::bs) => f(aexpFromZ3(a))(makeBinaryAExp(bs, f))
  }

  def aexpFromZ3(e: Expr): AExp.aexp[VName.vname] = {
    if (e.isAdd) {
      return makeBinaryAExp(e.getArgs().toList, (mkAdd _).curried)
    }
    if (e.isSub) {
      return makeBinaryAExp(e.getArgs().toList, (mkSub _).curried)
    }
    if (e.isMul) {
      return makeBinaryAExp(e.getArgs().toList, (mkMul _).curried)
    }
    if (e.isConst) {
      val name = e.toString.replace("latent", "")
      // TODO: This is hacky at best
      if (name.startsWith("i")) {
        return AExp.V(VName.I(Nat.Nata(name.drop(1).toLong)))
      } else if (name.startsWith("r")) {
        return AExp.V(VName.R(Nat.Nata(name.drop(1).toLong)))
      }
      else {
        return AExp.L(Value.Str(e.toString.replaceAll("^\"|\"$", "")))
      }
    }
		if (e.isIntNum()) {
      return AExp.L(Value.Inta(Int.int_of_integer(e.toString.toLong)))
    }

    throw new IllegalArgumentException("Couldn't convert from z3 expression "+e)
  }

  def toVName(vname: String): VName.vname = {
    if (vname.startsWith("i")) {
      val index = Nat.Nata(BigInt(vname.substring(1).toInt - 1))
      VName.I(index)
    }
    else {
      val index = Nat.Nata(BigInt(vname.substring(1).toInt))
      VName.R(index)
    }
  }

  def toInt(b: BigInt): Int = {
    if (b.isValidInt) {
      return b.toInt
    } else {
      throw new IllegalArgumentException(s"${b} is not a valid int")
    }
  }

  def toInt(n: Nat.nat): Int = n match {
    case Nat.Nata(nn) => toInt(nn)
  }

  def toInteger(i: Int.int): Integer = {
    val b = Code_Numeral.integer_of_int(i)
    if (b.isValidInt) {
      return b.toInt
    } else {
      throw new IllegalArgumentException(s"${b} is not a valid int")
    }
  }

  def toLong(i: Int.int): Long = {
    val b = Code_Numeral.integer_of_int(i)
    if (b.isValidLong) {
      return b.toLong
    } else {
      throw new IllegalArgumentException(s"${b} is not a valid int")
    }
  }

  def toInteger(b: BigInt): Integer = {
    if (b.isValidInt) {
      return b.toInt
    } else {
      throw new IllegalArgumentException(s"${b} is not a valid int")
    }
  }

  def toLong(b: BigInt): Long = {
    if (b.isValidLong) {
      return b.toLong
    } else {
      throw new IllegalArgumentException(s"${b} is not a valid long")
    }
  }

  def rat_of_double(x: Double): Rat.rat = {
    val frac = new BigFraction(x);
    val (num, den) = (frac.getNumerator(), frac.getDenominator())

      return Rat.Frct((Int.int_of_integer(num), Int.int_of_integer(den)))
  }

  def double_of_rat(x: Rat.rat): Double = x match {
    case Rat.Frct((Int.int_of_integer(num),Int.int_of_integer(den))) => {
      val frac = new BigFraction(new java.math.BigInteger(num.toString), new java.math.BigInteger(den.toString))
      return frac.doubleValue()
    }
  }

  def toValue(n: BigInt): Value.value = Value.Inta(Int.int_of_integer(n))
  def toValue(n: Long): Value.value = Value.Inta(Int.int_of_integer(n))
  def toValue(s: String): Value.value = Value.Str(s)
  def toValue(d: Double): Value.value = Value.Float(Real.Ratreal(rat_of_double(d)))
  def toValue(e: Expr): Value.value = {
    if (e.isIntNum())
      return Value.Inta(Int.int_of_integer(e.toString.toInt))
    else if (e.isString()) {
      val str = e.toString.slice(1, e.toString.length-1)
      return Value.Str(str)
    }
    else
      throw new IllegalArgumentException("Expressions can only be String or IntNum");
  }

  def toValue(a: Any): Value.value = {
    if (a.isInstanceOf[String]) {
      toValue(a.asInstanceOf[String])
    } else if (a.isInstanceOf[BigInt]) {
      toValue(a.asInstanceOf[BigInt])
    } else if (a.isInstanceOf[Double]) {
      toValue(a.asInstanceOf[Double])
    } else if (a.isInstanceOf[Expr]) {
      toValue(a.asInstanceOf[Expr])
    } else {
      throw new IllegalArgumentException(s"Invalid type ${a.getClass}. Can only be z3.Expr or a Value type (String, Float, or BigInt), not ${a.getClass().getName()}");
    }
  }

  def toEventTuple(e: Map[String, Any]): Types.Event = {
    (
      (e("label").asInstanceOf[String]),
      (e("inputs").asInstanceOf[List[Any]].map(x => toValue(x)),
        e("outputs").asInstanceOf[List[Any]].map(x => toValue(x))))
  }

  def indexWithInts(e: List[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]): List[((Int, Int), Transition.transition_ext[Unit])] =
    e.map(move => ((toInt(Code_Numeral.integer_of_nat(move._1._1)), toInt(Code_Numeral.integer_of_nat(move._1._2))), move._2))
}
