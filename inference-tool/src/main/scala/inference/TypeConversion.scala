import java.nio.file.{ Files, Paths }
import java.io._
import sys.process._
import scala.io.Source
import com.microsoft.z3._

import isabellesal._

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
  def mkAdd(a: AExp.aexp, b: AExp.aexp): AExp.aexp = AExp.Plus(a, b)
  def mkSub(a: AExp.aexp, b: AExp.aexp): AExp.aexp = AExp.Minus(a, b)

  def toAExp(best: Node[VariableAssignment[_]]): AExp.aexp = {
    val ctx = new Context()
    val aexp = TypeConversion.fromZ3(best.toZ3(ctx))
    ctx.close
    return aexp
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
    case Value.Numa(_) => "Int"
    case Value.Str(_) => "String"
  }

  def vnameFromString(name: String):VName.vname = {
    if (name.startsWith("i")) {
        return VName.I(Nat.Nata(name.drop(1).toInt))
      } else if (name.startsWith("r")) {
        return VName.R(Nat.Nata(name.drop(1).toInt))
      }
      else {
        throw new IllegalArgumentException("variables must be of the form \"(i|r)\\d*\"")
      }
  }

  def makeBinary(e: List[Expr], f: (AExp.aexp => AExp.aexp => AExp.aexp)): AExp.aexp = e match {
    case Nil => throw new IllegalArgumentException("Not enough children")
    case (a::b::Nil) => f(fromZ3(a))(fromZ3(b))
    case (a::bs) => f(fromZ3(a))(makeBinary(bs, f))
  }

  def fromZ3(e: Expr): AExp.aexp = {
    if (e.isAdd) {
      return makeBinary(e.getArgs().toList, (mkAdd _).curried)
    }
    if (e.isSub) {
      return makeBinary(e.getArgs().toList, (mkSub _).curried)
    }
    if (e.isConst) {
      val name = e.toString
      // TODO: This is hacky at best
      if (name.startsWith("i")) {
        return AExp.V(VName.I(Nat.Nata(name.drop(1).toInt)))
      } else if (name.startsWith("r")) {
        return AExp.V(VName.R(Nat.Nata(name.drop(1).toInt)))
      }
      else {
        return AExp.L(Value.Str(e.toString))
      }
    }
		if (e.isIntNum()) {
      return AExp.L(Value.Numa(Int.int_of_integer(e.toString.toInt)))
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

  def toValue(n: BigInt): Value.value = Value.Numa(Int.int_of_integer(n))
  def toValue(s: String): Value.value = Value.Str(s)
  def toValue(e: Expr): Value.value = {
    if (e.isIntNum())
      return Value.Numa(Int.int_of_integer(e.toString.toInt))
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
    } else if (a.isInstanceOf[Expr]) {
      toValue(a.asInstanceOf[Expr])
    } else {
      throw new IllegalArgumentException("Can only be String or BigInt");
    }
  }

  def toEventTuple(e: Map[String, Any]): Types.Event = {
    (
      (e("label").asInstanceOf[String]),
      (e("inputs").asInstanceOf[List[Any]].map(x => toValue(x)),
        e("outputs").asInstanceOf[List[Any]].map(x => toValue(x))))
  }

  def vnameToSALTranslator(v: VName.vname): Variable = {
    v match {
      case VName.I(Nat.Nata(n)) => isabellesal.Variable.newOneFrom('I', n.toLong + 1)
      case VName.R(Nat.Nata(n)) => isabellesal.Variable.newOneFrom('R', n.toLong)
    }
  }

  def aexpToSALTranslator(a: AExp.aexp): isabellesal.Expression = a match {
    case AExp.L(Value.Numa(Int.int_of_integer(n))) => isabellesal.Expression.newOneFrom(isabellesal.Constant.newOneFrom(toLong(n)))
    case AExp.L(Value.Str(s)) => isabellesal.Expression.newOneFrom(isabellesal.Constant.newOneFrom(s))
    case AExp.V(v) => isabellesal.Expression.newOneFrom(vnameToSALTranslator(v))
    case AExp.Plus(a1, a2) => isabellesal.Expression.newInfixFrom(
      Token.PLUS,
      aexpToSALTranslator(a1),
      aexpToSALTranslator(a2))
    case AExp.Minus(a1, a2) => isabellesal.Expression.newInfixFrom(
      Token.MINUS,
      aexpToSALTranslator(a1),
      aexpToSALTranslator(a2))
  }

  def gexpToSALTranslator(g: GExp.gexp): isabellesal.Predicate = g match {
    case GExp.Bc(v) => throw new java.lang.IllegalArgumentException("Can't translate boolean values")
    case GExp.Null(AExp.V(a)) => isabellesal.Predicate.newNullTest(vnameToSALTranslator(a))
    case GExp.Null(a) => throw new java.lang.IllegalArgumentException("Can only translate null guards of variables")
    // case GExp.In(v, l) => gexpToSALTranslator(GExp.fold_In(v, l))
    case GExp.In(v, Nil) => throw new java.lang.IllegalArgumentException("Can't translate empty membership")
    case GExp.In(v, l :: Nil) => isabellesal.Predicate.newInfixFrom(
      Token.EQUALS,
      isabellesal.Expression.newOneFrom(vnameToSALTranslator(v)),
      aexpToSALTranslator(AExp.L(l))
    )
    case GExp.In(v, l :: t) => isabellesal.Predicate.newInfixFrom(
      Token.OR,
      isabellesal.Predicate.newInfixFrom(
        Token.EQUALS,
        isabellesal.Expression.newOneFrom(vnameToSALTranslator(v)),
        aexpToSALTranslator(AExp.L(l))
      ),
      gexpToSALTranslator(GExp.In(v, t))
    )
    case GExp.Eq(a1, a2) => isabellesal.Predicate.newInfixFrom(
      Token.EQUALS,
      aexpToSALTranslator(a1),
      aexpToSALTranslator(a2))
    case GExp.Gt(a1, a2) => isabellesal.Predicate.newInfixFrom(
      Token.GT,
      aexpToSALTranslator(a1),
      aexpToSALTranslator(a2))
    case GExp.Nor(g1, g2) => isabellesal.Predicate.newInfixFrom(
      Token.NOR,
      gexpToSALTranslator(g1),
      gexpToSALTranslator(g2))
  }

  def updateToExp(u: (Nat.nat, AExp.aexp)): Assignment = u match {
    case (r, a) => Assignment.newOne(
      vnameToSALTranslator(VName.R(r)),
      aexpToSALTranslator(a))
  }

  def transitionToSALTranslator(id: String, t: Transition.transition_ext[Unit]): isabellesal.Transition = {
    isabellesal.Transition.newOneFrom(
      id,
      Transition.Label(t),
      toInt(Code_Numeral.integer_of_nat(Transition.Arity(t))),
      isabellesal.Predicate.listOfPredicatesFrom(Transition.Guard(t).map(gexpToSALTranslator): _*),
      isabellesal.Expression.newOutputs(Transition.Outputs(t).map(aexpToSALTranslator): _*),
      Transition.Updates(t).map(updateToExp): _*)
  }

  def toMichaelsMove(move: ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])): MichaelsMove = {
    new MichaelsMove(
      Code_Numeral.integer_of_nat(move._1._1).toInt,
      Code_Numeral.integer_of_nat(move._1._2).toInt,
      transitionToSALTranslator(Transition.Label(move._2) +
        "_" + System.currentTimeMillis, move._2))
  }

  def efsmToSALTranslator(e: Types.TransitionMatrix, f: String) = {
    Translator.clearEverything()
    isabellesal.EFSM.newOneFrom("MichaelsEFSM", FSet.sorted_list_of_fset(e).map(toMichaelsMove): _*)
    new Translator().writeSALandDOT(Paths.get("salfiles"), f);
    s"mv salfiles/${f}.dot ${Config.config.dotfiles}/".!
  }

  def salValue(v: Value.value): String = v match {
    case Value.Str(s) => s"Str(String__$s)"
    case Value.Numa(n) => s"Num(${Code_Numeral.integer_of_int(n)})"
  }

  def salState(s: Nat.nat): String = s match {
    case Nat.Nata(n) => s"State__${n}"
  }

  def doubleEFSMToSALTranslator(e1: Types.TransitionMatrix, e1Name: String, e2: Types.TransitionMatrix, e2Name: String, f: String, delete: Boolean = true) = {
    if (e1Name == e2Name) {
      throw new IllegalArgumentException("Models must have unique names");
    }
    Translator.clearEverything()
    isabellesal.EFSM.newOneFrom(e1Name, FSet.sorted_list_of_fset(e1).map(toMichaelsMove): _*)
    isabellesal.EFSM.newOneFrom(e2Name, FSet.sorted_list_of_fset(e2).map(toMichaelsMove): _*)
    new Translator().writeSALandDOT(Paths.get("salfiles"), f);
    if (delete) {
      s"rm salfiles/${f}.dot".!
    }
  }

  def indexWithInts(e: List[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]): List[((Int, Int), Transition.transition_ext[Unit])] =
    e.map(move => ((toInt(Code_Numeral.integer_of_nat(move._1._1)), toInt(Code_Numeral.integer_of_nat(move._1._2))), move._2))
}
