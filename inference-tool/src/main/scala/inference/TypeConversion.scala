import java.nio.file.{ Files, Paths }
import java.io._
import sys.process._
import scala.io.Source
import com.microsoft.z3._
import org.apache.commons.math3.fraction.BigFraction
import org.jgrapht.Graph
import org.jgrapht.graph.{ DefaultEdge, SimpleDirectedGraph }
import org.jgrapht.Graphs
import scala.util.control.Exception.allCatch
import scala.collection.JavaConverters._

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
  def mkDiv(a: AExp.aexp[VName.vname], b: AExp.aexp[VName.vname]): AExp.aexp[VName.vname] = AExp.Divide(a, b)

  def mkAnd(a: GExp.gexp[VName.vname], b: GExp.gexp[VName.vname]): GExp.gexp[VName.vname] = GExp.gAnd(a, b)
  def mkOr(a: GExp.gexp[VName.vname], b: GExp.gexp[VName.vname]): GExp.gexp[VName.vname] = GExp.gOr(a, b)

  def toGExp(nodes: List[Int], edges: List[(Int, Int)], labels: Map[Int, String]): GExp.gexp[VName.vname] = {
    val expGraph: Graph[Int, DefaultEdge] = new SimpleDirectedGraph(classOf[DefaultEdge])
    for (node <- nodes) {
      expGraph.addVertex(node)
    }
    for ((source, target) <- edges) {
      expGraph.addEdge(source, target)
    }
    println(expGraph)
    return toGExpAux(expGraph, 0, labels)
    throw new IllegalStateException(f"Cannot convert to aexp")
  }

  def value_type(s: String): PTA_Generalisation.value_type = s match {
    case "I" => PTA_Generalisation.I()
    case "R" => PTA_Generalisation.R()
    case "S" => PTA_Generalisation.S()
  }

  def toGExpAux[N, E](graph: Graph[N, E], root: N, labels: Map[N, String]): GExp.gexp[VName.vname] = {
    val children = Graphs.successorListOf(graph, root).asScala
    assert(children.length <= 2, f"We only support binary operators, not ${children}")
    val c1 = children(0)
    labels(root) match {
      case "and_" => {
        val c2 = children(1)
        return mkAnd(toGExpAux(graph, c1, labels), toGExpAux(graph, c2, labels))
      }
      case "or_" => {
        val c2 = children(1)
        return mkOr(toGExpAux(graph, c1, labels), toGExpAux(graph, c2, labels))
      }
      case "not_" => {
        return GExp.gNot(toGExpAux(graph, c1, labels))
      }
      case "le" => {
        val c2 = children(1)
        return GExp.Le(toAExpAux(graph, c1, labels), toAExpAux(graph, c2, labels))
      }
      case "lt" => {
        val c2 = children(1)
        return GExp.Lt(toAExpAux(graph, c1, labels), toAExpAux(graph, c2, labels))
      }
      case "ge" => {
        val c2 = children(1)
        return GExp.Gt(toAExpAux(graph, c1, labels), toAExpAux(graph, c2, labels))
      }
      case "gt" => {
        val c2 = children(1)
        return GExp.Ge(toAExpAux(graph, c1, labels), toAExpAux(graph, c2, labels))
      }
      case "eq" => {
        val c2 = children(1)
        return GExp.Eq(toAExpAux(graph, c1, labels), toAExpAux(graph, c2, labels))
      }
      case _ => throw new IllegalArgumentException(f"Invalid operator $root in $labels")
    }
  }

  def toAExp(nodes: List[Int], edges: List[(Int, Int)], labels: Map[Int, String]): AExp.aexp[VName.vname] = {
    val expGraph: Graph[Int, DefaultEdge] = new SimpleDirectedGraph(classOf[DefaultEdge])
    for (node <- nodes) {
      expGraph.addVertex(node)
    }
    for ((source, target) <- edges) {
      expGraph.addEdge(source, target)
    }
    println(expGraph)
    return toAExpAux(expGraph, 0, labels)
    throw new IllegalStateException(f"Cannot convert to aexp")
  }

  def isLongNumber(s: String): Boolean = (allCatch opt s.toLong).isDefined
  def isDoubleNumber(s: String): Boolean = (allCatch opt s.toDouble).isDefined

  def toAExpAux[N, E](graph: Graph[N, E], root: N, labels: Map[N, String]): AExp.aexp[VName.vname] = {
    val children = Graphs.successorListOf(graph, root)
    if (children.size == 0) {
      val name = labels(root)
      if (name.startsWith("i")) {
        return AExp.V(VName.I(Nat.Nata(name.drop(1).toLong)))
      } else if (name.startsWith("r")) {
        return AExp.V(VName.R(Nat.Nata(name.drop(1).toLong)))
      } else if (isLongNumber(name)) {
        return AExp.L(toValue(name.toLong))
      } else if (isDoubleNumber(name)) {
        return AExp.L(toValue(name.toDouble))
      } else {
        return AExp.L(toValue(name))
      }
    }

    val nested = children.asScala.map(v => toAExpAux(graph, v, labels))
    assert(nested.length == 2, "We only support binary operators")
    val c1 = nested(0)
    val c2 = nested(1)
    labels(root) match {
      case "add" => {
        return mkAdd(c1, c2)
      }
      case "sub" => {
        return mkSub(c1, c2)
      }
      case "mul" => {
        return mkMul(c1, c2)
      }
      case "div" => {
        return mkDiv(c1, c2)
      }
      case _ => throw new IllegalArgumentException(f"Invalid operator ${root}")
    }
  }

  // def toAExp(best: Node[VariableAssignment[_]]): AExp.aexp[VName.vname] = {
  //   val ctx = new com.microsoft.z3.Context()
  //   val aexp = aexpFromZ3(best.toZ3(ctx))
  //   ctx.close
  //   return aexp
  // }

  // def toGExp(best: Node[VariableAssignment[_]]): GExp.gexp[VName.vname] = {
  //   val ctx = new com.microsoft.z3.Context()
  //   val gexp = gexpFromZ3(best.toZ3(ctx))
  //   ctx.close
  //   return gexp
  // }

  def expandTypeString(t: String): String = {
    if (t == ":S")
      return "String"
    else if (t == ":I")
      return "Int"
    else if (t == ":D")
      return "Real"
    else
      throw new IllegalArgumentException("Type string must be either :I or :S")
  }

  def typeString(v: Value.value): String = v match {
    case Value.Inta(_) => "Int"
    case Value.Str(_) => "String"
    case Value.Reala(_) => "Real"
  }

  def vnameFromString(name: String): VName.vname = {
    if (name.startsWith("i")) {
      return VName.I(Nat.Nata(name.drop(1).toInt))
    } else if (name.startsWith("r")) {
      return VName.R(Nat.Nata(name.drop(1).toInt))
    } else {
      throw new IllegalArgumentException(s"""Cannot convert $name. Variables must be of the form \"(i|r)\\d*\"""")
    }
  }

  def makeBinaryGExp(e: List[Expr], f: (GExp.gexp[VName.vname] => GExp.gexp[VName.vname] => GExp.gexp[VName.vname])): GExp.gexp[VName.vname] = e match {
    case Nil => throw new IllegalArgumentException("Not enough children")
    case (a :: b :: Nil) => f(gexpFromZ3(a))(gexpFromZ3(b))
    case (a :: bs) => f(gexpFromZ3(a))(makeBinaryGExp(bs, f))
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
        aexpFromZ3(e.getArgs()(1)))
    }
    if (e.isGT) {
      return GExp.Gt(
        aexpFromZ3(e.getArgs()(0)),
        aexpFromZ3(e.getArgs()(1)))
    }
    if (e.isEq) {
      return GExp.Eq(
        aexpFromZ3(e.getArgs()(0)),
        aexpFromZ3(e.getArgs()(1)))
    }
    if (e.isTrue) {
      return GExp.Bc(true)
    }
    if (e.isFalse) {
      return GExp.Bc(false)
    }
    throw new IllegalArgumentException("Couldn't convert from z3 expression " + e)
  }

  def makeBinaryAExp(e: List[Expr], f: (AExp.aexp[VName.vname] => AExp.aexp[VName.vname] => AExp.aexp[VName.vname])): AExp.aexp[VName.vname] = e match {
    case Nil => throw new IllegalArgumentException("Not enough children")
    case (a :: b :: Nil) => f(aexpFromZ3(a))(aexpFromZ3(b))
    case (a :: bs) => f(aexpFromZ3(a))(makeBinaryAExp(bs, f))
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
      } else {
        return AExp.L(Value.Str(e.toString.replaceAll("^\"|\"$", "")))
      }
    }
    if (e.isIntNum()) {
      return AExp.L(Value.Inta(Int.int_of_integer(e.toString.toLong)))
    }

    throw new IllegalArgumentException("Couldn't convert from z3 expression " + e)
  }

  def toVName(vname: String): VName.vname = {
    if (vname.startsWith("i")) {
      val index = Nat.Nata(BigInt(vname.substring(1).toInt - 1))
      VName.I(index)
    } else {
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

  def to_real(x: Double): Real.real = {
    return Real.Ratreal(rat_of_double(x))
  }

  def toDouble(x: Rat.rat): Double = x match {
    case Rat.Frct((Int.int_of_integer(num), Int.int_of_integer(den))) => {
      val frac = new BigFraction(new java.math.BigInteger(num.toString), new java.math.BigInteger(den.toString))
      return frac.doubleValue()
    }
  }

  def toDouble(x: Real.real): Double = x match {
    case Real.Ratreal(rat) => toDouble(rat)
  }

  def toValue(n: BigInt): Value.value = Value.Inta(Int.int_of_integer(n))
  def toValue(n: Long): Value.value = Value.Inta(Int.int_of_integer(n))
  def toValue(s: String): Value.value = Value.Str(s)
  def toValue(d: Double): Value.value = Value.Reala(Real.Ratreal(rat_of_double(d)))
  def toValue(e: Expr): Value.value = {
    if (e.isIntNum())
      return Value.Inta(Int.int_of_integer(e.toString.toInt))
    if (e.isRatNum())
      return Value.Reala(Real.Ratreal(Rat.Frct((Int.int_of_integer(e.asInstanceOf[RatNum].getNumerator.toString.toLong), Int.int_of_integer(e.asInstanceOf[RatNum].getDenominator.toString.toLong)))))
    else if (e.isString()) {
      val str = e.toString.slice(1, e.toString.length - 1)
      return Value.Str(str)
    } else if (e.isAlgebraicNumber()) {
      return Value.Reala(to_real(e.asInstanceOf[AlgebraicNum].toDecimal(16).replace("?", "").toDouble))
    } else
      throw new IllegalArgumentException(f"Expressions can only be String, RatNum, or IntNum, not ${e}:${e.getClass.getName}");
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
      throw new IllegalArgumentException(s"Invalid type ${a.getClass}. Can only be z3.Expr or a Value type (String, Double, or BigInt), not ${a.getClass().getName()}");
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
