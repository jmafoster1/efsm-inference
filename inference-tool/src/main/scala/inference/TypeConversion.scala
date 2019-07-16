import java.nio.file.{Files, Paths}
import java.io._
import sys.process._

import isabellesal._
import Type_Inference._

object Types {
  type Event = (String, (List[Value.value], List[Value.value]))
  type Transition = Transition.transition_ext[Unit]
  type TransitionMatrix = FSet.fset[((Nat.nat, Nat.nat), Transition)]
  type IEFSM = FSet.fset[(Nat.nat, ((Nat.nat, Nat.nat), Transition))]
}

object TypeConversion {
  def toInt(b: BigInt): Int = {
    if (b.isValidInt) {
      return b.toInt
    }
    else {
      throw new IllegalArgumentException(s"${b} is not a valid int")
    }
  }

  def toLong(b: BigInt): Long = {
    if (b.isValidLong) {
      return b.toLong
    }
    else {
      throw new IllegalArgumentException(s"${b} is not a valid long")
    }
  }

  def toValue(n:BigInt): Value.value = Value.Numa(Int.int_of_integer(n))
  def toValue(s:String): Value.value = Value.Str(s)
  def toValue(a:Any): Value.value = {
    if (a.isInstanceOf[String]) {
      toValue(a.asInstanceOf[String])
    }
    else if (a.isInstanceOf[BigInt]) {
      toValue(a.asInstanceOf[BigInt])
    }
    else {
      throw new IllegalArgumentException("Can only be String or BigInt");
    }
  }

  def toEventTuple(e: Map[String, Any]): Types.Event = {
    (
      (e("label").asInstanceOf[String]),
      (e("inputs").asInstanceOf[List[Any]].map(x => toValue(x)),
      e("outputs").asInstanceOf[List[Any]].map(x => toValue(x)))
    )
  }

  def vnameToSALTranslator(v: VName.vname): Variable = {
    v match {
    case VName.I(Nat.Nata(n)) => Variable.newOneFrom('I', n.toLong+1)
    case VName.R(Nat.Nata(n)) => Variable.newOneFrom('R', n.toLong)
    }
  }

  def aexpToSALTranslator(a: AExp.aexp): Expression = a match {
    case AExp.L(Value.Numa(Int.int_of_integer(n))) => Expression.newOneFrom(Constant.newOneFrom(toLong(n)))
    case AExp.L(Value.Str(s)) => Expression.newOneFrom(Constant.newOneFrom(s))
    case AExp.V(v) => Expression.newOneFrom(vnameToSALTranslator(v))
    case AExp.Plus(a1, a2) => Expression.newInfixFrom(
            Token.PLUS,
            aexpToSALTranslator(a1),
            aexpToSALTranslator(a2)
    )
    case AExp.Minus(a1, a2) => Expression.newInfixFrom(
            Token.MINUS,
            aexpToSALTranslator(a1),
            aexpToSALTranslator(a2)
    )
  }

  def gexpToSALTranslator(g: GExp.gexp): isabellesal.Predicate = g match {
    case GExp.Bc(v) => throw new java.lang.IllegalArgumentException("Can't translate boolean values")
    case GExp.Null(AExp.V(a)) => isabellesal.Predicate.newNullTest(vnameToSALTranslator(a))
    case GExp.Null(a) => throw new java.lang.IllegalArgumentException("Can only translate null guards of variables")
    case GExp.Eq(a1, a2) => isabellesal.Predicate.newInfixFrom(
            Token.EQUALS,
            aexpToSALTranslator(a1),
            aexpToSALTranslator(a2)
          )
    case GExp.Gt(a1, a2) => isabellesal.Predicate.newInfixFrom(
            Token.GT,
            aexpToSALTranslator(a1),
            aexpToSALTranslator(a2)
          )
    case GExp.Nor(g1, g2) => isabellesal.Predicate.newInfixFrom(
              Token.NOR,
              gexpToSALTranslator(g1),
              gexpToSALTranslator(g2)
   )
  }

  def updateToExp(u: (Nat.nat, AExp.aexp)): Assignment = u match {
    case (r, a) => Assignment.newOne(
            vnameToSALTranslator(VName.R(r)),
            aexpToSALTranslator(a)
    )
  }

  def transitionToSALTranslator(id: String, t: Transition.transition_ext[Unit]):isabellesal.Transition = {
    isabellesal.Transition.newOneFrom(
      id,
      Transition.Label(t),
      toInt(Code_Numeral.integer_of_nat(Transition.Arity(t))),
      isabellesal.Predicate.listOfPredicatesFrom(Transition.Guard(t).map(gexpToSALTranslator):_*),
      Expression.newOutputs(Transition.Outputs(t).map(aexpToSALTranslator):_*),
      Transition.Updates(t).map(updateToExp):_*
    )
  }

  def toMichaelsMove(move: ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])): MichaelsMove = {
    new MichaelsMove(
      Code_Numeral.integer_of_nat(move._1._1).toInt,
      Code_Numeral.integer_of_nat(move._1._2).toInt,
      transitionToSALTranslator(Transition.Label(move._2) +
        "_" + System.currentTimeMillis, move._2)
      )
  }

  def efsmToSALTranslator(e: Types.TransitionMatrix, f: String) = {
    Translator.clearEverything()
    isabellesal.EFSM.newOneFrom(FSet.sorted_list_of_fset(e).map(toMichaelsMove):_*)
    try {
      new Translator().writeSALandDOT(Paths.get("salfiles"), f);
      s"mv salfiles/${f}.dot ${Config.config.dotfiles}/".!
    } catch {
      case ioe: java.lang.StringIndexOutOfBoundsException => {}
    }
  }

  def indexWithInts(e: List[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]): List[((Int, Int), Transition.transition_ext[Unit])] =
      e.map(move => ((toInt(Code_Numeral.integer_of_nat(move._1._1)), toInt(Code_Numeral.integer_of_nat(move._1._2))), move._2))
}
