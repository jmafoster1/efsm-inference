import isabellesal._
import java.nio.file.{Files, Paths}
import java.io._

object TypeConversion {

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

  type Event = (String, (List[Value.value], List[Value.value]))
  type TransitionMatrix = FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]

  def toEventTuple(e: Map[String, Any]): Event = {
    (
      (e("label").asInstanceOf[String]),
      (e("inputs").asInstanceOf[List[Any]].map(x => toValue(x)),
      e("outputs").asInstanceOf[List[Any]].map(x => toValue(x)))
    )
  }

  // This is hypothetical and will break until we get Siobhan's source code
  def vnameToSALTranslator(v: VName.vname): Variable = v match {
    case VName.I(Nat.Nata(n)) => Variable.newOneFrom('I', n.toInt)
    case VName.R(Nat.Nata(n)) => Variable.newOneFrom('R', n.toInt)
  }

  def aexpToSALTranslator(a: AExp.aexp): Expression = a match {
    case AExp.L(Value.Numa(Int.int_of_integer(n))) => Expression.newOneFrom(Constant.newOneFrom(n.toInt))
    case AExp.L(Value.Str(s)) =>
    try {
      Expression.newOneFrom(Constant.newOneFrom(s))
    }
    catch {
      case ioe: java.lang.ClassCastException => Expression.newOneFrom(Constant.currentVersionOf(s))
    }
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

  def gexpToSALTranslator(g: GExp.gexp): Expression = g match {
    case GExp.Bc(v) => throw new java.lang.IllegalArgumentException("Can't translate boolean values")
    case GExp.Null(AExp.V(a)) => Expression.isNull(vnameToSALTranslator(a))
    case GExp.Null(a) => throw new java.lang.IllegalArgumentException("Can only translate null guards of variables")
    case GExp.Eq(a1, a2) => Expression.newInfixFrom(
            Token.EQUALS,
            aexpToSALTranslator(a1),
            aexpToSALTranslator(a2)
          )
    case GExp.Gt(a1, a2) => Expression.newInfixFrom(
            Token.GT,
            aexpToSALTranslator(a1),
            aexpToSALTranslator(a2)
          )
    case GExp.Nor(g1, g2) => Expression.newInfixFrom(
              Token.OR,
              gexpToSALTranslator(g1),
              gexpToSALTranslator(g2)
   ).negated(),
  }

  def natToInt(n: Nat.nat): Int = n match {
    case Nat.Nata(b) => b.toInt
  }

  def foldGuard(gt: Seq[Expression]): Expression = {
    if (gt.toList.length == 0) {
      null
    }
    else if (gt.toList.length == 1) {
      gt.toList(0)
    }
    else {
      Expression.newPredicateFrom(gt:_*)
    }
  }

  def updateToExp(u: (VName.vname, AExp.aexp)): Expression = u match {
    case (r, a) => Expression.newInfixFrom(
            Token.EQUALS,
            Expression.newOneFrom(vnameToSALTranslator(r)),
            aexpToSALTranslator(a)
    )
  }

  def transitionToSALTranslator(id: String, t: Transition.transition_ext[Unit]):isabellesal.Transition = {
    isabellesal.Transition.newOneFrom(
      id,
      Transition.Label(t),
      natToInt(Transition.Arity(t)),
      // We want to just do it with one guard
      foldGuard(Transition.Guard(t).map(g => gexpToSALTranslator(g))),
      Expression.newOutputs(Transition.Outputs(t).map(a => aexpToSALTranslator(a)):_*),
      Transition.Updates(t).map(updateToExp):_*
    )
  }

  def toMichaelsMove(move: ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])): MichaelsMove = {
    new MichaelsMove(
      natToInt(move._1._1),
      natToInt(move._1._2),
      transitionToSALTranslator(Transition.Label(move._2) +
        "_" + System.currentTimeMillis, move._2)
      )
  }

  def fset_to_list[A](f: FSet.fset[A]): List[A] = FSet.fset(f) match {
    case Set.seta(s) => s
  }

  def efsmToSALTranslator(e: TransitionMatrix, f: String) = {
    val pw = new PrintWriter(new File("dotfiles/" + f + ".dot" ))
    pw.write(EFSM_Dot.efsm2dot(e))
    pw.close
    println("converting "+f)
    isabellesal.EFSM.newOneFrom(fset_to_list(FSet.fimage(toMichaelsMove, e)):_*)
    new Translator().writeSALandDOT(Paths.get("salfiles"), f);
  }

}
