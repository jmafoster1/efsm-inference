import isabellesal._

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
  def toSALTranslator(v: VName.vname): Variable = v match {
    case VName.I(Nat.Nata(n)) => Variable.newOneFrom('I', n.toInt)
    case VName.R(Nat.Nata(n)) => Variable.newOneFrom('R', n.toInt)
  }

  def toSALTranslator(a: AExp.aexp): Expression = a match {
    case AExp.L(Value.Numa(Int.int_of_integer(n))) => Expression.newOneFrom(Constant.newOneFrom(n.toInt))
    case AExp.L(Value.Str(s)) => Expression.newOneFrom(Constant.newOneFrom(s))
    case AExp.V(v) => Expression.newOneFrom(toSALTranslator(v))
    case AExp.Plus(a1, a2) => Expression.newInfixFrom(
            Token.PLUS,
            toSALTranslator(a1),
            toSALTranslator(a2)
    )
    case AExp.Plus(a1, a2) => Expression.newInfixFrom(
            Token.MINUS,
            toSALTranslator(a1),
            toSALTranslator(a2)
    )
  }

  def toSALTranslator(g: GExp.gexp): Expression = g match {
    case GExp.Bc(v) => throw new java.lang.IllegalArgumentException("Can't translate boolean values")
    case GExp.Null(a) => InfixExpression.isNull(toSALTranslator(a))
    case GExp.Eq(a1, a2) => Expression.newInfixFrom(
            Token.EQUALS,
            toSALTranslator(a1),
            toSALTranslator(a2)
          )
    case GExp.Gt(a1, a2) => Expression.newInfixFrom(
            Token.GT,
            toSALTranslator(a1),
            toSALTranslator(a2)
          )
    case GExp.Nor(g1, g2) => Expression.newInfixFrom(
              Token.OR,
              toSALTranslator(g1),
              toSALTranslator(g2)
   ).negated(),
  }

  def natToInt(n: Nat.nat): Int = n match {
    case Nat.Nata(b) => b.toInt
  }

  def toSALTranslator(t: Transition.transition_ext[Unit]):isabellesal.Transition = {
    isabellesal.Transition.newOneFrom(
      java.util.UUID.randomUUID().toString,
      Transition.Label(t),
      natToInt(Transition.Arity(t)),
      Expression.newPredicateFrom(Transition.Guard(t).map(g => toSALTranslator(g))),
      InfixExpression.newOutputs(Transition.Outputs(t).map(a => toSALTranslator(a))),
      Transition.Updates(t).map{case (r, a) => Expression.newInfixFrom(
              Token.EQUALS,
              Expression.newOneFrom(toSALTranslator(r)),
              toSALTranslator(a)
      )}

    )
  }

  def toMichaelsMove(move: ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])): MichaelsMove = {
    new MichaelsMove(move._1._1, move._1._2, toSALTranslator(move._2))
  }

  def fset_to_list[A](f: FSet.fset[A]): List[A] = FSet.fset(f) match {
    case Set.seta(s) => s
  }

  def toSALTranslator(e: TransitionMatrix): EFSM = {
    val ep = fset_to_list(FSet.fimage(toMichaelsMove, e))
    isabellesal.EFSM.newOneFrom(ep)
  }

}
