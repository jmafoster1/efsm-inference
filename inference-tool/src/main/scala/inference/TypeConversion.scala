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
  def toSALTranslator(v: VName.vname): Expression = match v {
    case VName.I(n) = Variable.newOneFrom("I", n)
    case VName.I(n) = Variable.newOneFrom("I", n)
  }

  def toSALTranslator(a: AExp.aexp): Expression = match a {
    case AExp.L(Num(n)) = Expression.newOneFrom(Constant.newOneFrom(n.intValue()))
    case AExp.L(Str(s)) = Expression.newOneFrom(Constant.newOneFrom(s)
    case AExp.V(v) = Expression.newOneFrom(toSALTranslator(v))
    case AExp.Plus(a1, a2) = InfixExpression.newOneFrom(
            Token.PLUS,
            toSALTranslator(a1),
            toSALTranslator(a2)
    )
    case AExp.Plus(a1, a2) = InfixExpression.newOneFrom(
            Token.MINUS,
            toSALTranslator(a1),
            toSALTranslator(a2)
    )
  }

  def toSALTranslator(g: GExp.gexp): Expression = match a {
    case GExp.Bc(v) = throw new java.lang.IllegalArgumentException("Can't translate boolean values")
    case GExp.Null(a) = InfixExpression.isNull(toSALTranslator(a))
    case GExp.Eq(a1, a2) = InfixExpression.newOneFrom(
            Token.EQUALS,
            toSALTranslator(a1),
            toSALTranslator(a2)
          )
    case GExp.Gt(a1, a2) = InfixExpression.newOneFrom(
            Token.GT,
            Expression.newOneFrom(toSALTranslator(a1)),
            Expression.newOneFrom(toSALTranslator(a2))
          )
    case GExp.Nor(g1, g2) = InfixExpression.newOneFrom(
              Token.OR,
              toSALTranslator(g1),
              toSALTranslator(g2)
   ).negated(),
  }

  def toSALTranslator(t: Transition.transition_ext[Unit]) = {
    Transition.newOneFrom(
      java.util.UUID.randomUUID().toString,
      Transition.Label(t),
      Transition.Arity(t),
      InfixExpression.newPredicateFrom(Transition.Guard(t).map(g => toSALTranslator(g))),
      InsertExpression.newOutputs(Transition.Outputs(t).map(a => toSALTranslator(Transition.Guard(a)))),
      Transition.Outputs(t).map(case (r, a) => InfixExpression.newOneFrom(
              Token.EQUALS,
              Expression.newOneFrom(toSALTranslator(r)),
              toSALTranslator(a)
      ))

    )
  }

  def toSALTranslator(e: TransitionMatrix)FSet.fset = {
    EFSM.newOneFrom(FSet.fimage((case ((from, to), tran) => new MichaelsMove(from, to, toSALTranslator(tran)), e))
  }

}
