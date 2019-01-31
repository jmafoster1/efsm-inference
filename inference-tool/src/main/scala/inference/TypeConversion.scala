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

}
