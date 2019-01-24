object TypeConversion {

def toValue(n:BigInt): Value.value = Value.Numa(Int.int_of_integer(n))
def toValue(s:String): Value.value = Value.Str(String.explode(s))
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

def valueToString(v:Value.value): String = {
  v match {
    case Value.Numa(n) =>
      n.toString()
    case Value.Str(s) =>
      String.implode(s)
  }
}

type Event = (List[String.char], (List[Value.value], List[Value.value]))

def toEventTuple(e: Map[String, Any]): Event = {
                           (String.explode(e("label").asInstanceOf[String]),
                            (e("inputs").asInstanceOf[List[Any]].map(x => TypeConversion.toValue(x)),
                            e("outputs").asInstanceOf[List[Any]].map(x => TypeConversion.toValue(x)))
                          )
                         }

}
