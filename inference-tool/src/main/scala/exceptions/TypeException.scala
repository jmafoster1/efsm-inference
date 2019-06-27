package exceptions

class TypeException(val message:String) extends Exception {
  override def toString(): String = super.toString() + ": " + message
}
