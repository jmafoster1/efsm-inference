package exceptions

class SatisfiabilityUnknownException(val message: String) extends Exception {
  override def toString(): String = super.toString() + ": " + message
}
