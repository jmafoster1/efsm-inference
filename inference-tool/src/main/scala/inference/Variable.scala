import DataType._;

class Variable(val name: VName.vname, var dataType: DataType = UNBOUND) extends Serializable{

  def assign(t: DataType) {
    assert(this.dataType == UNBOUND || this.dataType == t)
    this.dataType = t
  }

  def canEqual(a: Any) = a.isInstanceOf[Variable]
  override def equals(that: Any): Boolean =
    that match {
      case that: Variable => that.canEqual(this) && this.hashCode == that.hashCode
      case _              => false
    }
  override def hashCode: Int = {
    val prime = 31
    var result = 1
    result = prime * result + name.hashCode() + dataType.hashCode();
    result = prime * result + (if (name == null) 0 else name.hashCode)
    return result
  }

  override def toString(): String = this.name match {
    case VName.I(a) => "i"+Dirties.valueOf(a)+": "+this.dataType
    case VName.R(a) => "r"+Dirties.valueOf(a)+": "+this.dataType
  }
}
