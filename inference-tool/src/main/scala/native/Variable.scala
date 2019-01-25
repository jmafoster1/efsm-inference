package native
import DataType._;
import com.microsoft.z3;

class Variable(val name: VName, val id: String, var dataType: DataType = UNBOUND) extends Serializable{
  require(name.isInstanceOf[R] || id != null, "Variable ID cannot be null")
  require(!name.isInstanceOf[R] || id == null, "Register ID must be null")

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
    result = prime * result + name.hashCode() + (if (id == null) 0 else id.hashCode) + dataType.hashCode();
    result = prime * result + (if (name == null) 0 else name.hashCode)
    return result
  }

  override def toString() = this.name + (if (id == null || id == "") "" else ("_" + id)) + ":" + this.dataType
}
