import DataType._;

class VariableSet(var asSet: scala.collection.immutable.Set[Variable]) extends Set[Variable] with Serializable {

  def this(variables: Variable*) = {
    this(scala.collection.immutable.Set[Variable]())
    for (v <- variables) this += v
  }

  def contains(v: Variable): Boolean = this.asSet.contains(v)

  def get(filter: Variable => Boolean): Variable = {
    asSet.foreach(f => if (filter(f)) return f)
    return null
  }

  def +(newV: Variable): VariableSet = {
    val possibleClash = get(v => (v.name == newV.name && v.dataType != newV.dataType))
    if (possibleClash == null) return new VariableSet(asSet + newV)
    else
      (newV.dataType, possibleClash.dataType) match {
        // Replace the old variable with the new one - we can't lose any information
        case (_, UNBOUND) => return new VariableSet((asSet - possibleClash) + newV)
        // Replacing the existing variable with an unbound one loses information
        case (UNBOUND, _) => return new VariableSet(asSet)
        // Either we're trying to update an INT to an STR or vice versa
        case (_, _)       => throw new java.lang.IllegalArgumentException("Type clash " + newV.dataType + possibleClash.dataType)
      }
  }

  def +=(v: Variable): VariableSet = {
    this.asSet = (this + v).asSet
    return this
  }

  def ++(v: VariableSet): VariableSet = {
    return new VariableSet(asSet ++ v.asSet)
  }

  def -(v: Variable): VariableSet = {
    return new VariableSet(asSet - v)
  }

  def iterator: Iterator[Variable] = asSet.iterator

  def assignAll(t: DataType): VariableSet = {
    for (v <- asSet) {
      v.assign(t)
    }
    return this
  }

  override def toString() = asSet.toString()

}
