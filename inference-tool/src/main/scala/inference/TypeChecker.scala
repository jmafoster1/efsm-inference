class TypeChecker {
  val variables = new VariableSet()
  private val groups = scala.collection.mutable.Map[Variable, VariableSet]()

  def makeSameType(x: Variable, y: Variable) = {
    if (groups isDefinedAt x) groups(x) += y else groups(x) = new VariableSet(y)
    if (groups isDefinedAt y) groups(y) += x else groups(y) = new VariableSet(x)

    if ((variables contains x) && x.dataType != DataType.UNBOUND) groups(x).assignAll(x.dataType)
    if ((variables contains y) && y.dataType != DataType.UNBOUND) groups(y).assignAll(x.dataType)

    if (!(variables contains x)) variables += x
    if (!(variables contains y)) variables += y
  }

  def update(x: Variable, t: DataType.DataType) = {
    x.assign(t)
    if (groups isDefinedAt x) groups(x).assignAll(t)
    variables += x
  }

  def getVariables(g: AExp.aexp): VariableSet = g match {
    case AExp.L(v) => new VariableSet()
    case AExp.V(v) => new VariableSet(new Variable(v))
    case AExp.Plus(a1, a2) => getVariables(a1) ++ getVariables(a2)
    case AExp.Minus(a1, a2) => getVariables(a1) ++ getVariables(a2)
  }

  def getVariables(g: GExp.gexp): VariableSet = g match {
    case GExp.Bc(a) => new VariableSet()
    case GExp.Eq(a1, a2) => getVariables(a1) ++ getVariables(a2)
    case GExp.Gt(a1, a2) => getVariables(a1) ++ getVariables(a2)
    case GExp.Nor(g1, g2) => getVariables(g1) ++ getVariables(g2)
    case GExp.Null(v) => new VariableSet(new Variable(v))
  }

  def inferTypes(g: GExp.gexp): Unit = {
    g match {
      case GExp.Bc(v)    =>
      case GExp.Null(v)  => variables += new Variable(v)
      case GExp.Gt(a1, a2) => (getVariables(a1) ++ getVariables(a2)).foreach(f => update(f, DataType.NUM))
      case GExp.Nor(g1, g2) => {
        inferTypes(g1)
        inferTypes(g2)
      }
      case GExp.Eq(a1, a2) => (a1, a2) match {
        case (AExp.L(Value.Numa(_)), _)   => getVariables(a2).foreach(f => update(f, DataType.NUM))
        case (AExp.L(Value.Str(_)), _)   => getVariables(a2).foreach(f => update(f, DataType.STR))
        case (_, AExp.L(Value.Numa(_)))   => getVariables(a1).foreach(f => update(f, DataType.NUM))
        case (_, AExp.L(Value.Str(_)))   => getVariables(a1).foreach(f => update(f, DataType.STR))
        case (AExp.Minus(x, y), _) => (getVariables(a1) ++ getVariables(a2)).foreach(f => update(f, DataType.NUM))
        case (AExp.Plus(x, y), _)  => (getVariables(a1) ++ getVariables(a2)).foreach(f => update(f, DataType.NUM))
        case (_, AExp.Minus(x, y)) => (getVariables(a1) ++ getVariables(a2)).foreach(f => update(f, DataType.NUM))
        case (_, AExp.Plus(x, y))  => (getVariables(a1) ++ getVariables(a2)).foreach(f => update(f, DataType.NUM))
        case (AExp.V(x), AExp.V(y)) => (x, y) match {
          case (VName.R(_), VName.R(_)) => makeSameType(new Variable(x), new Variable(y))
          case (VName.R(_), _)    => makeSameType(new Variable(x), new Variable(y))
          case (_, VName.R(_))    => makeSameType(new Variable(x), new Variable(y))
          case (_, _)       => makeSameType(new Variable(x), new Variable(y))
        }
      }
    }
  }
}
