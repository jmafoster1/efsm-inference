package native
import com.microsoft.z3;
import DataType._;
import exceptions.ValueException

abstract sealed class GExp {
  def toZ3(ctx: z3.Context, variables: VariableSet, inputID: String, transitionID: String): z3.BoolExpr
  def getVariables(id: String): VariableSet
}

final case class Bc(a: Boolean) extends GExp {
  def toZ3(ctx: z3.Context, variables: VariableSet, input: String, transitionID: String): z3.BoolExpr = ctx.mkBool(a)
  def getVariables(id: String) = new VariableSet()
}
final case class Eq(a: AExp, b: AExp) extends GExp {
  def toZ3(ctx: z3.Context, variables: VariableSet, inputID: String, transitionID: String) = ctx.mkEq(a.toZ3(ctx, variables, inputID, transitionID), b.toZ3(ctx, variables, inputID, transitionID))
  def getVariables(id: String) = a.getVariables(id) ++ b.getVariables(id)
}
final case class Gt(a: AExp, b: AExp) extends GExp {
  def toZ3(ctx: z3.Context, variables: VariableSet, inputID: String, transitionID: String) = ctx.mkGt(a.toZ3(ctx, variables, inputID, transitionID).asInstanceOf[z3.ArithExpr], b.toZ3(ctx, variables, inputID, transitionID).asInstanceOf[z3.ArithExpr])
  def getVariables(id: String) = a.getVariables(id) ++ b.getVariables(id)
}
final case class Nor(a: GExp, b: GExp) extends GExp {
  def toZ3(ctx: z3.Context, variables: VariableSet, inputID: String, transitionID: String) = ctx.mkNot(ctx.mkOr(a.toZ3(ctx, variables, inputID, transitionID), b.toZ3(ctx, variables, inputID, transitionID)))
  def getVariables(id: String) = a.getVariables(id) ++ b.getVariables(id)
}
final case class Null(a: VName) extends GExp {
  def toZ3(ctx: z3.Context, variables: VariableSet, input: String, transitionID: String) = {
    null
  }
  def getVariables(id: String) = new VariableSet(new Variable(a, id))
}

object GExp {
  def Not(a: GExp): GExp = a match {
    case Bc(true)  => Bc(false)
    case Bc(false) => Bc(true)
    case _         => Nor(a, a)
  }
  def And(a: GExp, b: GExp): GExp = (a, b) match {
    case (Bc(false), _) => Bc(false)
    case (_, Bc(false)) => Bc(false)
    case (Bc(true), b)  => b
    case (a, Bc(true))  => a
    case _              => Nor(Nor(a, a), Nor(b, b))
  }
  def Or(a: GExp, b: GExp): GExp = Not(Nor(a, b))

  def Lt(a: AExp, b: AExp): GExp = Gt(b, a)
  def Le(a: AExp, b: AExp): GExp = Not(Gt(a, b))
  def Ge(a: AExp, b: AExp): GExp = Not(Lt(a, b))
  def Ne(a: AExp, b: AExp): GExp = Not(Eq(a, b))
}
