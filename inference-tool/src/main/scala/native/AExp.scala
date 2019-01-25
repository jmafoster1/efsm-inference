package native

import com.microsoft.z3;
import DataType._;
import exceptions.ValueException

abstract sealed class AExp {
  def toZ3(ctx: z3.Context, variables: VariableSet, inputID: String, transitionID: String): z3.Expr
  def getVariables(id: String): VariableSet
}
final case class L(a: Value) extends AExp {
  def toZ3(ctx: z3.Context, variables: VariableSet, inputID: String, transitionID: String): z3.Expr = a.toZ3(ctx)
  def getVariables(id: String) = new VariableSet()
}
final case class V(a: VName) extends AExp {
  def toZ3(ctx: z3.Context, variables: VariableSet, inputID: String, transitionID: String): z3.Expr = {
    var variable = variables.get(f => f.name == a && (f.id == transitionID || f.id == null))
    //      println("get(f => f.name == " + a + " && (f.id == \"" + transitionID + "\" || f.id == null)) from "+variables)
    variable.dataType match {
      case NUM     => a.toZ3(ctx, ctx.mkIntSort(), (if (variable.id == null || variable.id == "") "" else variable.id + "-") + inputID)
      case STR     => a.toZ3(ctx, ctx.mkStringSort(), (if (variable.id == null || variable.id == "") "" else variable.id + "-") + inputID)
      case UNBOUND => a.toZ3(ctx, ctx.mkStringSort(), (if (variable.id == null || variable.id == "") "" else variable.id + "-") + inputID)
    }
  }
  def getVariables(id: String) = a match {
    case R(_) => new VariableSet(new Variable(a, null))
    case _    => new VariableSet(new Variable(a, id))
  }
}
final case class Plus(a: AExp, b: AExp) extends AExp {
  def toZ3(ctx: z3.Context, variables: VariableSet, inputID: String, transitionID: String): z3.Expr = ctx.mkAdd(a.toZ3(ctx, variables, inputID, transitionID).asInstanceOf[z3.ArithExpr], b.toZ3(ctx, variables, inputID, transitionID).asInstanceOf[z3.ArithExpr])
  def getVariables(id: String) = a.getVariables(id) ++ b.getVariables(id)
}
final case class Minus(a: AExp, b: AExp) extends AExp {
  def toZ3(ctx: z3.Context, variables: VariableSet, inputID: String, transitionID: String): z3.Expr = ctx.mkSub(a.toZ3(ctx, variables, inputID, transitionID).asInstanceOf[z3.ArithExpr], b.toZ3(ctx, variables, inputID, transitionID).asInstanceOf[z3.ArithExpr])
  def getVariables(id: String) = a.getVariables(id) ++ b.getVariables(id)
}
