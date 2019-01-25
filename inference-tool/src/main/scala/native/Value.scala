package native
import com.microsoft.z3

abstract sealed class Value {
  def toZ3(ctx: z3.Context): z3.Expr
}
final case class Num(a: Int) extends Value {
  override def toString() = a.toString()
  def toZ3(ctx: z3.Context) = ctx.mkInt(a)
}
final case class Str(a: String) extends Value {
  override def toString() = "\'" + a + "\'"
  def toZ3(ctx: z3.Context) = ctx.mkString(a)
}
