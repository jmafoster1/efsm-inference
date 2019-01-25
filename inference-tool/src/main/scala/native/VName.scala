package native
import com.microsoft.z3

abstract sealed class VName {
  def toZ3(ctx: z3.Context, s: z3.Sort, id: String): z3.Expr
}
final case class I(a: Int) extends VName {
  def toZ3(ctx: z3.Context, s: z3.Sort, id: String) = ctx.mkConst("i" + a + (if (id == "") "" else "_" + id), s)
}
final case class R(a: Int) extends VName {
  def toZ3(ctx: z3.Context, s: z3.Sort, id: String) = ctx.mkConst("r" + a + (if (id == null) "" else "_" + id), s)
}
final case class O(a: Int) extends VName {
  def toZ3(ctx: z3.Context, s: z3.Sort, id: String) = ctx.mkConst("o" + a + "_" + id, s)
}
