import com.microsoft.z3
import scala.annotation.tailrec

object Dirties {

  type Set[A] = scala.collection.immutable.Set[A]

  def valueOf(i: Int.int): Int =  i match {
    case Int.int_of_integer(i1) => i1.intValue()
  }

  def valueOf(i: Nat.nat): Int =  i match {
    case Nat.Nata(i1) => i1.intValue()
  }

  def toZ3(v: Value.value, ctx: z3.Context):z3.Expr = v match {
    case Value.Numa(a) => ctx.mkInt(valueOf(a))
    case Value.Str(s) => ctx.mkString(String.implode(s))
  }

  def toZ3(v: VName.vname, ctx: z3.Context):z3.Expr = v match {
    case VName.R(a) => ctx.mkConst(s"r${valueOf(a)}", ctx.mkIntSort)
    case VName.I(a) => ctx.mkConst(s"i${valueOf(a)}", ctx.mkIntSort)
  }

  def toZ3(a: AExp.aexp, ctx: z3.Context):z3.Expr = a match {
    case AExp.L(v) => toZ3(v, ctx)
    case AExp.V(v) => toZ3(v, ctx)
    case AExp.Plus(a1, a2) => ctx.mkAdd(toZ3(a1, ctx).asInstanceOf[z3.ArithExpr], toZ3(a2, ctx).asInstanceOf[z3.ArithExpr])
    case AExp.Minus(a1, a2) => ctx.mkSub(toZ3(a1, ctx).asInstanceOf[z3.ArithExpr], toZ3(a2, ctx).asInstanceOf[z3.ArithExpr])
  }

  def toZ3(g: GExp.gexp, ctx: z3.Context):z3.BoolExpr = g match {
    case GExp.Bc(a) => ctx.mkBool(a)
    case GExp.Null(v) => null
    case GExp.Eq(a1, a2) => ctx.mkEq(toZ3(a1, ctx), toZ3(a2, ctx))
    case GExp.Gt(a1, a2) => ctx.mkGt(toZ3(a1, ctx).asInstanceOf[z3.ArithExpr], toZ3(a2, ctx).asInstanceOf[z3.ArithExpr])
    case GExp.Nor(g1, g2) => ctx.mkNot(ctx.mkOr(toZ3(g1, ctx), toZ3(g2, ctx)))
  }

  object DataType extends Enumeration {
    type DataType = Value
    val NUM, STR, UNBOUND, NULL = Value
  }

  def assign(types: Map[VName.vname, DataType.DataType], vname: VName.vname, datatype: DataType.DataType) = types getOrElse (vname, DataType.UNBOUND) match {
    case DataType.NUM => datatype match {
      case DataType.NUM => types
      case DataType.STR => throw new java.lang.IllegalArgumentException("Type clash NUM and STR")
      case DataType.NULL => throw new java.lang.IllegalArgumentException("Type clash NUM and NULL")
      case DataType.UNBOUND => types + (vname -> datatype)
    }
  }

  def getVariables(a: AExp.aexp):Set[VName.vname] = a match {
    case AExp.L(_) => scala.collection.immutable.Set()
    case AExp.V(v) => scala.collection.immutable.Set(v)
    case AExp.Plus(a1, a2) => getVariables(a1) ++ getVariables(a2)
    case AExp.Minus(a1, a2) => getVariables(a1) ++ getVariables(a2)
  }

  def getVariables(g: GExp.gexp):Set[VName.vname] = g match {
    case GExp.Bc(_) => scala.collection.immutable.Set()
    case GExp.Null(v) => scala.collection.immutable.Set(v)
    case GExp.Eq(a1, a2) => getVariables(a1) ++ getVariables(a2)
    case GExp.Gt(a1, a2) => getVariables(a1) ++ getVariables(a2)
    case GExp.Nor(g1, g2) => getVariables(g1) ++ getVariables(g2)
  }

  @tailrec
  def assignAll(vars: List[VName.vname], accum: Map[VName.vname, DataType.DataType], datatype: DataType.DataType): Map[VName.vname, DataType.DataType] = {
    vars match {
      case Nil => accum
      case x :: tail => assignAll(tail, assign(accum, x, datatype), datatype)
    }
  }

  def typeCheck(g: GExp.gexp, t: Map[VName.vname, DataType.DataType]): Map[VName.vname, DataType.DataType] = g match {
    case GExp.Bc(a) => t
    case GExp.Null(v) => assign(t, v, DataType.NULL)
    case GExp.Eq(AExp.L(Value.Numa(_)), a2) => assignAll(getVariables(a2).toList, t, DataType.NUM)
    case GExp.Eq(AExp.L(Value.Str(_)), a2) => assignAll(getVariables(a2).toList, t, DataType.STR)
    case GExp.Eq(AExp.Plus(a1a, a1b), a2) => assignAll((getVariables(a2) ++ getVariables(a1a) ++ getVariables(a1b)).toList, t, DataType.STR)
    case GExp.Eq(AExp.Minus(a1a, a1b), a2) => assignAll((getVariables(a2) ++ getVariables(a1a) ++ getVariables(a1b)).toList, t, DataType.STR)

    case GExp.Gt(a1, a2) => assignAll((getVariables(a2) ++ getVariables(a2)).toList, t, DataType.NUM)
    case GExp.Nor(g1, g2) => typeCheck(g1, t) ++ typeCheck(g2, t)
  }

  def satisfiable(g: GExp.gexp): Boolean = {
    val ctx = new z3.Context
    val solver = ctx.mkSimpleSolver()
    solver.add(toZ3(g, ctx))
    println(solver)
    return true
  }

  def scalaDirectlySubsumes(a: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])],
                            b: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])],
                            c: Nat.nat,
                            t1: Transition.transition_ext[Unit],
                            t2: Transition.transition_ext[Unit]):
  Boolean
  = HOL.equal(t1, t2)

    def scalaNondeterministicSimulates(a: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])],
                                       b: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])],
                                       c: Nat.nat => Nat.nat): Boolean
     = true
  }
