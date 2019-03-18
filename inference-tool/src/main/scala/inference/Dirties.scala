import com.microsoft.z3
import exceptions.SatisfiabilityUnknownException
// PrintWriter
import java.io._
object Dirties {

  def R(i: BigInt): VName.vname = {
    VName.R(Nat.Nata(i))
  }
  def I(i: BigInt): VName.vname = {
    VName.I(Nat.Nata(i))
  }

  def writeDot(e: FSet.fset[(
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))], f: String): Unit = {
                                   val pw = new PrintWriter(new File(f))
                                   pw.write(EFSM_Dot.efsm2dot(e))
                                   pw.close
                                 }

  def writeiDot(e: FSet.fset[(Nat.nat,
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))], f: String): Unit = {
                                   val pw = new PrintWriter(new File(f))
                                   pw.write(EFSM_Dot.iefsm2dot(e))
                                   pw.close
                                 }

  type Set[A] = scala.collection.immutable.Set[A]

  def valueOf(i: Int.int): Int =  i match {
    case Int.int_of_integer(i1) => i1.intValue()
  }

  def valueOf(i: Nat.nat): Int =  i match {
    case Nat.Nata(i1) => i1.intValue()
  }

  def toZ3(v: Value.value, ctx: z3.Context): z3.Expr = v match {
    case Value.Numa(n) => ctx.mkInt(valueOf(n))
    case Value.Str(s) => ctx.mkString(s)
  }

  def toZ3(v: VName.vname, ctx: z3.Context, datatype: z3.Sort): z3.Expr = v match {
    case VName.I(n) => ctx.mkConst("i"+valueOf(n), datatype)
    case VName.R(n) => ctx.mkConst("r"+valueOf(n), datatype)
  }

  def toZ3(a: AExp.aexp, ctx: z3.Context, types: FinFun.finfun[VName.vname, Type_Inference.typea]): z3.Expr =  a match {
    case AExp.L(v) => toZ3(v, ctx)
    case AExp.V(v) => {
      FinFun.finfun_apply(types, v) match {
        case Type_Inference.NUM()     => toZ3(v, ctx, ctx.mkIntSort())
        case Type_Inference.STRING()    => toZ3(v, ctx, ctx.mkStringSort())
        case Type_Inference.UNBOUND() => toZ3(v, ctx, ctx.mkUninterpretedSort("UNBOUND"))
        case Type_Inference.NULL() => toZ3(v, ctx, ctx.mkUninterpretedSort("NULL"))
      }
    }
    case AExp.Plus(a1, a2) => ctx.mkAdd(toZ3(a1, ctx, types).asInstanceOf[z3.ArithExpr], toZ3(a2, ctx, types).asInstanceOf[z3.ArithExpr])
    case AExp.Minus(a1, a2) => ctx.mkSub(toZ3(a1, ctx, types).asInstanceOf[z3.ArithExpr],toZ3(a2, ctx, types).asInstanceOf[z3.ArithExpr])
  }

  def toZ3(g: GExp.gexp, ctx: z3.Context, variables: FinFun.finfun[VName.vname, Type_Inference.typea]): z3.BoolExpr =  g match {
    case GExp.Bc(a) => ctx.mkBool(a)
    case GExp.Eq(a1, a2) => ctx.mkEq(toZ3(a1, ctx, variables), toZ3(a2, ctx, variables))
    case GExp.Gt(a1, a2) => ctx.mkGt(toZ3(a1, ctx, variables).asInstanceOf[z3.ArithExpr], toZ3(a2, ctx, variables).asInstanceOf[z3.ArithExpr])
    case GExp.Nor(g1, g2) => ctx.mkNot(ctx.mkOr(toZ3(g1, ctx, variables), toZ3(g2, ctx, variables)))
    case GExp.Null(v) => null
  }

  def satisfiable(g: GExp.gexp): Boolean = {
    val maybe_types = Type_Inference.infer_types(g)
    maybe_types match {
      case None => false
      case Some(types) => {
        // println(FinFun.finfun_apply(types, I(1)))
        val ctx = new z3.Context
        val solver = ctx.mkSimpleSolver()
        solver.add(toZ3(g, ctx, types))
        // print(solver)
        solver.check() match {
          case z3.Status.SATISFIABLE => true
          case z3.Status.UNSATISFIABLE => false
          case z3.Status.UNKNOWN => throw new SatisfiabilityUnknownException(g.toString())
        }
      }
    }
  }

  def lengthAndPrint(x:List[(Nat.nat, ((Nat.nat, Nat.nat), ((Transition.transition_ext[Unit], Nat.nat), (Transition.transition_ext[Unit], Nat.nat))))],
                     y:List[(Nat.nat, ((Nat.nat, Nat.nat), ((Transition.transition_ext[Unit], Nat.nat), (Transition.transition_ext[Unit], Nat.nat))))]): Boolean = {
   print("newScores: ")
   for (x1 <- x) {
     print(PrettyPrinter.pp(x1)+", ")
   }
   println()
   print("oldScores: ")
   for (y1 <- y) {
     print(PrettyPrinter.pp(y1)+", ")
   }
   println("\n")

    x.length < y.length
  }

  def compareLiteralOutputs(x: List[(AExp.aexp, AExp.aexp)]) : Boolean = x match {
    case Nil => true
    case (s :: ss) => {
      s match {
        case (AExp.L(a), AExp.L(b)) => if (a != b) false else compareLiteralOutputs(ss)
        case _ => compareLiteralOutputs(ss)
      }
    }
  }

  def scalaDirectlySubsumes(a: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])],
                            b: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])],
                            c: Nat.nat,
                            t1: Transition.transition_ext[Unit],
                            t2: Transition.transition_ext[Unit]): Boolean = {
                              if (HOL.equal(t1, t2)) {
                                true
                              }
                              else if (Transition.Outputs(t1).length != Transition.Outputs(t2).length) {
                                false
                              }
                              else if (!compareLiteralOutputs(Transition.Outputs(t1) zip Transition.Outputs(t2))) {
                                false
                              }
                              // else {
                              //   val efsm = new EFSM(a)
                              // }
                              else {
                                val subsumes = readLine(f"Does\n${PrettyPrinter.transitionToString(t1)}\ndirectly subsume\n${PrettyPrinter.transitionToString(t2)}? y/n\n") == "y"
                                subsumes
                              }
                            }
  }
