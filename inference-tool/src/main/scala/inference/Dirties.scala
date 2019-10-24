import com.microsoft.z3
import exceptions._
import java.io._
import scala.io.Source
import scala.util.Random
import sys.process._
import Types._
import org.apache.commons.io.FileUtils
import java.util.UUID.randomUUID

import com.lagodiuk.gp.symbolic.{SymbolicRegressionEngine, Target, TabulatedFunctionFitness, SymbolicRegressionIterationListener}

import com.lagodiuk.gp.symbolic.interpreter.Functions
import com.lagodiuk.gp.symbolic.interpreter.Expression;

import scala.collection.JavaConverters._

object Dirties {
  def foldl[A, B](f: A => B => A, b: A, l: List[B]): A =
    // l.par.foldLeft(b)(((x, y) => (f(x))(y)))
    l.foldLeft(b)(((x, y) => (f(x))(y)))

    def toZ3(v: Value.value): String = v match {
      case Value.Numa(n) => s"(Num ${Code_Numeral.integer_of_int(n).toString})"
      case Value.Str(s) => s"""(Str "${s}")"""
    }

    def toZ3(a: VName.vname): String = a match {
      case VName.I(n) => s"i${Code_Numeral.integer_of_nat(n) + 1}"
      case VName.R(n) => s"r${Code_Numeral.integer_of_nat(n)}"
    }

    def toZ3(a: AExp.aexp): String = a match {
      case AExp.L(v) => s"(Some ${toZ3(v)})"
      case AExp.V(v) => s"${toZ3(v)}"
      case AExp.Plus(a1, a2) => s"(Plus ${toZ3(a1)} ${toZ3(a2)})"
      case AExp.Minus(a1, a2) => s"(Minus ${toZ3(a1)} ${toZ3(a2)})"
    }

    def toZ3Native(v: Value.value): String = v match {
      case Value.Numa(n) => s"${Code_Numeral.integer_of_int(n).toString}"
      case Value.Str(s) => s""""${s}""""
    }

    def toZ3Native(a: AExp.aexp): String = a match {
      case AExp.L(v) => s"${toZ3Native(v)}"
      case AExp.V(v) => s"${toZ3(v)}"
      case AExp.Plus(a1, a2) => s"(+ ${toZ3Native(a1)} ${toZ3Native(a2)})"
      case AExp.Minus(a1, a2) => s"(- ${toZ3Native(a1)} ${toZ3Native(a2)})"
    }

    def toZ3(g: GExp.gexp): String = g match {
      case GExp.Bc(a) => a.toString()
      case GExp.Eq(a1, a2) => s"(Eq ${toZ3(a1)} ${toZ3(a2)})"
      case GExp.Gt(a1, a2) => s"(Gt ${toZ3(a1)} ${toZ3(a2)})"
      case GExp.In(v, l) => l.slice(0, 2).map(x => s"(Eq ${toZ3(v)} (Some ${toZ3(x)}))").fold("false")((x, y) => s"(Or ${x} ${y})")
      case GExp.Nor(g1, g2) => s"(Nor ${toZ3(g1)} ${toZ3(g2)})"
      case GExp.Null(AExp.V(v)) => s"(Eq ${toZ3(v)} None)"
      case GExp.Null(v) => throw new java.lang.IllegalArgumentException("Z3 does not handle null of more complex arithmetic expressions")
    }

    var sat_memo = scala.collection.immutable.Map[GExp.gexp, Boolean](GExp.Bc(true) -> true, GExp.Bc(false) -> false)

    def satisfiable(g: GExp.gexp): Boolean = {
      if (sat_memo isDefinedAt g) {
        return sat_memo(g)
      } else {
            var z3String = """
    (declare-datatype Option (par (X) ((None) (Some (val X)))))
    (declare-datatype Value ((Num (num Int)) (Str (str String))))
    (declare-datatype Trilean ((true) (false) (invalid)))

    (define-fun Plus ((x (Option Value)) (y (Option Value))) (Option Value)
    (match x (
      ((Some v1)
        (match y (
          ((Some v2)
            (match v1 (
              ((Num n1)
                (match v2 (
                  ((Num n2) (Some (Num (+ n1 n2))))
                  (_ None))
                ))
              (_ None))
            ))
          (_ None))
        ))
      (_ None))
    )
    )

    (define-fun Minus ((x (Option Value)) (y (Option Value))) (Option Value)
    (match x (
      ((Some v1)
        (match y (
          ((Some v2)
            (match v1 (
              ((Num n1)
                (match v2 (
                  ((Num n2) (Some (Num (- n1 n2))))
                  (_ None))
                ))
              (_ None))
            ))
          (_ None))
        ))
      (_ None))
    )
    )

    (define-fun Nor ((x Trilean) (y Trilean)) Trilean
    (ite (and (= x true) (= y true)) false
    (ite (and (= x true) (= y false)) false
    (ite (and (= x false) (= y true)) false
    (ite (and (= x false) (= y false)) true
    invalid))))
    )

    (define-fun Or ((x Trilean) (y Trilean)) Trilean
    (ite (and (= x true) (= y true)) true
    (ite (and (= x true) (= y false)) true
    (ite (and (= x false) (= y true)) true
    (ite (and (= x false) (= y false)) false
    invalid))))
    )

    (define-fun Gt ((x (Option Value)) (y (Option Value))) Trilean
    (ite (exists ((x1 Int)) (exists ((y1 Int)) (and (= x (Some (Num x1))) (and (= y (Some (Num y1))) (> x1 y1))))) true
    (ite (exists ((x1 Int)) (exists ((y1 Int)) (and (= x (Some (Num x1))) (and (= y (Some (Num y1))) (not (> x1 y1)))))) false
    invalid))
    )

    (define-fun Eq ((x (Option Value)) (y (Option Value))) Trilean
    (ite (= x y) true
    false)
    )

    """
            val vars = GExp.enumerate_vars(g)
            z3String += vars.map(v => s"(declare-const ${toZ3(v)} (Option Value))").foldLeft("")(((x, y) => x + y + "\n"))
            z3String += s"\n(assert (= true ${toZ3(g)}))"

            val ctx = new z3.Context()
            val solver = ctx.mkSimpleSolver()
            solver.fromString(z3String)
            val sat = solver.check()
            ctx.close()

            sat_memo = sat_memo + (g -> (sat == z3.Status.SATISFIABLE))
            return sat == z3.Status.SATISFIABLE
      }
    }

  def randomMember[A](f: FSet.fset[A]): Option[A] = f match {
    case FSet.fset_of_list(l) =>
      if (l == List()) {
        None
      } else {
        Some(Random.shuffle(l).head)
      }
  }

  def addLTL(f: String, e: String) = {
    val lines = Source.fromFile(f).getLines().toList.dropRight(1)

    val pw = new PrintWriter(new File(f))

    (lines :+ (e + "\nEND")).foreach(pw.println)

    pw.close()
  }

  // We're checking for the existence of a trace that gets us to the right
  // states in the respective machines such that we can take t2 so we check
  // the global negation of this to see if there's a counterexample
  def alwaysDifferentOutputsDirectSubsumption[A](
    e1: IEFSM,
    e2: IEFSM,
    s1: Nat.nat,
    s2: Nat.nat,
    t2: Transition.transition_ext[A]): Boolean = {
    if (Config.config.skip) {
      return true
    }
    val f = "intermediate_" + randomUUID.toString().replace("-", "_")
    TypeConversion.doubleEFSMToSALTranslator(Inference.tm(e1), "e1", Inference.tm(e2), "e2", f)
    addLTL(s"salfiles/${f}.sal", s"composition: MODULE = (RENAME o to o_e1 IN e1) || (RENAME o to o_e2 IN e2);\n" +
      s"canTake: THEOREM composition |- G(cfstate.1 = ${TypeConversion.salState(s1)} AND cfstate.2 = ${TypeConversion.salState(s2)} => NOT(input_sequence ! size?(i) = ${Code_Numeral.integer_of_nat(Transition.Arity(t2))} AND ${efsm2sal.guards2sal(Transition.Guard(t2))}));")
    val output = Seq("bash", "-c", s"cd salfiles; sal-smc --assertion='${f}{${Code_Numeral.integer_of_int(Inference.max_int(FSet.sup_fset(e1, e2)))+1}}!canTake'").!!
    if (!output.toString.startsWith("Counterexample")) {
      Log.root.warn(s"""Path failure:\n
        G(cfstate.1 = ${TypeConversion.salState(s1)} AND cfstate.2 = ${TypeConversion.salState(s2)} => NOT(input_sequence ! size?(I) = ${Code_Numeral.integer_of_nat(Transition.Arity(t2))} AND ${efsm2sal.guards2sal(Transition.Guard(t2))}));\n
        sal-smc --assertion='${f}{${Code_Numeral.integer_of_int(Inference.max_int(FSet.sup_fset(e1, e2)))+1}}!canTake'""")
    }
     FileUtils.deleteQuietly(new File(s"salfiles/${f}.sal"))
    return (output.toString.startsWith("Counterexample"))
  }

  // Check that whenever we're in state s, register r is always undefined
  def initiallyUndefinedContextCheck(e: TransitionMatrix, r: Nat.nat, s: Nat.nat): Boolean = {
    println("initiallyUndefinedContextCheck")
    val f = "intermediate_" + randomUUID.toString().replace("-", "_")
    TypeConversion.efsmToSALTranslator(e, f)

    addLTL("salfiles/" + f + ".sal", s"  initiallyUndefined: THEOREM MichaelsEFSM |- G(cfstate = ${TypeConversion.salState(s)} => r__${Code_Numeral.integer_of_nat(r)} = None);")

    val output = Seq("bash", "-c", s"cd salfiles; sal-smc --assertion='${f}{${Code_Numeral.integer_of_int(EFSM.max_int(e))+1}}!initiallyUndefined'").!!
    if (output.toString != "proved.\n") {
      print(output)
    }
    FileUtils.deleteQuietly(new File(s"salfiles/${f}.sal"))
    return (output.toString == "proved.\n")
  }

  // We're looking to confirm that traces which get us to s1 in e1 and s2 in e2
  // always leave register r (in e2) holding value v
  def generaliseOutputContextCheck(v: Value.value, r: Nat.nat, s1: Nat.nat, s2: Nat.nat, e1: IEFSM, e2: IEFSM): Boolean = {
    val f = "intermediate_" + randomUUID.toString().replace("-", "_")
    TypeConversion.doubleEFSMToSALTranslator(Inference.tm(e1), "e1", Inference.tm(e2), "e2", f)
    addLTL(s"salfiles/${f}.sal", s"composition: MODULE = (RENAME o to o_e1 IN e1) || (RENAME o to o_e2 IN e2);\n" +
      s"checkRegValue: THEOREM composition |- G(cfstate.1 = ${TypeConversion.salState(s1)} AND cfstate.2 = ${TypeConversion.salState(s2)} => r__${Code_Numeral.integer_of_nat(r)}.2 = Some(${TypeConversion.salValue(v)}));")
    val output = Seq("bash", "-c", s"cd salfiles; sal-smc --assertion='${f}{${Code_Numeral.integer_of_int(Inference.max_int(FSet.sup_fset(e1, e2)))+1}}!checkRegValue'").!!
    if (output.toString != "proved.\n") {
      print(output)
    }
    FileUtils.deleteQuietly(new File(s"salfiles/${f}.sal"))
    return (output.toString == "proved.\n")
  }

  // Here we check to see if globally we can never be in both states
  // If there's a counterexample then there exists a trace which gets us to
  // both states
  def acceptsAndGetsUsToBoth(
    a: IEFSM,
    b: IEFSM,
    s1: Nat.nat,
    s2: Nat.nat,
    ): Boolean = {
      if (Config.config.skip) {
        return true
      }
    val f = "intermediate_" + randomUUID.toString().replace("-", "_")
    TypeConversion.doubleEFSMToSALTranslator(Inference.tm(a), "e1", Inference.tm(b), "e2", f)
    addLTL(s"salfiles/${f}.sal", s"composition: MODULE = (RENAME o to o_e1 IN e1) || (RENAME o to o_e2 IN e2);\n" +
      s"getsUsToBoth: THEOREM composition |- G(NOT(cfstate.1 = ${TypeConversion.salState(s1)} AND cfstate.2 = ${TypeConversion.salState(s2)}));")
    val output = Seq("bash", "-c", s"cd salfiles; sal-smc --assertion='${f}{${Code_Numeral.integer_of_int(Inference.max_int(FSet.sup_fset(a, b)))+1}}!getsUsToBoth'").!!
    FileUtils.deleteQuietly(new File(s"salfiles/${f}.sal"))
    if (!output.toString.startsWith("Counterexample")) {
      Log.root.warn(s"""Path failure:\n
        getsUsToBoth: THEOREM composition |- G(NOT(cfstate.1 = ${TypeConversion.salState(s1)} AND cfstate.2 = ${TypeConversion.salState(s2)}));\n
        sal-smc --assertion='${f}{${Code_Numeral.integer_of_int(Inference.max_int(FSet.sup_fset(a, b)))+1}}!getsUsToBoth'""")
    }
    return (output.toString.startsWith("Counterexample"))
  }

  // Confirm the existance of a trace which gets us to the correct respective
  // states but produces a context in which register r holds the wrong value
  def possiblyNotValueCtx[A](
    v: Value.value,
    r: Nat.nat,
    t1: Transition,
    s2: Nat.nat,
    e2: IEFSM,
    s1: Nat.nat,
    e1: IEFSM): Boolean = {
      val f = "intermediate_" + randomUUID.toString().replace("-", "_")
      TypeConversion.doubleEFSMToSALTranslator(Inference.tm(e1), "e1", Inference.tm(e2), "e2", f)
      addLTL(s"salfiles/${f}.sal", s"composition: MODULE = (RENAME o to o_e1 IN e1) || (RENAME o to o_e2 IN e2);\n" +
        s"possiblyNotValue: THEOREM composition |- G(NOT(cfstate.1 = ${TypeConversion.salState(s1)} AND cfstate.2 = ${TypeConversion.salState(s2)} AND r_${Code_Numeral.integer_of_nat(r)} = Some(${TypeConversion.salValue(v)}) AND input_sequence ! size?(I) = ${Code_Numeral.integer_of_nat(Transition.Arity(t1))} AND ${efsm2sal.guards2sal(Transition.Guard(t1))}));")
      val output = Seq("bash", "-c", s"cd salfiles; sal-smc --assertion='${f}{${Code_Numeral.integer_of_int(Inference.max_int(FSet.sup_fset(e1, e2)))+1}}!possiblyNotValue'").!!
      FileUtils.deleteQuietly(new File(s"salfiles/${f}.sal"))
      return (output.toString.startsWith("Counterexample"))
    }

  def scalaDirectlySubsumes(a: IEFSM,
    b: IEFSM,
    s: Nat.nat,
    s_prime: Nat.nat,
    t1: Transition.transition_ext[Unit],
    t2: Transition.transition_ext[Unit]): Boolean = {
    println(s"Does ${PrettyPrinter.transitionToString(t1)} directly subsume ${PrettyPrinter.transitionToString(t2)}? (y/N)")
    val subsumes = scala.io.StdIn.readLine() == "y"
    subsumes
  }

  def getUpdate(
    r: Nat.nat,
    values: List[Int.int],
    train: List[(List[Value.value], (Map[Nat.nat,Option[Value.value]], Map[Nat.nat,Option[Value.value]]))]
  ): Option[AExp.aexp] = {
    var vars:List[String] = List()
    var targets: List[Target] = List()
    for (t <- train) t match {
      case (inputs, (anteriorRegs, posteriorRegs)) => posteriorRegs(r) match {
        case None => ()
        case Some(Value.Str(_)) => ()
        case Some(Value.Numa(Int.int_of_integer(n))) => {

          return Some(AExp.Plus(AExp.V(VName.R(Nat.Nata(2))), AExp.V(VName.I(Nat.Nata(0)))))




          println("  Inputs: "+inputs)
          println("  AnteriorRegs: "+anteriorRegs)
          println("  posteriorRegs: "+posteriorRegs)
          val target = new Target()
          target.targetIs(TypeConversion.toInt(n))
          for ((ip:Value.value, ix:Int) <- inputs.zipWithIndex) ip match {
            case Value.Str(_) => ()
            case Value.Numa(Int.int_of_integer(n)) => {
              val vname = f"i${ix+1}"
              vars = vname::vars
              target.when(vname, TypeConversion.toInt(n))
            }
          }
          for ((k:Nat.nat, v:Option[Value.value]) <- anteriorRegs) v match {
            case None => ()
            case Some(Value.Str(_)) => ()
            case Some(Value.Numa(Int.int_of_integer(n))) => {
              val vname = f"r${TypeConversion.natToInt(k)}"
              vars = vname::vars
              target.when(vname, TypeConversion.toInt(n))
            }
          }
          targets = target::targets
          println(target)
        }
      }
    }
    val fitness = new TabulatedFunctionFitness(targets: _*)
    val engine = new SymbolicRegressionEngine(
      values.map(n => TypeConversion.toInteger(Code_Numeral.integer_of_int(n))).asJava,
      fitness,
      (vars.toList).asJava,
      List(
              Functions.ADD,
              Functions.SUB,
              Functions.VARIABLE,
              Functions.CONSTANT
          ).asJava
      )
      engine.addIterationListener(new SymbolicRegressionIterationListener() {
        override def update(engine: SymbolicRegressionEngine): Unit = {
          val bestSyntaxTree: Expression = engine.getBestSyntaxTree
          val currFitValue: Double = engine.fitness(bestSyntaxTree)
          // halt condition
          if (currFitValue == 0) {
            engine.terminate()
          }
        }
      })
      engine.evolve(Config.config.gpIterations)
      val best = engine.getBestSyntaxTree().simplify()
      println("Best update function is: "+best)
      if (engine.isCorrect(best)) {
        println(best.simplify() + " is correct")
        return Some(TypeConversion.toAExp(best))
      }
      else {
        return None
      }
    }

  def getFunction(
    r: Nat.nat,
    values: List[Int.int],
    i: List[List[Value.value]],
    o: List[Value.value]
  ): Option[AExp.aexp] = {
    var vars:List[String] = List()
    var targets: List[Target] = List()
    for ((inputs, output) <- i zip o) output match {
      case Value.Str(_) => return None
      case Value.Numa(Int.int_of_integer(n)) => {


        return Some(AExp.Plus(AExp.V(VName.R(Nat.Nata(2))), AExp.V(VName.I(Nat.Nata(0)))))


        val target = new Target()
        target.targetIs(TypeConversion.toInt(n))
        for ((ip, ix) <- inputs.zipWithIndex) ip match {
          case Value.Str(_) => ()
          case Value.Numa(Int.int_of_integer(n)) => {
            val vname = f"i${ix+1}"
            vars = vname::vars
            target.when(vname, TypeConversion.toInt(n))
          }
        }
        targets = target::targets
      }
    }

    val fitness = new TabulatedFunctionFitness(targets: _*)
    val engine = new SymbolicRegressionEngine(
			values.map(n => TypeConversion.toInteger(Code_Numeral.integer_of_int(n))).asJava,
			fitness,
			// define variables
			("r"+(Code_Numeral.integer_of_nat(r)+1)::vars.toList).asJava,
			// define base functions
			List(
							Functions.ADD,
							Functions.SUB,
							Functions.VARIABLE,
							Functions.CONSTANT
					).asJava
			)
      engine.addIterationListener(new SymbolicRegressionIterationListener() {
        override def update(engine: SymbolicRegressionEngine): Unit = {
          val bestSyntaxTree: Expression = engine.getBestSyntaxTree
          val currFitValue: Double = engine.fitness(bestSyntaxTree)
          // halt condition
          if (currFitValue == 0) {
            engine.terminate()
          }
        }
      })
      engine.evolve(Config.config.gpIterations)
      val best = engine.getBestSyntaxTree().simplify()
      println("Best output function is: "+best)
      if (engine.isCorrect(best)) {
        println(best + " is correct")
        return Some(TypeConversion.toAExp(best))
      }
      else {
        return None
      }
  }

  def getRegs(
    i: List[Value.value],
    f: AExp.aexp,
    v: Value.value
  ): Map[Nat.nat, Option[Value.value]] = {
    val expVars = Lista.sorted_list_of_set(AExp.enumerate_vars(f)).map(v => PrettyPrinter.vnameToString(v))
    // println(Lista.sorted_list_of_set(AExp.enumerate_vars(f)))
    val definedVars = (1 to i.length).map(v => f"i${v}")
    val undefinedVars = expVars.filter(v => ! definedVars.contains(v))

    var inputs: String = ""
    for (v <- expVars) {
      inputs += f"(${v} Int)"
    }
    var z3String: String = "(define-fun f (" + inputs + ") Int \n  " + toZ3Native(f) + "\n)\n"
    for (v <- undefinedVars) {
      z3String += "(declare-const " + PrettyPrinter.vnameToString(TypeConversion.toVName(v)) + " Int)\n"
    }
    val args = expVars.zipWithIndex.map{case (v:String, k:Int) =>
      if (definedVars.contains(v)) {
        PrettyPrinter.valueToString(i(k))
      } else {
        v
      }
    }

    val assertion: String = "(assert (= " + PrettyPrinter.valueToString(v) + " (f " + args.mkString(" ") + ")))"
    z3String += assertion

    val ctx = new z3.Context()
    val solver = ctx.mkSimpleSolver()
    solver.fromString(z3String)
    solver.check()
    val model: z3.Model = solver.getModel

    var regs: Map[Nat.nat, Option[Value.value]] = Map()
    for (f <- model.getConstDecls) {
      regs = regs + (Nat.Nata(BigInt(f.getName.toString.substring(1).toInt)) -> Some(Value.Numa(Int.int_of_integer(BigInt(model.getConstInterp(f).toString.toInt)))))
    }
    ctx.close()
    regs
  }


}
