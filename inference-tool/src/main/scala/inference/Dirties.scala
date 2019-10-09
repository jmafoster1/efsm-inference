import com.microsoft.z3
import exceptions._
import java.io._
import scala.io.Source
import scala.util.Random
import sys.process._
import Types._
import org.apache.commons.io.FileUtils
import java.util.UUID.randomUUID

object Dirties {

  def foldl[A, B](f: A => B => A, b: A, l: List[B]): A =
    // l.par.foldLeft(b)(((x, y) => (f(x))(y)))
    l.foldLeft(b)(((x, y) => (f(x))(y)))

  def toZ3(a: VName.vname): String = a match {
    case VName.I(n) => s"i${Code_Numeral.integer_of_nat(n)}"
    case VName.R(n) => s"r${Code_Numeral.integer_of_nat(n)}"
  }

  def toZ3(a: AExp.aexp): String = a match {
    case AExp.L(Value.Numa(n)) => s"(Some (Num ${Code_Numeral.integer_of_int(n).toString}))"
    case AExp.L(Value.Str(s)) => s"""(Some (Str "${s}"))"""
    case AExp.V(v) => s"${toZ3(v)}"
    case AExp.Plus(a1, a2) => s"(+ ${toZ3(a1)} ${toZ3(a2)})"
    case AExp.Minus(a1, a2) => s"(- ${toZ3(a1)} ${toZ3(a2)})"
  }

  def toZ3(g: GExp.gexp): String = g match {
    case GExp.Bc(a) => a.toString()
    case GExp.Eq(a1, a2) => s"(eq ${toZ3(a1)} ${toZ3(a2)})"
    case GExp.Gt(a1, a2) => s"(gt ${toZ3(a1)} ${toZ3(a2)})"
    case GExp.In(v, l) => toZ3(GExp.fold_In(v, l))
    case GExp.Nor(g1, g2) => s"(nor ${toZ3(g1)} ${toZ3(g2)})"
    case GExp.Null(AExp.V(v)) => s"(eq ${toZ3(v)} None)"
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

(define-fun nor ((x Trilean) (y Trilean)) Trilean
  (ite (and (= x true) (= y true)) false
  (ite (and (= x true) (= y false)) false
  (ite (and (= x false) (= y true)) false
  (ite (and (= x false) (= y false)) true
  invalid))))
)

(define-fun gt ((x (Option Value)) (y (Option Value))) Trilean
  (ite (exists ((x1 Int)) (exists ((y1 Int)) (and (= x (Some (Num x1))) (and (= y (Some (Num y1))) (> x1 y1))))) true
  (ite (exists ((x1 Int)) (exists ((y1 Int)) (and (= x (Some (Num x1))) (and (= y (Some (Num y1))) (not (> x1 y1)))))) false
  invalid))
)

(define-fun eq ((x (Option Value)) (y (Option Value))) Trilean
  (ite (= x y) true
  false)
)
"""
          val vars = GExp.enumerate_vars(g)
          z3String += vars.map(v => s"(declare-const ${toZ3(v)} (Option Value))").foldLeft("")(((x, y) => x + y + "\n"))
          z3String += s"(assert (= true ${toZ3(g)}))"

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
  def initiallyUndefinedContextCheck(e: IEFSM, r: Nat.nat, s: Nat.nat): Boolean = {
    println("initiallyUndefinedContextCheck")
    val f = "intermediate_" + randomUUID.toString().replace("-", "_")
    TypeConversion.efsmToSALTranslator(Inference.tm(e), f)

    addLTL("salfiles/" + f + ".sal", s"  initiallyUndefined: THEOREM MichaelsEFSM |- G(cfstate = ${TypeConversion.salState(s)} => r_${Code_Numeral.integer_of_nat(r)} = value_option ! None);")

    val output = Seq("bash", "-c", s"cd salfiles; sal-smc --assertion='${f}{${Code_Numeral.integer_of_int(Inference.max_int(e))+1}}!initiallyUndefined'").!!
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
      s"checkRegValue: THEOREM composition |- G(cfstate.1 = ${TypeConversion.salState(s1)} AND cfstate.2 = ${TypeConversion.salState(s2)} => r_${Code_Numeral.integer_of_nat(r)}.2 = Some(${TypeConversion.salValue(v)}));")
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
    val subsumes = readLine("") == "y"
    subsumes
  }
}
