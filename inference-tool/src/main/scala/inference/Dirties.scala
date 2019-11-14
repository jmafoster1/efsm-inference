import com.microsoft.z3
import exceptions._
import java.io._
import scala.io.Source
import scala.util.Random
import sys.process._
import Types._
import org.apache.commons.io.FileUtils
import java.util.UUID.randomUUID

import scala.collection.JavaConversions._

import mint.inference.gp.Generator;
import mint.inference.gp.tree.Node;
import mint.inference.gp.tree.NonTerminal;
import mint.inference.gp.tree.nonterminals.integers.AddIntegersOperator;
import mint.inference.gp.tree.nonterminals.integers.SubtractIntegersOperator;
import mint.inference.gp.tree.nonterminals.booleans.LTBooleanIntegersOperator;
import mint.inference.gp.tree.nonterminals.booleans.GTBooleanIntegersOperator;
import mint.inference.gp.tree.nonterminals.booleans.AndBooleanOperator;
import mint.inference.gp.tree.nonterminals.booleans.OrBooleanOperator;
import mint.inference.gp.tree.nonterminals.booleans.NotBooleanOperator;
import mint.inference.gp.tree.terminals.BooleanVariableAssignmentTerminal;
import mint.inference.gp.tree.terminals.IntegerVariableAssignmentTerminal;
import mint.inference.gp.tree.terminals.StringVariableAssignmentTerminal;
import mint.inference.gp.tree.terminals.VariableTerminal;
import mint.tracedata.types.BooleanVariableAssignment;
import mint.tracedata.types.IntegerVariableAssignment;
import mint.tracedata.types.StringVariableAssignment;
import mint.tracedata.types.VariableAssignment;
import mint.inference.gp.LatentVariableGP;
import mint.inference.gp.SingleOutputGP;
import mint.inference.evo.GPConfiguration;

import org.apache.log4j.BasicConfigurator;
import org.apache.log4j.Level;
import org.apache.log4j.Logger;

import org.apache.commons.collections4.MultiValuedMap;
import org.apache.commons.collections4.multimap.HashSetValuedHashMap;

import isabellesal._

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
    case AExp.Times(a1, a2) => s"(Times ${toZ3(a1)} ${toZ3(a2)})"
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
    case AExp.Times(a1, a2) => s"(* ${toZ3Native(a1)} ${toZ3Native(a2)})"
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

    (define-fun Times ((x (Option Value)) (y (Option Value))) (Option Value)
    (match x (
      ((Some v1)
      (match y (
        ((Some v2)
        (match v1 (
          ((Num n1)
          (match v2 (
            ((Num n2) (Some (Num (* n1 n2))))
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
  def alwaysDifferentOutputsDirectSubsumption[A](e1: IEFSM, e2: IEFSM, s1: Nat.nat, s2: Nat.nat, t2: Transition.transition_ext[A]): Boolean = {
    if (Config.config.skip) {
      return true
    }
    val f = "intermediate_" + randomUUID.toString().replace("-", "_")
    TypeConversion.doubleEFSMToSALTranslator(Inference.tm(e1), "e1", Inference.tm(e2), "e2", f)
    addLTL(s"salfiles/${f}.sal", s"composition: MODULE = (RENAME o to o_e1 IN e1) || (RENAME o to o_e2 IN e2);\n" +
      s"canTake: THEOREM composition |- G(cfstate.1 = ${TypeConversion.salState(s1)} AND cfstate.2 = ${TypeConversion.salState(s2)} => NOT(input_sequence ! size?(i) = ${Code_Numeral.integer_of_nat(Transition.Arity(t2))} AND ${efsm2sal.guards2sal(Transition.Guard(t2))}));")
    val output = Seq("bash", "-c", s"cd salfiles; sal-smc --assertion='${f}{${Code_Numeral.integer_of_int(Inference.max_int(FSet.sup_fset(e1, e2))) + 1}}!canTake'").!!
    if (!output.toString.startsWith("Counterexample")) {
      Log.root.warn(s"""Path failure:\n
      G(cfstate.1 = ${TypeConversion.salState(s1)} AND cfstate.2 = ${TypeConversion.salState(s2)} => NOT(input_sequence ! size?(I) = ${Code_Numeral.integer_of_nat(Transition.Arity(t2))} AND ${efsm2sal.guards2sal(Transition.Guard(t2))}));\n
      sal-smc --assertion='${f}{${Code_Numeral.integer_of_int(Inference.max_int(FSet.sup_fset(e1, e2))) + 1}}!canTake'""")
    }
    FileUtils.deleteQuietly(new File(s"salfiles/${f}.sal"))
    return (output.toString.startsWith("Counterexample"))
  }

  // Check that whenever we're in state s, register r is always undefined
  def initiallyUndefinedContextCheck(e: TransitionMatrix, r: Nat.nat, s: Nat.nat): Boolean = {
      val f = "intermediate_" + randomUUID.toString().replace("-", "_")
      TypeConversion.efsmToSALTranslator(e, f)

      addLTL("salfiles/" + f + ".sal", s"  initiallyUndefined: THEOREM MichaelsEFSM |- G(cfstate = ${TypeConversion.salState(s)} => r__${Code_Numeral.integer_of_nat(r)} = None);")

      val output = Seq("bash", "-c", s"cd salfiles; sal-smc --assertion='${f}{${Code_Numeral.integer_of_int(EFSM.max_int(e)) + 1}}!initiallyUndefined'").!!
      if (output.toString != "proved.\n") {
        print(output)
      }
      FileUtils.deleteQuietly(new File(s"salfiles/${f}.sal"))
      return (output.toString == "proved.\n")
  }

  // We're looking to confirm that traces which get us to s1 in e1 and s2 in e2
  // always leave register r (in e2) holding value v
  def generaliseOutputContextCheck(
    v: Value.value,
    r: Nat.nat,
    s1: Nat.nat,
    s2: Nat.nat,
    e1: IEFSM,
    e2: IEFSM): Boolean = {
    val f = "intermediate_" + randomUUID.toString().replace("-", "_")
    TypeConversion.doubleEFSMToSALTranslator(Inference.tm(e1), "e1", Inference.tm(e2), "e2", f)
    addLTL(s"salfiles/${f}.sal", s"composition: MODULE = (RENAME o to o_e1 IN e1) || (RENAME o to o_e2 IN e2);\n" +
      s"checkRegValue: THEOREM composition |- G(cfstate.1 = ${TypeConversion.salState(s1)} AND cfstate.2 = ${TypeConversion.salState(s2)} => r__${Code_Numeral.integer_of_nat(r)}.2 = Some(${TypeConversion.salValue(v)}));")
    val output = Seq("bash", "-c", s"cd salfiles; sal-smc --assertion='${f}{${Code_Numeral.integer_of_int(Inference.max_int(FSet.sup_fset(e1, e2))) + 1}}!checkRegValue'").!!
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
    s2: Nat.nat): Boolean = {
    if (Config.config.skip) {
      return true
    }
    val f = "intermediate_" + randomUUID.toString().replace("-", "_")
    TypeConversion.doubleEFSMToSALTranslator(Inference.tm(a), "e1", Inference.tm(b), "e2", f)
    addLTL(s"salfiles/${f}.sal", s"composition: MODULE = (RENAME o to o_e1 IN e1) || (RENAME o to o_e2 IN e2);\n" +
      s"getsUsToBoth: THEOREM composition |- G(NOT(cfstate.1 = ${TypeConversion.salState(s1)} AND cfstate.2 = ${TypeConversion.salState(s2)}));")
    val output = Seq("bash", "-c", s"cd salfiles; sal-smc --assertion='${f}{${Code_Numeral.integer_of_int(Inference.max_int(FSet.sup_fset(a, b))) + 1}}!getsUsToBoth'").!!
    FileUtils.deleteQuietly(new File(s"salfiles/${f}.sal"))
    if (!output.toString.startsWith("Counterexample")) {
      Log.root.warn(s"""Path failure:\n
        getsUsToBoth: THEOREM composition |- G(NOT(cfstate.1 = ${TypeConversion.salState(s1)} AND cfstate.2 = ${TypeConversion.salState(s2)}));\n
        sal-smc --assertion='${f}{${Code_Numeral.integer_of_int(Inference.max_int(FSet.sup_fset(a, b))) + 1}}!getsUsToBoth'""")
    }
    return (output.toString.startsWith("Counterexample"))
  }

  // Confirm the existance of a trace which gets us to the correct respective
  // states but produces a context in which register r holds the wrong value
  def diffOutputsCtx[A, B](
    e1: IEFSM,
    e2: IEFSM,
    s1: Nat.nat,
    s2: Nat.nat,
    t1: Transition.transition_ext[A],
    t2: Transition.transition_ext[B]): Boolean = {
    if (Transition.Outputs(t1) == Transition.Outputs(t2)) {
      return false
    }
    val f = "intermediate_" + randomUUID.toString().replace("-", "_")
    TypeConversion.doubleEFSMToSALTranslator(Inference.tm(e1), "e1", Inference.tm(e2), "e2", f)
    addLTL(s"salfiles/${f}.sal", s"composition: MODULE = (RENAME o to o_e1 IN e1) || (RENAME o to o_e2 IN e2);\n" +
      s"""diffOutputs: THEOREM composition |- G(
          NOT(
            cfstate.1 = ${TypeConversion.salState(s1)} AND
            cfstate.2 = ${TypeConversion.salState(s2)} AND
            input_sequence ! size?(i) = ${Code_Numeral.integer_of_nat(Transition.Arity(t1))} AND ${efsm2sal.guards2sal(Transition.Guard(t1))} AND
            input_sequence ! size?(i) = ${Code_Numeral.integer_of_nat(Transition.Arity(t2))} AND ${efsm2sal.guards2sal(Transition.Guard(t2))} AND
            X(o_e1 /= o_e2)
          )
        );""")
    val cmd = s"cd salfiles; sal-smc --assertion='${f}{${Code_Numeral.integer_of_int(Inference.max_int(FSet.sup_fset(e1, e2))) + 1}}!diffOutputs'"
    val output = Seq("bash", "-c", cmd).!!
    FileUtils.deleteQuietly(new File(s"salfiles/${f}.sal"))
    return (output.toString.startsWith("Counterexample"))
  }

  def canStillTake[A, B](
    e1: IEFSM,
    e2: IEFSM,
    s1: Nat.nat,
    s2: Nat.nat,
    t1: Transition.transition_ext[A],
    t2: Transition.transition_ext[B]): Boolean = {
        val f = "intermediate_" + randomUUID.toString().replace("-", "_")
        TypeConversion.doubleEFSMToSALTranslator(Inference.tm(e1), "e1", Inference.tm(e2), "e2", f)
        addLTL(s"salfiles/${f}.sal", s"composition: MODULE = (RENAME o to o_e1 IN e1) || (RENAME o to o_e2 IN e2);\n" +
          s"""canStillTake: THEOREM composition |- G(
                NOT(
                  cfstate.1 = ${TypeConversion.salState(s1)} AND
                  cfstate.2 = ${TypeConversion.salState(s2)} AND
                  ((input_sequence ! size?(i) = ${Code_Numeral.integer_of_nat(Transition.Arity(t2))} AND ${efsm2sal.guards2sal_num(Transition.Guard(t2), Nat.Nata(2))}) =>
                  (input_sequence ! size?(i) = ${Code_Numeral.integer_of_nat(Transition.Arity(t1))} AND ${efsm2sal.guards2sal_num(Transition.Guard(t1), Nat.Nata(1))}))
                )
              );""")
        val cmd = s"cd salfiles; sal-smc --assertion='${f}{${Code_Numeral.integer_of_int(Inference.max_int(FSet.sup_fset(e1, e2))) + 1}}!canStillTake'"
        val output = Seq("bash", "-c", cmd).!!
        // FileUtils.deleteQuietly(new File(s"salfiles/${f}.sal"))
        return (output.toString.startsWith("Counterexample"))
  }

  def scalaDirectlySubsumes(
    e1: IEFSM,
    e2: IEFSM,
    s1: Nat.nat,
    s2: Nat.nat,
    t1: Transition.transition_ext[Unit],
    t2: Transition.transition_ext[Unit]): Boolean = {
    println(s"Does ${PrettyPrinter.transitionToString(t1)} directly subsume ${PrettyPrinter.transitionToString(t2)}? (y/N)")
    val subsumes = scala.io.StdIn.readLine() == "y"
    subsumes
  }

  def getTypes(i: List[Value.value]): List[String] = i.map {
    case Value.Numa(_) => "Int"
    case Value.Str(_) => "Str"
  }

  def getTypes(r: Map[Nat.nat, Option[Value.value]]): List[String] = {
    val keys = r.keySet.toList.map(x => Code_Numeral.integer_of_nat(x))
    keys.sorted
    keys.map(key => r(Nat.Nata(key)) match {
      case Some(Value.Numa(_)) => "Int"
      case Some(Value.Str(_)) => "String"
      case None => throw new IllegalArgumentException("Got none from a map")
    })
  }

  def sortedValues(r: Map[Nat.nat, Option[Value.value]]): List[String] = {
    val keys = r.keySet.toList.map(x => Code_Numeral.integer_of_nat(x))
    keys.sorted
    keys.map(key => r(Nat.Nata(key)) match {
      case Some(Value.Numa(Int.int_of_integer(n))) => n.toString
      case Some(Value.Str(s)) => "\"" + s + "\""
      case None => throw new IllegalArgumentException("Got none from a map")
    })
  }

  def findDistinguishingGuard(
    g1: (List[(List[Value.value], Map[Nat.nat, Option[Value.value]])]),
    g2: (List[(List[Value.value], Map[Nat.nat, Option[Value.value]])])): Option[(GExp.gexp, GExp.gexp)] = {
    BasicConfigurator.resetConfiguration();
    BasicConfigurator.configure();
    Logger.getRootLogger().setLevel(Level.OFF);

    val gpGenerator: Generator = new Generator(new java.util.Random(0))

    val intNonTerms = List[NonTerminal[_]](
      new AddIntegersOperator(),
      new SubtractIntegersOperator())
    gpGenerator.setIntegerFunctions(intNonTerms);

    var intTerms = List[VariableTerminal[_]](new IntegerVariableAssignmentTerminal(0))

    // No supported stringNonTerms
    var stringTerms = List[VariableTerminal[_]]()

    // Boolean terminals
    val boolTerms = List[VariableTerminal[_]](
      new BooleanVariableAssignmentTerminal(new BooleanVariableAssignment("tr", true), true),
      new BooleanVariableAssignmentTerminal(new BooleanVariableAssignment("fa", false), true))
    gpGenerator.setBooleanTerminals(boolTerms)

    // Boolean nonterminals
    val boolNonTerms = List[NonTerminal[_]](
      new LTBooleanIntegersOperator(),
      new GTBooleanIntegersOperator(),
      new NotBooleanOperator(),
      new AndBooleanOperator(),
      new OrBooleanOperator())
    gpGenerator.setBooleanFunctions(boolNonTerms)

    var stringVarNames = List[String]()
    var intVarNames = List[String]()

    val trainingSet = new HashSetValuedHashMap[java.util.List[VariableAssignment[_]], VariableAssignment[_]]()

    // g1 needs to be true
    for ((inputs, registers) <- g1) {
      var scenario = List[VariableAssignment[_]]()
      for ((ip, ix) <- inputs.zipWithIndex) ip match {
        case Value.Numa(n) => {
          intVarNames = s"i${ix}" :: intVarNames
          scenario = (new IntegerVariableAssignment(s"i${ix}", TypeConversion.toInteger(n))) :: scenario
        }
        case Value.Str(s) => {
          stringVarNames = s"i${ix}" :: stringVarNames
          scenario = (new StringVariableAssignment(s"i${ix}", s)) :: scenario
        }
      }
      for ((r, v) <- registers) v match {
        case Some(Value.Numa(n)) => {
          intVarNames = s"r${PrettyPrinter.natToString(r)}" :: intVarNames
          scenario = (new IntegerVariableAssignment(s"r${PrettyPrinter.natToString(r)}", TypeConversion.toInteger(n))) :: scenario
        }
        case Some(Value.Str(s)) => {
          stringVarNames = s"r${PrettyPrinter.natToString(r)}" :: stringVarNames
          scenario = (new StringVariableAssignment(s"r${PrettyPrinter.natToString(r)}", s)) :: scenario
        }
      }
      trainingSet.put(scenario, new BooleanVariableAssignment("g1", true))
    }

    // g1 needs to be false if g2 is true
    for ((inputs, registers) <- g2) {
      var scenario = List[VariableAssignment[_]]()
      for ((ip, ix) <- inputs.zipWithIndex) ip match {
        case Value.Numa(n) => {
          intVarNames = s"i${ix}" :: intVarNames
          scenario = (new IntegerVariableAssignment(s"i${ix}", TypeConversion.toInteger(n))) :: scenario
        }
        case Value.Str(s) => {
          stringVarNames = s"i${ix}" :: stringVarNames
          scenario = (new StringVariableAssignment(s"i${ix}", s)) :: scenario
        }
      }
      for ((r, v) <- registers) v match {
        case Some(Value.Numa(n)) => {
          intVarNames = s"r${PrettyPrinter.natToString(r)}" :: intVarNames
          scenario = (new IntegerVariableAssignment(s"r${PrettyPrinter.natToString(r)}", TypeConversion.toInteger(n))) :: scenario
        }
        case Some(Value.Str(s)) => {
          stringVarNames = s"r${PrettyPrinter.natToString(r)}" :: stringVarNames
          scenario = (new StringVariableAssignment(s"r${PrettyPrinter.natToString(r)}", s)) :: scenario
        }
      }
      trainingSet.put(scenario, new BooleanVariableAssignment("g1", false))
    }

    for (intVarName <- intVarNames.distinct) {
      intTerms = (new IntegerVariableAssignmentTerminal(intVarName)) :: intTerms
    }

    for (stringVarName <- stringVarNames.distinct) {
      stringTerms = (new StringVariableAssignmentTerminal(new StringVariableAssignment(stringVarName), false)) :: stringTerms
    }

    gpGenerator.setIntegerTerminals(intTerms)
    gpGenerator.setStringTerminals(stringTerms)

    val gp = new SingleOutputGP(gpGenerator, trainingSet, new GPConfiguration(20, 0.9f, 0.01f, 7, 7), false)

    val best: Node[VariableAssignment[_]] = gp.evolve(10).asInstanceOf[Node[VariableAssignment[_]]]

    // println("Guard training set: " + trainingSet)
    // println("  Int terminals: " + intTerms)
    // println("  Best function is: " + best.simp())

    val ctx = new z3.Context()
    val gexp = TypeConversion.gexpFromZ3(best.toZ3(ctx))
    ctx.close
    if (gp.isCorrect(best)) {
      return Some((gexp, GExp.gNot(gexp)))
    } else {
      return None
    }
  }

  def getUpdate(
    r: Nat.nat,
    values: List[Value.value],
    train: List[(List[Value.value], (Map[Nat.nat, Option[Value.value]], Map[Nat.nat, Option[Value.value]]))]): Option[AExp.aexp] = {

    val maxReg = TypeConversion.toInt(r)

    BasicConfigurator.resetConfiguration();
    BasicConfigurator.configure();
    Logger.getRootLogger().setLevel(Level.OFF);

    val gpGenerator: Generator = new Generator(new java.util.Random(0))

    val intNonTerms = List[NonTerminal[_]](new AddIntegersOperator(), new SubtractIntegersOperator())
    gpGenerator.setIntegerFunctions(intNonTerms);

    var intTerms = List[VariableTerminal[_]](new IntegerVariableAssignmentTerminal(0))

    // No supported stringNonTerms
    var stringTerms = List[VariableTerminal[_]]()

    for (v <- values) v match {
      case Value.Numa(n) => intTerms = (new IntegerVariableAssignmentTerminal(TypeConversion.toInteger(n))) :: intTerms
      case Value.Str(s) => stringTerms = (new StringVariableAssignmentTerminal(s)) :: stringTerms
    }

    var stringVarNames = List[String]()
    var intVarNames = List[String]()

    val trainingSet = new HashSetValuedHashMap[java.util.List[VariableAssignment[_]], VariableAssignment[_]]()

    for (t <- train) t match {
      case (inputs, (anteriorRegs, posteriorRegs)) => {
        var scenario = List[VariableAssignment[_]]()
        for ((ip, ix) <- inputs.zipWithIndex) ip match {
          case Value.Numa(n) => {
            intVarNames = s"i${ix}" :: intVarNames
            scenario = (new IntegerVariableAssignment(s"i${ix}", TypeConversion.toInteger(n))) :: scenario
          }
          case Value.Str(s) => {
            stringVarNames = s"i${ix}" :: stringVarNames
            scenario = (new StringVariableAssignment(s"i${ix}", s)) :: scenario
          }
        }
        posteriorRegs(r) match {
          case None => ()
          case Some(Value.Numa(n)) => trainingSet.put(scenario, new IntegerVariableAssignment("o1", TypeConversion.toInteger(n)))
          case Some(Value.Str(s)) => trainingSet.put(scenario, new StringVariableAssignment("o1", s))
        }
      }
    }

    for (intVarName <- intVarNames.distinct) {
      intTerms = (new IntegerVariableAssignmentTerminal(intVarName)) :: intTerms
    }

    for (stringVarName <- stringVarNames.distinct) {
      stringTerms = (new StringVariableAssignmentTerminal(new StringVariableAssignment(stringVarName), false)) :: stringTerms
    }

    gpGenerator.setIntegerTerminals(intTerms)
    gpGenerator.setStringTerminals(stringTerms)

    val gp = new LatentVariableGP(gpGenerator, trainingSet, new GPConfiguration(20, 0.9f, 0.01f, 7, 7))

    val best: Node[VariableAssignment[_]] = gp.evolve(10).asInstanceOf[Node[VariableAssignment[_]]]

    // println("Update training set: " + trainingSet)
    // println("  Int terminals: " + intTerms)
    // println("  Best function is: " + best.simp())

    val ctx = new z3.Context()
    val aexp = TypeConversion.aexpFromZ3(best.toZ3(ctx))
    ctx.close
    if (gp.isCorrect(best)) {
      return Some(aexp)
    } else {
      return None
    }
  }

  def getTypes(best: Node[VariableAssignment[_]]): Map[VName.vname, String] = {
    var types = Map[VName.vname, String]()

    for (v <- asScalaSet(best.varsInTree)) {
      types = types + (TypeConversion.vnameFromString(v.getName) -> v.typeString)
    }
    return types
  }

  def getFunction(
    r: Nat.nat,
    values: List[Value.value],
    i: List[List[Value.value]],
    o: List[Value.value]): Option[(AExp.aexp, Map[VName.vname, String])] = {

    val ioPairs = (i zip o).distinct
    val maxReg = TypeConversion.toInt(r)

    BasicConfigurator.resetConfiguration();
    BasicConfigurator.configure();
    Logger.getRootLogger().setLevel(Level.OFF);

    val gpGenerator: Generator = new Generator(new java.util.Random(0))

    val intNonTerms = List[NonTerminal[_]](new AddIntegersOperator(), new SubtractIntegersOperator())
    gpGenerator.setIntegerFunctions(intNonTerms);

    var intTerms = List[VariableTerminal[_]](new IntegerVariableAssignmentTerminal(0))

    // No supported stringNonTerms
    var stringTerms = List[VariableTerminal[_]]()

    for (v <- values) v match {
      case Value.Numa(n) => intTerms = (new IntegerVariableAssignmentTerminal(TypeConversion.toInteger(n))) :: intTerms
      case Value.Str(s) => stringTerms = (new StringVariableAssignmentTerminal(s)) :: stringTerms
    }

    var stringVarNames = List[String](s"r${maxReg + 1}")
    var intVarNames = List[String](s"r${maxReg + 2}")

    val trainingSet = new HashSetValuedHashMap[java.util.List[VariableAssignment[_]], VariableAssignment[_]]()
    for ((inputs, output) <- ioPairs) {
      var scenario = List[VariableAssignment[_]]()
      for ((ip, ix) <- inputs.zipWithIndex) ip match {
        case Value.Numa(n) => {
          intVarNames = s"i${ix}" :: intVarNames
          scenario = (new IntegerVariableAssignment(s"i${ix}", TypeConversion.toInteger(n))) :: scenario
        }
        case Value.Str(s) => {
          stringVarNames = s"i${ix}" :: stringVarNames
          scenario = (new StringVariableAssignment(s"i${ix}", s)) :: scenario
        }
      }
      output match {
        case Value.Numa(n) => trainingSet.put(scenario, new IntegerVariableAssignment("o1", TypeConversion.toInteger(n)))
        case Value.Str(s) => trainingSet.put(scenario, new StringVariableAssignment("o1", s))
      }
    }

    for (intVarName <- intVarNames.distinct) {
      intTerms = (new IntegerVariableAssignmentTerminal(intVarName)) :: intTerms
    }

    for (stringVarName <- stringVarNames.distinct) {
      stringTerms = (new StringVariableAssignmentTerminal(new StringVariableAssignment(stringVarName), false)) :: stringTerms
    }

    gpGenerator.setIntegerTerminals(intTerms)
    gpGenerator.setStringTerminals(stringTerms)

    val gp = new LatentVariableGP(gpGenerator, trainingSet, new GPConfiguration(20, 0.9f, 0.01f, 7, 7))

    val best: Node[VariableAssignment[_]] = gp.evolve(10).asInstanceOf[Node[VariableAssignment[_]]]

    // println("Output training set: " + trainingSet)
    // println("  Int terminals: " + intTerms)
    // println("  Best function is: " + best)

    if (gp.isCorrect(best)) {
      return Some((TypeConversion.toAExp(best), getTypes(best)))
    } else {
      return None
    }
  }

  def getRegs(
    types: Map[VName.vname, String],
    i: List[Value.value],
    f: AExp.aexp,
    v: Value.value): Map[Nat.nat, Option[Value.value]] = {
    val expVars: List[VName.vname] = Lista.sorted_list_of_set(AExp.enumerate_vars(f))
    val definedVars = (0 to i.length).map(i => VName.I(Nat.Nata(i)))
    val undefinedVars = expVars.filter(v => !definedVars.contains(v))

    // println("\noutputFun: " + PrettyPrinter.aexpToString(f, true) + " = " + PrettyPrinter.valueToString(v))
    // println("  expVars: " + expVars)
    // println("  undefinedVars: " + undefinedVars)

    var inputs: String = ""
    for (v <- expVars) {
      inputs += f"(${PrettyPrinter.vnameToString(v)} ${TypeConversion.expandTypeString(types(v))})"
    }
    var z3String: String = f"(define-fun f (${inputs}) ${TypeConversion.typeString(v)} \n  ${toZ3Native(f)}\n)\n"
    for (v <- undefinedVars) {
      z3String += f"(declare-const ${PrettyPrinter.vnameToString(v)} ${TypeConversion.expandTypeString(types(v))})\n"
    }
    val args = expVars.zipWithIndex.map {
      case (v: VName.vname, k: Int) =>
        if (definedVars.contains(v)) {
          PrettyPrinter.valueToString(i(k))
        } else {
          PrettyPrinter.vnameToString(v)
        }
    }

    if (args.length == 0) {
      val assertion: String = "(assert (= " + PrettyPrinter.valueToString(v) + " f))"
      z3String += assertion
    } else {
      val assertion: String = "(assert (= " + PrettyPrinter.valueToString(v) + " (f " + args.mkString(" ") + ")))"
      z3String += assertion
    }

    val ctx = new z3.Context()
    val solver = ctx.mkSimpleSolver()

    solver.fromString(z3String)
    solver.check()
    val model: z3.Model = solver.getModel

    var regs: Map[Nat.nat, Option[Value.value]] = Map()
    for (f <- model.getConstDecls) {
      val constInterp = model.getConstInterp(f)
      regs = regs + (Nat.Nata(BigInt(f.getName.toString.substring(1).toInt)) -> Some(TypeConversion.toValue(model.getConstInterp(f))))
    }
    ctx.close()
    regs
  }
}
