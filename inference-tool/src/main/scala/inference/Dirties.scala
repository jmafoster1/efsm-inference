import com.microsoft.z3
import exceptions._
import java.io._
import scala.io.Source
import scala.util.Random
import sys.process._
import Types._
import org.apache.commons.io.FileUtils

import java.util.UUID.randomUUID
import java.util.Collections
import java.util.stream.Collectors;

import scala.collection.JavaConversions._

import org.apache.log4j.BasicConfigurator;
import org.apache.log4j.Level;
import org.apache.log4j.Logger;

import org.apache.commons.collections4.MultiValuedMap;
import org.apache.commons.collections4.multimap.HashSetValuedHashMap;

import java.util.ArrayList

import hammerlab.math.tolerance._

import me.shadaj.scalapy.py
import me.shadaj.scalapy.py.SeqConverters
import py.PyQuote

// let things be "equal" that are within 1% of one another

object Dirties {
  implicit val ε: E = 1e-2
  def doubleEquals(a: Real.real, b: Real.real): Boolean =
    TypeConversion.toDouble(a) === TypeConversion.toDouble(b)

  def foldl[A, B](f: A => B => A, b: A, l: List[B]): A =
    // l.par.foldLeft(b)(((x, y) => (f(x))(y)))
    l.foldLeft(b)(((x, y) => (f(x))(y)))

  def toZ3(v: Value.value): String = v match {
    case Value.Inta(n) => s"(Int ${Code_Numeral.integer_of_int(n).toString})"
    case Value.Str(s) => s"""(Str "${s}")"""
    case Value.Reala(f) => s"""(Double ${TypeConversion.toDouble(f)})"""
  }

  def toZ3(a: VName.vname): String = a match {
    case VName.I(n) => s"i${Code_Numeral.integer_of_nat(n)}"
    case VName.R(n) => s"r${Code_Numeral.integer_of_nat(n)}"
  }

  def toZ3(a: AExp.aexp[VName.vname]): String = a match {
    case AExp.L(v) => s"(Some ${toZ3(v)})"
    case AExp.V(v) => s"${toZ3(v)}"
    case AExp.Plus(a1, a2) => s"(Plus ${toZ3(a1)} ${toZ3(a2)})"
    case AExp.Minus(a1, a2) => s"(Minus ${toZ3(a1)} ${toZ3(a2)})"
    case AExp.Times(a1, a2) => s"(Times ${toZ3(a1)} ${toZ3(a2)})"
    case AExp.Divide(a1, a2) => s"(Divide ${toZ3(a1)} ${toZ3(a2)})"
  }

  def toZ3Native(v: Value.value): String = v match {
    case Value.Inta(n) => s"${Code_Numeral.integer_of_int(n).toString}"
    case Value.Reala(r) => s"${TypeConversion.toDouble(r).toString}"
    case Value.Str(s) => s""""${s}""""
  }

  def toZ3Native(a: AExp.aexp[VName.vname]): String = a match {
    case AExp.L(v) => s"${toZ3Native(v)}"
    case AExp.V(v) => s"${toZ3(v)}"
    case AExp.Plus(a1, a2) => s"(+ ${toZ3Native(a1)} ${toZ3Native(a2)})"
    case AExp.Minus(a1, a2) => s"(- ${toZ3Native(a1)} ${toZ3Native(a2)})"
    case AExp.Times(a1, a2) => s"(* ${toZ3Native(a1)} ${toZ3Native(a2)})"
    case AExp.Divide(a1, a2) => s"(/ ${toZ3Native(a1)} ${toZ3Native(a2)})"
  }

  def toZ3(g: GExp.gexp[VName.vname]): String = g match {
    case GExp.Bc(a) => a.toString()
    case GExp.Eq(a1, a2) => s"(Eq ${toZ3(a1)} ${toZ3(a2)})"
    case GExp.Gt(a1, a2) => s"(Gt ${toZ3(a1)} ${toZ3(a2)})"
    case GExp.In(v, l) => l.slice(0, 2).map(x => s"(Eq ${toZ3(v)} (Some ${toZ3(x)}))").fold("false")((x, y) => s"(Or ${x} ${y})")
    case GExp.Nor(g1, g2) => {
      s"(Nor ${toZ3(g1)} ${toZ3(g2)})"
    }
  }

  var sat_memo = scala.collection.immutable.Map[GExp.gexp[VName.vname], Boolean](GExp.Bc(true) -> true, GExp.Bc(false) -> false)

  def check(z3String: String, expected: z3.Status = z3.Status.SATISFIABLE): Boolean = {
    val ctx = new z3.Context()
    val solver = ctx.mkSimpleSolver()
    solver.fromString(z3String)
    val sat = solver.check()
    ctx.close()

    return sat == expected
  }

  def satisfiable(g: GExp.gexp[VName.vname]): Boolean = {
    if (sat_memo isDefinedAt g)
      return sat_memo(g)
    else {
      var z3String = Config.z3Head
      z3String += GExp.enumerate_vars(g).map(v => s"(declare-const ${toZ3(v)} (Option Value))").foldLeft("")(((x, y) => x + y + "\n"))
      z3String += s"\n(assert (= true ${toZ3(g)}))"

      val sat = check(z3String)
      sat_memo = sat_memo + (g -> sat)
      return sat
    }
  }

  def randomMember[A](f: FSet.fset[A]): Option[A] = f match {
    case FSet.fset_of_list(l) =>
      if (l == List())
        return None
      if (l.length == 1)
        return Some(l.head)
      else
        Some(Random.shuffle(l).head)
  }

  def addLTL(f: String, e: String) = {
    val lines = Source.fromFile(f).getLines().toList.dropRight(1)
    val pw = new PrintWriter(new File(f))
    (lines :+ (e + "\nEND")).foreach(pw.println)
    pw.close()
  }

  def maxNum(e1: IEFSM, e2: IEFSM = FSet.bot_fset): Int = {
    TypeConversion.toInt(Code_Numeral.integer_of_int(Inference.max_int(FSet.sup_fset(e1, e2))) + 1)
  }

  def scalaDirectlySubsumes(
    e1: TransitionMatrix,
    e2: TransitionMatrix,
    s1: Nat.nat,
    s2: Nat.nat,
    t1: Transition.transition_ext[Unit],
    t2: Transition.transition_ext[Unit]): Boolean = {
    return false
    // Log.root.debug(s"Does ${PrettyPrinter.show(t1)} directly subsume ${PrettyPrinter.show(t2)}? (y/N)")
    // val subsumes = scala.io.StdIn.readLine() == "y"
    // subsumes
  }

  def getTypes(i: List[Value.value]): List[String] = i.map {
    case Value.Inta(_) => "Int"
    case Value.Str(_) => "Str"
    case Value.Reala(_) => "Double"
  }

  def getTypes(r: Map[Nat.nat, Option[Value.value]]): List[String] = {
    val keys = r.keySet.toList.map(x => Code_Numeral.integer_of_nat(x))
    keys.sorted
    keys.map(key => r(Nat.Nata(key)) match {
      case Some(Value.Inta(_)) => "Int"
      case Some(Value.Str(_)) => "String"
      case Some(Value.Reala(_)) => "Double"
      case None => throw new IllegalArgumentException("Got none from a map")
    })
  }

  def sortedValues(r: Map[Nat.nat, Option[Value.value]]): List[String] = {
    val keys = r.keySet.toList.map(x => Code_Numeral.integer_of_nat(x))
    keys.sorted
    keys.map(key => r(Nat.Nata(key)) match {
      case Some(Value.Inta(Int.int_of_integer(n))) => n.toString
      case Some(Value.Reala(r)) => TypeConversion.toDouble(r).toString
      case Some(Value.Str(s)) => "\"" + s + "\""
      case None => throw new IllegalArgumentException("Got none from a map")
    })
  }

  var guardMap = scala.collection.immutable.Map[List[((List[Value.value], scala.collection.immutable.Map[Nat.nat, Option[Value.value]]), Boolean)], Option[GExp.gexp[VName.vname]]]()
  // var guardMem: List[mint.inference.gp.tree.Node[mint.tracedata.types.VariableAssignment[_]]] = List()
  // var vars: scala.collection.immutable.Map[(String, Value.value), VariableAssignment[_]] = scala.collection.immutable.Map()

  // def varOf(name: String, value: Value.value): VariableAssignment[_] = {
  //   if (vars.isDefinedAt((name, value)))
  //     return vars((name, value))
  //   value match {
  //     case Value.Inta(n) => {
  //       vars += ((name, value) -> new IntegerVariableAssignment(name, TypeConversion.toLong(n)))
  //     }
  //     case Value.Reala(n) => {
  //       vars += ((name, value) -> new DoubleVariableAssignment(name, TypeConversion.toDouble(n)))
  //     }
  //     case Value.Str(s) => {
  //       vars += ((name, value) -> new StringVariableAssignment(name, s))
  //     }
  //   }
  //   return vars((name, value))
  // }

  // def varOf(nv: (String, Value.value)): VariableAssignment[_] = varOf(nv._1, nv._2)

  val sys = py.module("sys")
  sys.path.append("./src/main/python")
  val deap_gp = py.module("deap_gp")

  def findDistinguishingGuards(
    g1: (List[(List[Value.value], Map[Nat.nat, Option[Value.value]])]),
    g2: (List[(List[Value.value], Map[Nat.nat, Option[Value.value]])])): Option[(GExp.gexp[VName.vname], GExp.gexp[VName.vname])] = {

    return None
    // val ioPairs = (g1 zip List.fill(g1.length)(true)) ++ (g1 zip List.fill(g1.length)(false))
    //
    // if (guardMap isDefinedAt ioPairs) guardMap(ioPairs) match {
    //   case None => return None
    //   case Some(g) => return Some((g, GExp.gNot(g)))
    // }
    //
    // BasicConfigurator.resetConfiguration();
    // BasicConfigurator.configure();
    // Logger.getRootLogger().setLevel(Level.OFF);
    //
    // val gpGenerator: Generator = new Generator(new java.util.Random(Config.config.guardSeed))
    //
    // IntegerVariableAssignment.clearValues()
    // StringVariableAssignment.clearValues()
    // DoubleVariableAssignment.clearValues()
    //
    // // No supported stringNonTerms
    // gpGenerator.addFunctions(GP.intNonTerms);
    // gpGenerator.addFunctions(GP.doubleNonTerms);
    // gpGenerator.addFunctions(GP.boolNonTerms)
    //
    // var intVarVals = List(0l, 1l, 2l)
    // var doubleVarVals = List(0.0, 1.0, 2.0)
    // var stringVarVals = List[String]("")
    //
    // var intTerms = List[VariableTerminal[_]]()
    // var doubleTerms = List[VariableTerminal[_]]()
    // var stringTerms = List[VariableTerminal[_]]()
    //
    // var intVarNames = List[String]()
    // var doubleVarNames = List[String]()
    // var stringVarNames = List[String]()
    //
    // val trainingSet = new HashSetValuedHashMap[java.util.List[VariableAssignment[_]], VariableAssignment[_]]()
    //
    // // g1 needs to be true
    // for ((inputs, registers) <- g1) {
    //   var scenario = List[VariableAssignment[_]]()
    //   for ((ip, ix) <- inputs.zipWithIndex) ip match {
    //     case Value.Inta(n) => {
    //       intVarVals = TypeConversion.toLong(n) :: intVarVals
    //       intVarNames = s"i${ix}" :: intVarNames
    //       scenario = (varOf((s"i${ix}", Value.Inta(n)))) :: scenario
    //     }
    //     case Value.Reala(n) => {
    //       doubleVarVals = TypeConversion.toDouble(n) :: doubleVarVals
    //       doubleVarNames = s"i${ix}" :: doubleVarNames
    //       scenario = (varOf((s"i${ix}", Value.Reala(n)))) :: scenario
    //     }
    //     case Value.Str(s) => {
    //       stringVarVals = s :: stringVarVals
    //       stringVarNames = s"i${ix}" :: stringVarNames
    //       scenario = (varOf((s"i${ix}", Value.Str(s)))) :: scenario
    //     }
    //   }
    //   for ((r, v) <- registers) v match {
    //     case None => {}
    //     case Some(Value.Inta(n)) => {
    //       intVarVals = TypeConversion.toLong(n) :: intVarVals
    //       intVarNames = s"r${PrettyPrinter.show(r)}" :: intVarNames
    //       scenario = varOf((s"r${PrettyPrinter.show(r)}", Value.Inta(n))) :: scenario
    //     }
    //     case Some(Value.Reala(n)) => {
    //       doubleVarVals = TypeConversion.toDouble(n) :: doubleVarVals
    //       doubleVarNames = s"r${PrettyPrinter.show(r)}" :: doubleVarNames
    //       scenario = varOf((s"r${PrettyPrinter.show(r)}", Value.Reala(n))) :: scenario
    //     }
    //     case Some(Value.Str(s)) => {
    //       stringVarVals = s :: stringVarVals
    //       stringVarNames = s"r${PrettyPrinter.show(r)}" :: stringVarNames
    //       scenario = varOf((s"r${PrettyPrinter.show(r)}", Value.Str(s))) :: scenario
    //
    //     }
    //   }
    //   trainingSet.put(scenario, new BooleanVariableAssignment("g1", true))
    // }
    //
    // // g1 needs to be false if g2 is true
    // for ((inputs, registers) <- g2) {
    //   var scenario = List[VariableAssignment[_]]()
    //   for ((ip, ix) <- inputs.zipWithIndex) ip match {
    //     case Value.Inta(n) => {
    //       intVarVals = TypeConversion.toLong(n) :: intVarVals
    //       intVarNames = s"i${ix}" :: intVarNames
    //       scenario = (varOf((s"i${ix}", Value.Inta(n)))) :: scenario
    //     }
    //     case Value.Reala(n) => {
    //       doubleVarVals = TypeConversion.toDouble(n) :: doubleVarVals
    //       doubleVarNames = s"i${ix}" :: doubleVarNames
    //       scenario = (varOf((s"i${ix}", Value.Reala(n)))) :: scenario
    //     }
    //     case Value.Str(s) => {
    //       stringVarVals = s :: stringVarVals
    //       stringVarNames = s"i${ix}" :: stringVarNames
    //       scenario = (varOf((s"i${ix}", Value.Str(s)))) :: scenario
    //     }
    //   }
    //   for ((r, v) <- registers) v match {
    //     case None => {}
    //     case Some(Value.Inta(n)) => {
    //       intVarVals = TypeConversion.toLong(n) :: intVarVals
    //       intVarNames = s"r${PrettyPrinter.show(r)}" :: intVarNames
    //       scenario = varOf((s"r${PrettyPrinter.show(r)}", Value.Inta(n))) :: scenario
    //     }
    //     case Some(Value.Reala(n)) => {
    //       doubleVarVals = TypeConversion.toDouble(n) :: doubleVarVals
    //       doubleVarNames = s"r${PrettyPrinter.show(r)}" :: doubleVarNames
    //       scenario = varOf((s"r${PrettyPrinter.show(r)}", Value.Reala(n))) :: scenario
    //     }
    //     case Some(Value.Str(s)) => {
    //       stringVarVals = s :: stringVarVals
    //       stringVarNames = s"r${PrettyPrinter.show(r)}" :: stringVarNames
    //       scenario = varOf((s"r${PrettyPrinter.show(r)}", Value.Str(s))) :: scenario
    //
    //     }
    //   }
    //   trainingSet.put(scenario, new BooleanVariableAssignment("g1", false))
    // }
    //
    // intTerms = intVarNames.distinct.map(intVarName => new IntegerVariableAssignmentTerminal(intVarName, false)) ++
    //            intVarVals.distinct.map(intVarVal => new IntegerVariableAssignmentTerminal(intVarVal)) ++
    //            intTerms
    // doubleTerms = doubleVarNames.distinct.map(doubleVarName => new DoubleVariableAssignmentTerminal(doubleVarName, false)) ++
    //            doubleVarVals.distinct.map(doubleVarVal => new DoubleVariableAssignmentTerminal(doubleVarVal)) ++
    //            doubleTerms
    // stringTerms = stringVarNames.distinct.map(stringVarName => new StringVariableAssignmentTerminal(new StringVariableAssignment(stringVarName), false, false)) ++
    //               stringVarVals.distinct.map(stringVarVal => new StringVariableAssignmentTerminal(new StringVariableAssignment(stringVarVal, stringVarVal), true, false)) ++
    //               stringTerms
    //
    // gpGenerator.setTerminals(GP.boolTerms++intTerms++stringTerms++doubleTerms)
    //
    // Log.root.debug("Guard training set: " + trainingSet)
    //
    // // If any of the guards need to simultaneously be true and false then stop
    // if (trainingSet.keys().stream().anyMatch(x => trainingSet.get(x).size() > 1)) {
    //   Log.root.debug("    UNSATISFIABLE")
    //   guardMap = guardMap + (ioPairs -> None)
    //   return None
    // }
    //
    // var gp = new LatentVariableGP(gpGenerator, trainingSet, new GPConfiguration(100, 10, 1f, 2));
    //
    // guardMem.find(f => gp.isCorrect(f)  && f.varsInTree().stream().allMatch(v => !v.isLatent())) match {
    //   case None => {}
    //   case Some(best) => {
    //     Log.root.debug("    Best memoised guard is: " + best)
    //     Log.root.debug("    Best guard is correct")
    //     val gexp = TypeConversion.toGExp(best)
    //     return Some((gexp, GExp.gNot(gexp)))
    //   }
    // }
    //
    // val best = gp.evolve(100).asInstanceOf[Node[VariableAssignment[_]]].simp
    //
    // Log.root.debug("  Best guard is: " + best)
    //
    // val gexp = TypeConversion.toGExp(best)
    //
    // if (gp.isCorrect(best)) {
    //   Log.root.debug("  Best guard is correct")
    //   guardMap = guardMap + (ioPairs -> Some(gexp))
    //   guardMem = best :: guardMem
    //   return Some((gexp, GExp.gNot(gexp)))
    // } else {
    //   guardMap = guardMap + (ioPairs -> None)
    //   return None
    // }
  }

  var funMem: List[Any] = List()

  def setupTrainingSet(ioPairs: List[(List[Value.value], (Map[Nat.nat, Option[Value.value]], Value.value))]): (py.Dynamic, Map[String, String]) = {
    var points: List[Map[String, Any]] = List()
    var types: Map[String, String] = Map()

    for (t <- ioPairs) t match {
      case (inputs, (anteriorRegs, output)) => {
        var point: Map[String, Object] = Map()
        for ((ip, ix) <- inputs.zipWithIndex) {
          val inx = s"i${ix}"
          ip match {
            case Value.Inta(n) => {
              point = point + (inx -> TypeConversion.toLong(n).asInstanceOf[Integer])
              types = types + (inx -> "Int")
            }
            case Value.Reala(n) => {
              point = point + (inx -> TypeConversion.toDouble(n).asInstanceOf[java.lang.Double])
              types = types + (inx -> "Real")
            }
            case Value.Str(s) => {
              point = point + (inx -> s)
              types = types + (inx -> "String")
            }
          }
        }
        for ((r: Nat.nat, v: Option[Value.value]) <- anteriorRegs) {
          val rx = s"r${TypeConversion.toInt(r)}"
          v match {
            case None => throw new IllegalStateException("Got None from registers")
            case Some(Value.Inta(n)) => {
              point = point + (rx -> TypeConversion.toLong(n).asInstanceOf[Integer])
              types = types + (rx -> "Int")
            }
            case Some(Value.Reala(n)) => {
              point = point + (rx -> TypeConversion.toDouble(n).asInstanceOf[java.lang.Double])
              types = types + (rx -> "Real")
            }
            case Some(Value.Str(s)) => {
              point = point + (rx -> s)
              types = types + (rx -> "String")
            }
          }
        }

        output match {
          case Value.Inta(n) => {
            point = point + ("expected" -> TypeConversion.toLong(n).asInstanceOf[Integer])
            types = types + ("expected" -> "Int")
          }
          case Value.Reala(n) => {
            point = point + ("expected" -> TypeConversion.toDouble(n).asInstanceOf[java.lang.Double])
            types = types + ("expected" -> "Real")
          }
          case Value.Str(s) => {
            point = point + ("expected" -> s)
            types = types + ("expected" -> "String")
          }
        }
        points = point :: points
      }
    }

    val flatpoints = points.flatten
      .groupBy(_._1)
      .mapValues(_.map(_._2))

    val pd = py.module("pandas")
    val training_set = pd.DataFrame()

    types("expected") match {
      case "Int" => training_set.insert(0, "expected", flatpoints("expected").asInstanceOf[List[Long]].toPythonProxy)
      case "Real" => training_set.insert(0, "expected", flatpoints("expected").asInstanceOf[List[Double]].toPythonProxy)
      case "String" => {
        training_set.insert(0, "expected", flatpoints("expected").asInstanceOf[List[String]].toPythonProxy)
        training_set.bracketUpdate("expected", training_set.bracketAccess("expected").astype("string"))
      }
      case _ => throw new IllegalStateException(f"Type of expected value should be Int, Real, or String, not ${types("expected")}")
    }

    for ((col, vals) <- flatpoints - "expected") {
      types(col) match {
        case "Int" => training_set.insert(0, col, vals.asInstanceOf[List[Int]].toPythonProxy)
        case "Real" => training_set.insert(0, col, vals.asInstanceOf[List[Double]].toPythonProxy)
        case "String" => {
          training_set.insert(0, col, vals.asInstanceOf[List[String]].toPythonProxy)
          training_set.bracketUpdate(col, training_set.bracketAccess(col).astype("string"))
        }
        case _ => throw new IllegalStateException(f"Type of $col should be Int, Real, or String, not ${types("expected")}")
      }
    }

    return (training_set, types)
  }

  def getUpdate(
    l: String,
    r: Nat.nat,
    values: List[Value.value],
    train: List[(List[Value.value], (Map[Nat.nat, Option[Value.value]], Map[Nat.nat, Option[Value.value]]))]): Option[AExp.aexp[VName.vname]] = {

    Log.root.debug(f"  Getting update for $l")

    val r_index = TypeConversion.toInt(r)
    val ioPairs = (train.map {
      case (inputs, (aregs, pregs)) => pregs(r) match {
        case None => throw new IllegalStateException("Got None from registers")
        case Some(v) => (inputs, (aregs.filterKeys(_ == r), v))
      }
    }).distinct

    val (training_set, types) = setupTrainingSet(ioPairs)
    Log.root.debug("  Output training set:\n" + training_set)

    //
    // for (intVarName <- intVarNames.distinct) {
    //   intTerms = (new IntegerVariableAssignmentTerminal(intVarName, false)) :: intTerms
    // }
    //
    // for (doubleVarName <- doubleVarNames.distinct) {
    //   doubleTerms = (new DoubleVariableAssignmentTerminal(doubleVarName, false)) :: doubleTerms
    // }
    //
    // for (stringVarName <- stringVarNames.distinct) {
    //   stringTerms = (new StringVariableAssignmentTerminal(new StringVariableAssignment(stringVarName), false, false)) :: stringTerms
    // }
    //
    // gpGenerator.setTerminals(intTerms++stringTerms++doubleTerms)
    //
    // Log.root.debug("    Update training set: " + trainingSet)
    //
    // // If number of inputs < possible outputs then we can't solve it
    // if (trainingSet.keys().stream().anyMatch(x => trainingSet.get(x).size() > 1 && x.size() < trainingSet.get(x).size())) {
    //   Log.root.debug("    Too few inputs for possible updates")
    //   return None
    // }
    //
    // var gp = new LatentVariableGP(gpGenerator, trainingSet, new GPConfiguration(100, 10, 1f, 2));
    //
    // funMem.find(f => gp.isCorrect(f) && f.varsInTree().stream().allMatch(v => !v.isLatent())) match {
    //   case None => {}
    //   case Some(best) => {
    //     Log.root.debug("    Best memoised update is: " + best)
    //     Log.root.debug("    Best update is correct")
    //
    //     return Some(TypeConversion.toAExp(best))
    //   }
    // }
    //
    // // =========================================================================
    // // Delete these seeds
    // // val sub = new SubtractIntegersOperator()
    // // sub.addChild(new IntegerVariableAssignmentTerminal(100))
    // // sub.addChild(new IntegerVariableAssignmentTerminal("r1", false))
    // // gp.addSeed(sub)
    // //
    // // val add = new AddDoublesOperator()
    // // add.addChild(new DoubleVariableAssignmentTerminal("i0", false))
    // // add.addChild(new DoubleVariableAssignmentTerminal("r1", true))
    // // gp.addSeed(add)
    // //
    // // val add2 = new AddIntegersOperator()
    // // add2.addChild(new IntegerVariableAssignmentTerminal("i0", false))
    // // add2.addChild(new IntegerVariableAssignmentTerminal("r2", true))
    // // gp.addSeed(add2)
    // // =========================================================================
    //
    // gp.setSeeds((intTerms ++ stringTerms))
    //
    val pset = deap_gp.setup_pset(training_set)
    val best = deap_gp.run_gp(training_set, pset, random_seed=Config.config.updateSeed)
    Log.root.debug("    Best update is: " + best)

    if (deap_gp.correct(best, training_set, pset).toString == "True") {
      Log.root.debug(f"  Best output $best is correct")
      val (nodes, edges, labels) = deap_gp.graph(best).as[(List[Int], List[(Int, Int)], Map[Int, String])]

      val aexp = TypeConversion.toAExp(nodes, edges, labels)
      println(best, aexp)
      if (!AExp.is_lit(aexp))
        funMem = best :: funMem
      val stringTypes = types - "expected"
      println(stringTypes)
      // val stringTypes = deap_gp.get_types(training_set).as[Map[String, String]] - "expected"
      println(best, stringTypes)
      println(training_set.dtypes)
      return Some(aexp)
    } else {
      return None
    }
  }

  def getOutput(
    label: String,
    maxReg: Nat.nat,
    values: List[Value.value],
    ioPairs: List[(List[Value.value], (Map[Nat.nat, Option[Value.value]], Value.value))],
    latentVariable: Boolean = false): Option[(AExp.aexp[VName.vname], Map[VName.vname, String])] = {
    Log.root.debug(f"Getting Output for $label")

    val outputs = ioPairs.map(x => x._2._2)

    if (outputs.distinct.length == 1) {
      Log.root.debug("  Singleton literal output")
      return Some(AExp.L(outputs(0)), scala.collection.immutable.Map())
    }

    val r_index = TypeConversion.toInt(maxReg) + 1

    var (training_set, types) = setupTrainingSet(ioPairs)

    // If we have a key that's empty but returns more than one value then we need a latent variable
    if (deap_gp.shortcut_latent(training_set).as[Boolean]) {
      Log.root.debug(f"  No inputs = output latent variable r$r_index")
      val reg = TypeConversion.vnameFromString(f"r$r_index")
      return Some(AExp.V(reg), Map(reg -> types("expected")))
    }

    // Cut straight to having a latent variable if there's more possible outputs than inputs
    if (!latentVariable && deap_gp.need_latent(training_set).as[Boolean]) {
        Log.root.debug("  Nondeterminism = try with latent variable")
        return getOutput(label, maxReg, values, ioPairs, true)
    }

    Log.root.debug("  Output training set:\n" + training_set)

    // =========================================================================
    // Delete these seeds
    // val sub = new SubtractIntegersOperator()
    // sub.addChild(new IntegerVariableAssignmentTerminal(100))
    // sub.addChild(new IntegerVariableAssignmentTerminal("r1", false))
    // gp.addSeed(sub)
    //
    // val add = new AddDoublesOperator()
    // add.addChild(new DoubleVariableAssignmentTerminal("i0", false))
    // add.addChild(new DoubleVariableAssignmentTerminal("r1", true))
    // gp.evaluatePopulation(List(add))
    // gp.addSeed(add)
    //
    // val add2 = new AddIntegersOperator()
    // add2.addChild(new IntegerVariableAssignmentTerminal("i0", false))
    // add2.addChild(new IntegerVariableAssignmentTerminal("r2", true))
    // gp.addSeed(add2)
    // =========================================================================

    // funMem.find(f => gp.isCorrect(f) && f.varsInTree().stream().allMatch(v => if (v.isLatent()) v.getName() == f"r$r_index" else true )) match {
    //   case None => {}
    //   case Some(best) => {
    //     Log.root.debug("    Best memoised output is: " + best)
    //     Log.root.debug("    Best output is correct")
    //     return Some((TypeConversion.toAExp(best), getTypes(best)))
    //   }
    // }

    if (latentVariable) {
      training_set.insert(0, f"r$r_index", py"None")
      types = types + (f"r$r_index" -> types("expected"))
    }

    val pset = deap_gp.setup_pset(training_set)
    for (value <- values) value match {
      case Value.Inta(i) => pset.addTerminal(TypeConversion.toLong(i), py"int")
      case Value.Reala(r) => pset.addTerminal(TypeConversion.toDouble(r), py"float")
      case Value.Str(s) => pset.addTerminal(s, py"str")
    }

    var best = deap_gp.run_gp(training_set, pset, random_seed=Config.config.outputSeed)
    // for (i <- 1 until 20) {
    //       best = deap_gp.run_gp(training_set, pset, random_seed=Config.config.outputSeed)
    //       println(f"Run $i best is $best")
    // }
    Log.root.debug("    Best output is: " + best)

    // TODO: Make sure the configs match
    // var gp = new LatentVariableGP(gpGenerator, trainingSet, new GPConfiguration(100, 10, 1f, 2));

    // TODO: Find a way to set the seeds
    // gp.setSeeds((intTerms ++ stringTerms).filter(x => !x.isConstant()))
    // val best = gp.evolve(100).asInstanceOf[Node[VariableAssignment[_]]].simp

    // Log.root.debug("  Best output is: " + best)

    if (deap_gp.correct(best, training_set, pset).toString == "True") {
      Log.root.debug(f"  Best output $best is correct")
      val (nodes, edges, labels) = deap_gp.graph(best).as[(List[Int], List[(Int, Int)], Map[Int, String])]

      val aexp = TypeConversion.toAExp(nodes, edges, labels)
      println(best, aexp)
      if (!AExp.is_lit(aexp))
        funMem = best :: funMem
      val stringTypes = types - "expected"
      println(stringTypes)
      println(best, stringTypes)
      println(training_set.dtypes)

      return Some((aexp, stringTypes.map(x => (TypeConversion.vnameFromString(x._1), x._2)).toMap))
    } else if (!latentVariable) {
      Log.root.debug("Trying again with a latent variable")
      return getOutput(label, maxReg, values, ioPairs, true)
    } else return None
  }

  def getRegs(
    types: Map[VName.vname, String],
    i: List[Value.value],
    f: AExp.aexp[VName.vname],
    v: Value.value): Map[Nat.nat, Option[Value.value]] = {
    val expVars: List[VName.vname] = Lista.sorted_list_of_set(AExp.enumerate_vars(f))
    val definedVars = (0 to i.length).map(i => VName.I(Nat.Nata(i)))
    val undefinedVars = expVars.filter(v => !definedVars.contains(v))

    // Log.root.debug("\noutputFun: " + PrettyPrinter.aexpToString(f, true) + " = " + PrettyPrinter.show(v))
    // Log.root.debug("  expVars: " + expVars)
    // Log.root.debug("  undefinedVars: " + undefinedVars)

    var inputs: String = ""
    for (v <- expVars) {
      inputs += f"(${PrettyPrinter.vnameToString(v)} ${types(v)})"
    }
    var z3String: String = f"(define-fun f (${inputs}) ${TypeConversion.typeString(v)} \n  ${toZ3Native(f)}\n)\n"
    for (v <- undefinedVars) {
      z3String += f"(declare-const ${PrettyPrinter.vnameToString(v)} ${types(v)})\n"
    }
    val args = expVars.zipWithIndex.map {
      case (v: VName.vname, k: Int) =>
        if (definedVars.contains(v)) {
          PrettyPrinter.show(i(k))
        } else {
          PrettyPrinter.vnameToString(v)
        }
    }

    if (args.length == 0) {
      val assertion: String = "(assert (= " + PrettyPrinter.show(v) + " f))"
      z3String += assertion
    } else {
      val assertion: String = "(assert (= " + PrettyPrinter.show(v) + " (f " + args.mkString(" ") + ")))"
      z3String += assertion
    }

    val ctx = new z3.Context()
    val solver = ctx.mkSimpleSolver()

    solver.fromString(z3String)
    solver.check()
    val model: z3.Model = solver.getModel

    var regs: Map[Nat.nat, Option[Value.value]] = scala.collection.immutable.Map()
    for (f <- model.getConstDecls) {
      val constInterp = model.getConstInterp(f)
      regs = regs + (Nat.Nata(BigInt(f.getName.toString.substring(1).toInt)) -> Some(TypeConversion.toValue(model.getConstInterp(f))))
    }
    ctx.close()
    regs
  }
}
