import com.microsoft.z3
import java.io._
import scala.io.Source
import scala.util.Random
import sys.process._
import Types._
import ShowImplicits._

import scala.collection.JavaConversions._

import org.apache.commons.math3.util.Precision

import me.shadaj.scalapy.py
import me.shadaj.scalapy.py.SeqConverters
import py.PyQuote

object Dirties {
  // let doubles be "equal" that are within 1% of one another
  def doubleEquals(a: Real.real, b: Real.real, epsilon: Double = 0.0001): Boolean = {
    return Precision.equals(TypeConversion.toDouble(a), TypeConversion.toDouble(b), epsilon)
  }

  def defaultValue[A, B](m: Map[A, B]): B = m match {
    case m: Map.WithDefault[A, B] => m.default(null.asInstanceOf[A])
    case _ => throw new IllegalArgumentException("Map has no default value.")
  }

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

  var guardMap = scala.collection.immutable.Map[List[(List[Value.value], (Map[Nat.nat, Option[Value.value]], (Value.Inta, List[Int])))], Option[GExp.gexp[VName.vname]]]()
  var guardMem: List[Any] = List()

  val sys = py.module("sys")
  val site = py.module("site")
  sys.path.append("./src/main/python")
  for (p <- site.getsitepackages().as[List[String]])
    sys.path.append(p)
  val deap_gp = py.module("deap_gp")

  def findDistinguishingGuards(
    g1: (List[(List[Value.value], Map[Nat.nat, Option[Value.value]])]),
    g2: (List[(List[Value.value], Map[Nat.nat, Option[Value.value]])])): Option[(GExp.gexp[VName.vname], GExp.gexp[VName.vname])] = {
      Log.root.debug(f"${"-"*84}\nGetting a distinguishing guard")
      Log.root.debug(f"$g1")
      Log.root.debug(f"$g2")
      Config.config.guardSeed += 1


    val ioPairs = g1.map(ir => (ir._1, (ir._2, (Value.Inta(Int.int_of_integer(1)), List())))) ++ g2.map(ir => (ir._1, (ir._2, (Value.Inta(Int.int_of_integer(0)), List()))))

    // (g1 zip List.fill(g1.length)(Value.Inta(Int.int_of_integer(1)))) ++ (g1 zip List.fill(g1.length)(Value.Inta(Int.int_of_integer(0))))
    val (training_set, types, latent_vars_rows) = setupTrainingSet(ioPairs)
    training_set.bracketUpdate("expected", training_set.bracketAccess("expected").astype("bool"))
    val pset = deap_gp.setup_pset(training_set)

    // If any of the guards need to simultaneously be true and false then stop
    if (deap_gp.need_latent(training_set, latent_vars_rows.toPythonProxy).as[Boolean]) {
      Log.root.debug("    UNSATISFIABLE")
      guardMap = guardMap + (ioPairs -> None)
      return None
    }

    // guardMem.find(f => funMemFind(f.asInstanceOf[me.shadaj.scalapy.py.Any], training_set, pset, false, f"")) match {
    //   case None => {}
    //   case Some(best) => {
    //     Log.root.debug("    Best memoised guard is: " + best)
    //     Log.root.debug("    Best guard is correct")
    //     val (nodes, edges, labels) = deap_gp.graph(best.asInstanceOf[me.shadaj.scalapy.py.Any]).as[(List[Int], List[(Int, Int)], Map[Int, String])]
    //     val gexp = TypeConversion.toGExp(nodes, edges, labels)
    //     return Some((gexp, GExp.gNot(gexp)))
    //   }
    // }

    var seeds: List[String] = List()
    var best = deap_gp.run_gp(training_set, pset, random_seed = Config.config.outputSeed, seeds = seeds.toPythonProxy, ngen = Config.config.ngen)
    Log.root.debug("    Best guard is: " + best)

    if (deap_gp.correct(best, training_set, pset, latent_vars_rows=latent_vars_rows.toPythonProxy).as[Boolean]) {
      Log.root.debug(f"  Best guard $best is correct")
      guardMem = best :: guardMem
      val (nodes, edges, labels) = deap_gp.graph(best).as[(List[Int], List[(Int, Int)], Map[Int, String])]
      val gexp = TypeConversion.toGExp(nodes, edges, labels)
      return Some((gexp, GExp.gNot(gexp)))
    } else {
      return None
    }
  }

  // var funMem: Map[String, List[Any]] = Map().withDefaultValue(List())

  def returnTrainingSet(training_set: py.Dynamic, known_regs: List[List[String]]): (py.Dynamic, List[List[String]]) = {
    val cols = py"list($training_set.columns.values)"
    py"$cols.pop($cols.index('expected'))"
    training_set.bracketUpdate("known", py"[tuple(t) for t in ${known_regs.toPythonProxy}]")
    training_set.drop_duplicates(inplace=true)
    Log.root.debug(f"Training set:\n$training_set")
    Log.root.debug(py"$training_set.dtypes".toString)
    val defined_regs = cols.as[List[String]].filter(x => x.startsWith("r"))
    val latent_vars_rows = py"$training_set['known'].tolist()".as[List[List[String]]].map(regs => defined_regs.filter(x => !regs.contains(x)))
    return (py"$training_set[$cols+['expected']]", latent_vars_rows)
  }

  def setupTrainingSet(ioPairs: List[(List[Value.value], (Map[Nat.nat, Option[Value.value]], (Value.value, List[Nat.nat])))]): (py.Dynamic, Map[String, String], List[List[String]]) = {
    var points: List[Map[String, Any]] = List()
    var types: Map[String, String] = Map()

    for (t <- ioPairs) t match {
      case (inputs, (anteriorRegs, (output, latent))) => {
        var point: Map[String, Object] = Map("latent" -> latent.map(x => f"r${TypeConversion.toInt(x)}"))
        for ((ip, ix) <- inputs.zipWithIndex) {
          val inx = s"i${ix}"
          ip match {
            case Value.Inta(n) => {
              point = point + (inx -> TypeConversion.toLong(n).asInstanceOf[java.lang.Long])
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
        if (anteriorRegs.size > 0)
          for ((r: Nat.nat, v: Option[Value.value]) <- anteriorRegs) {
            val rx = s"r${TypeConversion.toInt(r)}"
            v match {
              case None => {} //throw new IllegalStateException("Got None from registers")
              case Some(Value.Inta(n)) => {
                point = point + (rx -> TypeConversion.toLong(n).asInstanceOf[java.lang.Long])
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
            point = point + ("expected" -> TypeConversion.toLong(n).asInstanceOf[java.lang.Long])
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

    val pd = py.module("pandas")

    // Only keep data of the same type as the expected value
    val known_regs: List[List[String]] = points.map(row => row("latent").asInstanceOf[List[String]])
    points = points.map(row => row.filter(v => v._1 != "latent" && types(v._1) == types("expected")))

    types("expected") match {
      case "Int" => {
        val training_set = pd.DataFrame(points.asInstanceOf[List[Map[String, Long]]].toPythonProxy, dtype = "Int64")
        val (ts, latent) =  returnTrainingSet(training_set, known_regs)
        return (ts, types, latent)
      }
      case "Real" => {
        val training_set = pd.DataFrame(points.asInstanceOf[List[Map[String, Double]]].toPythonProxy, dtype = "float64")
        val (ts, latent) =  returnTrainingSet(training_set, known_regs)
        return (ts, types, latent)
      }
      case "String" => {
        val training_set = pd.DataFrame(points.asInstanceOf[List[Map[String, String]]].toPythonProxy, dtype = "string")
        val (ts, latent) =  returnTrainingSet(training_set, known_regs)
        return (ts, types, latent)
      }
      case _ => throw new IllegalStateException(f"Type of expected value should be Int, Real, or String, not ${types("expected")}")
    }
  }

  def toValueType(s: String): PTA_Generalisation.value_type = {
    if (s == "Int")
      return PTA_Generalisation.I()
    if (s == "Real")
      return PTA_Generalisation.R()
    if (s == "String")
      return PTA_Generalisation.S()
    throw new IllegalArgumentException(f"Could not convert type '$s' to a value_type. Can only be 'Int', 'Real', or 'String'")
  }

  def getUpdate(
    l: String,
    r: Nat.nat,
    values: List[Value.value],
    ioPairs: List[(List[Value.value], (Map[Nat.nat, Option[Value.value]], (Value.value, List[Nat.nat])))],
    bads: List[AExp.aexp[VName.vname]] = List()): Option[(AExp.aexp[VName.vname], Map[VName.vname,PTA_Generalisation.value_type])] = {
      Config.config.updateSeed += 1

    Log.root.debug(f"${"-"*84}\nGetting update for $l")

    val r_index = TypeConversion.toInt(r)
    // val ioPairs = (train.map {
    //   case (inputs, (aregs, pregs)) => pregs.getOrElse(r, None) match {
    //     case None => return None //throw new IllegalStateException(f"Got None when trying to access r${PrettyPrinter.show(r)} from registers\n$pregs")
    //     case Some(v) => (inputs, (aregs, v))
    //     // case Some(v) => (inputs, (aregs.filterKeys(_ == r), v))
    //   }
    // }).distinct

    var (training_set, types, _) = setupTrainingSet(ioPairs)
    // We don't want any latent variables in update inference
    val latent_vars_rows=py"[() for i in range(len($training_set))]"
    val output_type = training_set.dtypes.bracketAccess("expected")
    training_set = training_set.select_dtypes(include = output_type)

    // If number of inputs < possible outputs then we can't solve it
    if (deap_gp.need_latent(training_set, latent_vars_rows).as[Boolean]) {
      Log.root.debug(f"    Too few inputs for possible updates\n${"-"*84}")
      return None
    }
    val pset = deap_gp.setup_pset(training_set)
    for (value <- values) value match {
      case Value.Inta(i) => pset.addTerminal(TypeConversion.toLong(i), py"int")
      case Value.Reala(r) => pset.addTerminal(TypeConversion.toDouble(r), py"float")
      case Value.Str(s) => pset.addTerminal(s, py"str")
    }

    // funMem(l).find(f => funMemFind(f.asInstanceOf[me.shadaj.scalapy.py.Any], training_set, pset, false, f"")) match {
    //   case None => {}
    //   case Some(best) => {
    //     Log.root.debug(f"  Best memoised update $best is correct")
    //     val (nodes, edges, labels) = deap_gp.graph(best.asInstanceOf[me.shadaj.scalapy.py.Any]).as[(List[Int], List[(Int, Int)], Map[Int, String])]
    //     val aexp = TypeConversion.toAExp(nodes, edges, labels)
    //     val stringTypes = types - "expected"
    //     return Some(aexp)
    //   }
    // }

    val targets = ioPairs.map(x => x._2._2._1)
    if (targets.distinct.length == 1 && targets.length > 1) {
      Log.root.debug(f"  Singleton literal update\n${"-"*84}")
      return Some((AExp.L(targets(0)), Map().withDefaultValue(PTA_Generalisation.type_signature(targets(0)))))
    }

    var seeds: List[String] = List()

    // if (py"'r'+str($r_index) in $training_set".as[Boolean]) {
    //   if (output_type.toString == "Int64")
    //     seeds ++= List(f"sub(r$r_index, 50)", f"add(r$r_index, 50)", f"sub(r$r_index, 1)", f"add(r$r_index, 1)")
    //   if (py"'i0' in $training_set".as[Boolean])
    //     seeds ++= List(f"sub(r$r_index, i0)", f"add(r$r_index, i0)")
    // }
    // Log.root.debug("Seeds")
    // for (seed <- seeds) {
    //   val fitness = deap_gp.fitness(seed, training_set, pset)
    //   Log.root.debug(f"  $seed: $fitness")
    // }

    var best = deap_gp.run_gp(training_set, pset, random_seed = Config.config.outputSeed, seeds = seeds.toPythonProxy, ngen = Config.config.ngen)
    if (deap_gp.correct(best, training_set, pset, latent_vars_rows=latent_vars_rows).as[Boolean]) {
      Log.root.debug(f"  Best update $best is correct\n${"-"*84}")
      Log.root.debug(f"unused_vars: ${deap_gp.get_unused_vars(best, training_set, latent_vars_rows, verbose=true)}")
      val (nodes, edges, labels) = deap_gp.graph(best).as[(List[Int], List[(Int, Int)], Map[Int, String])]

      val aexp = TypeConversion.toAExp(nodes, edges, labels)
      // if (!AExp.is_lit(aexp))
      //   funMem = funMem + (l -> (best :: funMem(l)))
      val stringTypes = types - "expected"
      return Some((aexp, stringTypes.map(x => (TypeConversion.vnameFromString(x._1), toValueType(x._2)))))
    } else {
      Log.root.debug(f"  Best update $best is incorrect\n${"-"*84}")
      return None
    }
  }

  def to_gp_string(a: AExp.aexp[VName.vname]): String = a match {
      case AExp.L(v) => PrettyPrinter.show(v)
      case AExp.V(v) => PrettyPrinter.vnameToString(v)
      case AExp.Plus(a1, a2) => f"add(${to_gp_string(a1)}, ${to_gp_string(a2)})"
      case AExp.Minus(a1, a2) => f"sub(${to_gp_string(a1)}, ${to_gp_string(a2)})"
      case AExp.Times(a1, a2) => f"mul(${to_gp_string(a1)}, ${to_gp_string(a2)})"
      case AExp.Divide(a1, a2) => f"div(${to_gp_string(a1)}, ${to_gp_string(a2)})"
    }

  def valid_for_pset(a: AExp.aexp[VName.vname], pset: List[String]): Boolean = a match {
      case AExp.L(v) => true
      case AExp.V(v) => pset.contains(PrettyPrinter.vnameToString(v))
      case AExp.Plus(a1, a2) => valid_for_pset(a1, pset) && valid_for_pset(a2, pset)
      case AExp.Minus(a1, a2) => valid_for_pset(a1, pset) && valid_for_pset(a2, pset)
      case AExp.Times(a1, a2) => valid_for_pset(a1, pset) && valid_for_pset(a2, pset)
      case AExp.Divide(a1, a2) => valid_for_pset(a1, pset) && valid_for_pset(a2, pset)
    }

  def getOutput(
    label: String,
    tids: List[Nat.nat],
    maxReg: Nat.nat,
    values: List[Value.value],
    bad_set: Set.set[AExp.aexp[VName.vname]],
    train: List[(List[Value.value], (Map[Nat.nat, Option[Value.value]], (Value.value, List[Nat.nat])))],
    latentVariable: Boolean = false
  ): Option[(AExp.aexp[VName.vname], Map[VName.vname, PTA_Generalisation.value_type])] = {
    Config.config.outputSeed += 1

    Log.root.debug(f"${"="*84}\nGetting Output for ${PrettyPrinter.show(tids)}$label")
    // Log.root.debug(f"ioPairs: ${train.map(ir => "(" + PrettyPrinter.show(ir._1) + ", " + PrettyPrinter.show(ir._2._1) + ", " + PrettyPrinter.show(ir._2._2._1) + PrettyPrinter.show(ir._2._2._2) + ")")}")

    val Set.seta(bad) = bad_set
    Log.root.debug(f"Bad: ${PrettyPrinter.outputsToString(bad)}")


    val r_index = TypeConversion.toInt(maxReg) + 1

    var (training_set, types, latent_vars_rows) = setupTrainingSet(train)
    val output_type = training_set.dtypes.bracketAccess("expected")
    Log.root.debug(f"Output type $output_type")
    Log.root.debug(f"types $types")
    // training_set = training_set.select_dtypes(include=output_type)

    // Cut straight to having a latent variable if there's more possible outputs than inputs
    // if (!latentVariable && deap_gp.need_latent(training_set, latent_vars_rows.toPythonProxy).as[Boolean]) {
    if (!latentVariable && PTA_Generalisation.needs_latent_code(train)) {
      Log.root.debug("  Nondeterminism = try with latent variable")
      return getOutput(label, tids, maxReg, values, bad_set, train, true)
    }

    if (latentVariable) {
      val new_reg =  f"r$r_index"
      training_set.insert(0, new_reg, py"None")
      types = types + (new_reg -> types("expected"))
      latent_vars_rows = latent_vars_rows.map(x => f"r$r_index" :: x)
    }

    val pset = deap_gp.setup_pset(training_set)

    for (value <- values) value match {
      case Value.Inta(i) => pset.addTerminal(TypeConversion.toLong(i), py"int")
      case Value.Reala(r) => pset.addTerminal(TypeConversion.toDouble(r), py"float")
      case Value.Str(s) => pset.addTerminal(s, py"str")
    }

    Log.root.debug("  Consts:" + py"set([c.value for c in $pset.terminals[int] if type(c.value) == int])")
    // Log.root.debug(f"  Values: ${PrettyPrinter.show(values)}")
    Log.root.debug(f"  r_index r$r_index in training_set " + py"'r'+str($r_index) in $training_set".as[Boolean])

    // if (bad.length == 0) {
    //   funMem(label).find(f => funMemFind(f.asInstanceOf[me.shadaj.scalapy.py.Any], training_set, pset, latentVariable, f"r$r_index")) match {
    //     case None => {}
    //     case Some(best) => {
    //       Log.root.debug(f"  Best memoised output $best is correct")
    //       val (nodes, edges, labels) = deap_gp.graph(best.asInstanceOf[me.shadaj.scalapy.py.Any]).as[(List[Int], List[(Int, Int)], Map[Int, String])]
    //       val aexp = TypeConversion.toAExp(nodes, edges, labels)
    //       val stringTypes = types - "expected"
    //       return Some((aexp, stringTypes.map(x => (TypeConversion.vnameFromString(x._1), x._2)).toMap))
    //     }
    //   }
    // }

    val outputs = train.map(x => x._2._2._1)
    if (outputs.distinct.length == 1) {
      Log.root.debug("  Singleton literal output")
      return Some((AExp.L(outputs(0)), scala.collection.immutable.Map()))
    }

    // TODO: Delete these seeds
    // TODO: Delete these seeds
    val pd = py.module("pandas")
    var seeds: List[String] = List()
    // if (py"'i0' in $training_set".as[Boolean] && output_type.toString == "Int64")
    //   seeds ++= List(f"add(i0, 1)", f"sub(i0, 1)")
    // for (i <- 1 to r_index) {
    //   if (py"'r'+str($i) in $training_set".as[Boolean]) {
    //     if (py"'i0' in $training_set".as[Boolean])
    //       seeds ++= List(f"sub(r$i, i0)", f"sub(i0, r$i)", f"add(r$i, i0)")
    //     if (output_type.toString == "Int64") {
    //       seeds ++= List(f"sub(50, r$i)", f"sub(r$i, 50)", f"add(r$i, 50)", f"sub(r$i, 1)", f"add(r$i, 1)", f"0")
    //     }
    //   }
    // }

    // Log.root.debug("Seeds:")
    // for (seed <- seeds) {
    //   val fitness = deap_gp.fitness(seed, training_set, pset)
    //   Log.root.debug(f"  $seed: $fitness")
    // }

    val deap_gp_bad = bad.filter(x => valid_for_pset(x, py"list($pset.mapping.keys())".as[List[String]])).map(x => deap_gp.gp.PrimitiveTree.from_string(to_gp_string(x), pset))
    // Log.root.debug(f"PSET KEYS: ${pset.mapping.keys()}")

    var best = deap_gp.run_gp(training_set, pset, latent_vars_rows=latent_vars_rows.toPythonProxy, random_seed = Config.config.outputSeed, seeds = seeds.toPythonProxy, bad=deap_gp_bad.toPythonProxy, ngen=Config.config.ngen)
    Log.root.debug(f"Best output is $best")

    Log.root.debug("Checking correctness")

    if (deap_gp.correct(best, training_set, pset, latent_vars_rows=latent_vars_rows.toPythonProxy).as[Boolean]) {
      Log.root.debug(f"  Best output $best is correct\n${"="*84}")
      val (nodes, edges, labels) = deap_gp.graph(best).as[(List[Int], List[(Int, Int)], Map[Int, String])]
      val aexp = TypeConversion.toAExp(nodes, edges, labels)
      // if (!AExp.is_lit(aexp))
      //   funMem = funMem + (label -> (best :: funMem(label)))
      val stringTypes = types - "expected"
      return Some((aexp, stringTypes.map(x => (TypeConversion.vnameFromString(x._1), toValueType(x._2)))))
    } else if (!latentVariable) {
      Log.root.debug(f"  Best output $best is incorrect\n${"="*84}")
      return None
      // Log.root.debug("    Failed - Trying again with a latent variable")
      // return getOutput(label, maxReg, values, bad, train, true)
    } else {
      Log.root.debug(f"  Best output $best is incorrect\n${"="*84}")
      return None
    }
  }

  // def funMemFind(f: me.shadaj.scalapy.py.Any, training_set: me.shadaj.scalapy.py.Any, pset: me.shadaj.scalapy.py.Any, latentVariable: Boolean, reg: String): Boolean = {
  //   Log.root.debug(f"$f correct?")
  //
  //   deap_gp.add_consts_to_pset(f, pset)
  //
  //   // Check if all the variables in the expression are defined in the pset
  //   if (!deap_gp.all_vars_defined(f, pset).as[Boolean]) {
  //     val psetMapping = py"$pset.mapping"
  //     Log.root.debug(f"  false - undefined vars ${psetMapping}")
  //     return false
  //   }
  //
  //   // val latent_vars = deap_gp.latent_variables(f, training_set).as[List[String]]
  //   // if (latent_vars.size == 0 || (latent_vars == List(reg) && latentVariable))
  //   val correct = deap_gp.correct(f, training_set, pset).as[Boolean]
  //   Log.root.debug(f"  $correct")
  //   return correct
  //   // return false
  // }

  def getRegs(
    types: Map[VName.vname, PTA_Generalisation.value_type],
    i: List[Value.value],
    f: AExp.aexp[VName.vname],
    v: Value.value): Map[Nat.nat, Option[Value.value]] = {
    val expVars: List[VName.vname] = Lista.sorted_list_of_set(AExp.enumerate_vars(f))
    if (expVars.length == 0) {
      return Map()
    }
    val definedVars = (0 to i.length).map(i => VName.I(Nat.Nata(i)))
    val undefinedVars = expVars.filter(v => !definedVars.contains(v))

    var inputs: String = ""
    for (v <- expVars) {
      inputs += f"(${PrettyPrinter.vnameToString(v)} ${types(v).show})"
    }
    var z3String: String = f"(define-fun f (${inputs}) ${TypeConversion.typeString(v)} \n  ${toZ3Native(f)}\n)\n"
    for (v <- undefinedVars) {
      z3String += f"(declare-const ${PrettyPrinter.vnameToString(v)} ${types(v).show})\n"
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
    // Return an empty map if unsatisfiable
    // NB. unsatisfiable occurs if dividing by zero
    if (solver.check() != z3.Status.SATISFIABLE) {
      return Map().withDefaultValue(None)
    }

    val model: z3.Model = solver.getModel

    var regs: Map[Nat.nat, Option[Value.value]] = scala.collection.immutable.Map().withDefaultValue(None)
    for (f <- model.getConstDecls) {
      val constInterp = model.getConstInterp(f)
      regs = regs + (Nat.Nata(BigInt(f.getName.toString.substring(1).toLong)) -> Some(TypeConversion.toValue(model.getConstInterp(f))))
    }
    ctx.close()
    regs
  }
}
