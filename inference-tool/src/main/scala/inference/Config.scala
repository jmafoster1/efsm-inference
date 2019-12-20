import scopt.OParser
import java.io._
import scala.io.Source
import net.liftweb.json._
import ch.qos.logback.classic.Level
import Types._
import java.nio.file.{ Paths, Files }

object Heuristics extends Enumeration {
  type Heuristic = Value
  val store, inputgen, inc, sr, sr2, distinguish, sru, same, ignore, ignoret, lob, gob, gungho, eq, neq = Value
}

object Nondeterminisms extends Enumeration {
  type Nondetermnism = Value
  val basic, labar, labar_d = Value
}

object Strategies extends Enumeration {
  type Strategy = Value
  val naive, naive_eq_bonus, rank, comprehensive, comprehensiveEQ, eq = Value
}

case class Config(
  heuristics: Seq[Heuristics.Heuristic] = Seq(),
  abs: Boolean = false,
  file: File = null,
  outputname: String = null,
  dotfiles: String = "dotfiles",
  nondeterminismMetric: IEFSM => FSet.fset[(Nat.nat, ((Nat.nat, Nat.nat), ((Types.Transition, List[Nat.nat]), (Types.Transition, List[Nat.nat]))))] = (Inference.nondeterministic_pairs _),
  strategy: List[Nat.nat] => List[Nat.nat] => IEFSM => Nat.nat = (SelectionStrategies.naive_score _).curried,
  skip: Boolean = false,
  logLevel: Level = Level.DEBUG,
  logFile: String = null,
  smallInts: Boolean = false,
  log: List[List[Types.Event]] = List(),
  k: Int = 1,
  gpIterations: Int = 50,
  guardSeed: Int = 0,
  outputSeed: Int = 0,
  updateSeed: Int = 0)

object Config {
  val builder = OParser.builder[Config]
  var config: Config = null
  var heuristics = Inference.try_heuristics(List(), (Inference.nondeterministic_pairs _))
  var numStates: BigInt = 0
  var ptaNumStates: BigInt = 0

  implicit val heuristicsRead: scopt.Read[Heuristics.Value] = scopt.Read.reads(Heuristics withName _)
  implicit val strategiesRead: scopt.Read[List[Nat.nat] => List[Nat.nat] => IEFSM => Nat.nat] =
    scopt.Read.reads {
      _.toLowerCase match {
        case "eq" => (SelectionStrategies.exactly_equal _).curried
        case "naive" => (SelectionStrategies.naive_score _).curried
        case "naive_eq_bonus" => (SelectionStrategies.naive_score_eq_bonus _).curried
        case "rank" => (SelectionStrategies.naive_score_outputs _).curried
        case "comprehensive" => (SelectionStrategies.naive_score_comprehensive _).curried
        case "comprehensiveeq" => (SelectionStrategies.naive_score_comprehensive_eq_high _).curried
        case "origins" => (SelectionStrategies.origin_states _).curried
        case s =>
          throw new IllegalArgumentException(s"'${s}' is not a valid strategy ${Nondeterminisms.values}")
      }
    }
  implicit val levelRead: scopt.Read[Level] =
    scopt.Read.reads {
      _.toLowerCase match {
        case "debug" => Level.DEBUG
        case "warn" => Level.WARN
        case "info" => Level.INFO
        case "error" => Level.ERROR
        case s =>
          throw new IllegalArgumentException(s"'${s}' is not a debug level.")
      }
    }
  implicit val nondeterminismRead: scopt.Read[Types.IEFSM => FSet.fset[(Nat.nat, ((Nat.nat, Nat.nat), ((Types.Transition, List[Nat.nat]), (Types.Transition, List[Nat.nat]))))]] =
    scopt.Read.reads {
      _.toLowerCase match {
        case "basic" => (Inference.nondeterministic_pairs _)
        case "labar" => (Inference.nondeterministic_pairs_labar _)
        case "labar_d" => (Inference.nondeterministic_pairs_labar_dest _)
        case s =>
          throw new IllegalArgumentException(s"'${s}' is not a valid strategy ${Nondeterminisms.values}")
      }
    }

  val source = scala.io.Source.fromFile("lib/head.smt2")
  val z3Head = try source.mkString finally source.close()

  val parser1 = {
    import builder._
    OParser.sequence(
      programName("inference-tool"),
      head("inference-tool", "0.x"),
      help("help").text("prints this usage text"),
      opt[Seq[Heuristics.Heuristic]]('h', "heuristics")
        .valueName("<heuristic1>,<heuristic2>...")
        .action((x, c) => c.copy(heuristics = x))
        .text(s"heuristics to give the inference process ${Heuristics.values}"),
      opt[String]('o', "output")
        .valueName("filename")
        .action((x, c) => c.copy(outputname = x))
        .text("The preferred name of the file to output the SAL and DOT representations of the inferred model to - defaults to the input file name"),
      opt[Int]('k', "k")
        .valueName("k")
        .action((x, c) => c.copy(k = x))
        .text("The depth of the k-tails (defaults to zero)"),
      opt[Int]('i', "gpIterations")
        .valueName("GP iterations")
        .action((x, c) => c.copy(gpIterations = x))
        .text("The number of iterations to run the symbolic regression heuristic for (defaults to 50)"),
      opt[List[Nat.nat] => List[Nat.nat] => IEFSM => Nat.nat]('s', "strategy")
        .valueName("strategy")
        .action((x, c) => c.copy(strategy = x))
        .text(s"The preferred strategy to rank state merges ${Strategies.values}"),
      opt[Types.IEFSM => FSet.fset[(Nat.nat, ((Nat.nat, Nat.nat), ((Types.Transition, List[Nat.nat]), (Types.Transition, List[Nat.nat]))))]]('n', "nondeterminism")
        .valueName("nondeterminism checker")
        .action((x, c) => c.copy(nondeterminismMetric = x))
        .text(s"The preferred definition of nondeterminism - defaults to label, arity, and guard check ${Nondeterminisms.values}"),
      opt[String]('d', "dotfiles")
        .valueName("dir")
        .action((x, c) => c.copy(dotfiles = x))
        .text("The directory in which to save dotfiles produced during the inference process - defaults to 'dotfiles'"),
      opt[Unit]("skip")
        .action((_, c) => c.copy(skip = true))
        .text("Set this flag to skip some model checking tests which should be trivially true"),
      opt[Unit]("small")
        .action((_, c) => c.copy(skip = true))
        .text("Set this flag to map integers down to smaller values"),
      opt[Unit]("abstract")
        .action((_, c) => c.copy(abs = true))
        .text("Set this flag to use abstract traces"),
      opt[Level]('l', "level")
        .valueName("level")
        .action((x, c) => c.copy(logLevel = x))
        .text(s"The log level {info, debug, warn, error}"),
      opt[String]('f', "logFile")
        .valueName("logFile")
        .action((x, c) => c.copy(logFile = x))
        .text(s"The name/location of the logfile"),
      arg[File]("filename")
        .required()
        .action((x, c) => c.copy(file = x))
        .text("The json file listing the traces"),
      opt[Int]('g', "guardSeed")
        .valueName("Random seed for guard GP")
        .action((x, c) => c.copy(guardSeed = x)),
      opt[Int]('p', "outputSeed")
        .valueName("Random seed for output GP")
        .action((x, c) => c.copy(outputSeed = x)),
      opt[Int]('u', "updateSeed")
        .valueName("Random seed for update GP")
        .action((x, c) => c.copy(updateSeed = x)))
  }

  def parseArgs(args: Array[String]) = {
    OParser.parse(parser1, args, Config()) match {
      case Some(configuration) => {
        var config = configuration
        if (config.logFile == null)
          config = config.copy(logFile = config.dotfiles + "/log")
        if (!Files.exists(Paths.get(config.dotfiles)))
          new java.io.File(config.dotfiles).mkdirs
        if (Files.list(Paths.get(config.dotfiles)).findAny().isPresent())
          throw new IllegalArgumentException(s"Dotfiles directory '${config.dotfiles}' is not empty")
        if (Files.exists(Paths.get(config.logFile)))
          throw new IllegalArgumentException(s"Log file '${config.logFile}' already exists")
        if (config.k < 0)
          throw new IllegalArgumentException(s"k must be greater than 0")

        // Set up the log
        val rawJson = Source.fromFile(config.file).getLines.mkString
        val parsed = (parse(rawJson))
        val list = parsed.values.asInstanceOf[List[List[Map[String, Any]]]]
        config = config.copy(log = list.map(run => run.map(x => TypeConversion.toEventTuple(x))))
        if (config.smallInts) {
          config = config.copy(log = Use_Small_Numbers.use_smallest_ints(Config.config.log))
        }

        // Set up the heuristics
        val heuristics = scala.collection.immutable.Map(
          Heuristics.store -> Store_Reuse.heuristic_1(config.log),
          Heuristics.inputgen -> Store_Reuse.heuristic_2(config.log),
          Heuristics.inc -> (Increment_Reset.insert_increment_2 _).curried,
          Heuristics.sr -> (Symbolic_Regression.infer_output_functions _).curried(config.log),
          Heuristics.sr2 -> (Symbolic_Regression.infer_output_functions_2 _).curried(config.log),
          Heuristics.sru -> (Symbolic_Regression.infer_output_update_functions _).curried(config.log),
          Heuristics.distinguish -> (Distinguishing_Guards.distinguish _).curried(config.log),
          Heuristics.same -> (Same_Register.same_register _).curried,
          Heuristics.ignore -> (Ignore_Inputs.drop_inputs _).curried,
          Heuristics.ignoret -> (Ignore_Inputs.transitionwise_drop_inputs _).curried,
          Heuristics.lob -> (Least_Upper_Bound.lob _).curried,
          Heuristics.gob -> (Least_Upper_Bound.gob _).curried,
          Heuristics.gungho -> (Least_Upper_Bound.gung_ho _).curried,
          Heuristics.eq -> (Equals.equals _).curried,
          Heuristics.neq -> (Equals.not_equals _).curried)

        // this.strategy = if (Config.config.oneFinal)
        //     (SelectionStrategies.score_one_final_state _).curried(strategies(config.strategy))
        //   else (strategies(config.strategy))
        this.heuristics = Inference.try_heuristics_check((Inference.satisfies _).curried(Set.seta(config.log)), config.heuristics.map(x => heuristics(x)).toList, config.nondeterminismMetric)
        this.config = config

      }
      case _ =>
        System.exit(1)
    }
  }

}
