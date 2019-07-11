import scopt.OParser
import java.io._
import scala.io.Source
import net.liftweb.json._
import ch.qos.logback.classic.Level

object Heuristics extends Enumeration {
  type Heuristic = Value
  val store, inc, same, ignore, ignoret, ignores = Value
}

object Nondeterminisms extends Enumeration {
  type Nondeterminism = Value
  val basic, labar = Value
}

object Strategies extends Enumeration {
  type Strategy = Value
  val naive, rank, comprehensive, comprehensiveEQ = Value
}

case class Config(
  heuristics: Seq[Heuristics.Heuristic] = Seq(),
  file: File = null,
  outputname: String = null,
  dotfiles: String = "dotfiles",
  nondeterminism: Nondeterminisms.Nondeterminism = Nondeterminisms.basic,
  strategy: Strategies.Strategy = Strategies.naive,
  oneFinal: Boolean = false,
  logLevel: Level = Level.DEBUG,
  k: Int = 0
)

object Config {
  val builder = OParser.builder[Config]

  implicit val heuristicsRead: scopt.Read[Heuristics.Value] =
    scopt.Read.reads(Heuristics withName _)
  implicit val nondeterminismsRead: scopt.Read[Nondeterminisms.Value] =
    scopt.Read.reads(Nondeterminisms withName _)
  implicit val strategiesRead: scopt.Read[Strategies.Value] =
    scopt.Read.reads(Strategies withName _)
  implicit val booleanRead: scopt.Read[Level]     =
  scopt.Read.reads { _.toLowerCase match {
    case "debug"  => Level.DEBUG
    case "warn"  => Level.WARN
    case "info"  => Level.INFO
    case "error"  => Level.ERROR
    case s       =>
      throw new IllegalArgumentException("'" + s + "' is not a boolean.")
  }}

  var config: Config = null
  var log: List[List[TypeConversion.Event]] = List()
  var strategy = (SelectionStrategies.naive_score _).curried
  var heuristics = Inference.try_heuristics(List(), (Inference.nondeterministic_pairs _))
  var nondeterminismMetric = (Inference.nondeterministic_pairs _)

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
      opt[Strategies.Strategy]('s', "strategy")
        .valueName("strategy")
        .action((x, c) => c.copy(strategy = x))
        .text(s"The preferred strategy to rank state merges ${Nondeterminisms.values}"),
      opt[Nondeterminisms.Nondeterminism]('n', "nondeterminism")
        .valueName("nondeterminism checker")
        .action((x, c) => c.copy(nondeterminism = x))
        .text(s"The preferred definition of nondeterminism - defaults to label, arity, and guard check ${Nondeterminisms.values}"),
      opt[String]('d', "dotfiles")
        .valueName("dir")
        .action((x, c) => c.copy(dotfiles = x))
        .text("The directory in which to save dotfiles produced during the inference process - defaults to 'dotfiles'"),
      opt[Unit]("f1")
        .action((_, c) => c.copy(oneFinal = true))
        .text("Set this flag to merge states with no outgoing transitions"),
      opt[Level]('l', "level")
        .valueName("level")
        .action((x, c) => c.copy(logLevel = x))
        .text(s"The log level {info, debug, warn, error}"),
      arg[File]("filename")
        .required()
        .action((x, c) => c.copy(file = x))
        .text("The json file listing the traces"))
  }

  def parseArgs(args: Array[String]) = {
    OParser.parse(parser1, args, Config()) match {
      case Some(config) => {
        this.config = config
        val rawJson = Source.fromFile(config.file).getLines.mkString
        val parsed = (parse(rawJson))
        val list = parsed.values.asInstanceOf[List[List[Map[String, Any]]]]
        this.log = list.map(run => run.map(x => TypeConversion.toEventTuple(x)))
        val heuristics = scala.collection.immutable.Map(
          Heuristics.store -> Store_Reuse.heuristic_1(log),
          Heuristics.inc -> (Increment_Reset.insert_increment_2 _).curried,
          Heuristics.same -> (Same_Register.same_register _).curried,
          Heuristics.ignore -> (Ignore_Inputs.drop_inputs _).curried,
          Heuristics.ignoret -> (Ignore_Inputs.transitionwise_drop_inputs _).curried,
          Heuristics.ignores -> (Ignore_Inputs.statewise_drop_inputs _).curried)

        val nondeterminisms = scala.collection.immutable.Map(
          Nondeterminisms.basic -> (Inference.nondeterministic_pairs _),
          Nondeterminisms.labar -> (Inference.nondeterministic_pairs_labar _))

        val strategies = scala.collection.immutable.Map(
          Strategies.naive -> (SelectionStrategies.naive_score _).curried,
          Strategies.rank -> (SelectionStrategies.naive_score_outputs _).curried,
          Strategies.comprehensive -> (SelectionStrategies.naive_score_comprehensive _).curried,
          Strategies.comprehensiveEQ -> (SelectionStrategies.naive_score_comprehensive_eq_high _).curried)

          this.strategy = strategies(config.strategy)
        // this.strategy = if (Config.config.oneFinal)
        //     (SelectionStrategies.score_one_final_state _).curried(strategies(config.strategy))
        //   else (strategies(config.strategy))
        this.heuristics = Inference.try_heuristics(config.heuristics.map(x => heuristics(x)).toList, nondeterminisms(config.nondeterminism))
        this.nondeterminismMetric = nondeterminisms(config.nondeterminism)
        }
      case _ =>
        System.exit(1)
      }
  }

}
