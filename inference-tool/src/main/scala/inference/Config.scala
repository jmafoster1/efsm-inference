import scopt.OParser
import java.io._
import scala.io.Source
import net.liftweb.json._
import ch.qos.logback.classic.Level
import Types._
import java.nio.file.{ Paths, Files }

object Heuristics extends Enumeration {
  type Heuristic = Value
  val store, inputgen, inc, distinguish, same, ws, lob = Value
}

object Nondeterminisms extends Enumeration {
  type Nondetermnism = Value
  val basic, labar, labar_d = Value
}

object Strategies extends Enumeration {
  type Strategy = Value
  val naive, naive_eq_bonus, rank, comprehensive, comprehensiveEQ, eq, blueFringe = Value
}

object Preprocessors extends Enumeration {
  type Preprocessor = Value
  val gp, dropGuards, none, ehw = Value
}

case class Config(
  heuristics: Seq[Heuristics.Heuristic] = Seq(),
  prep: Preprocessors.Preprocessor = null,
  post: Preprocessors.Preprocessor = null,
  outputname: String = null,
  dotfiles: String = "dotfiles",
  nondeterminismMetric: IEFSM => FSet.fset[(Nat.nat, ((Nat.nat, Nat.nat), ((Types.Transition, List[Nat.nat]), (Types.Transition, List[Nat.nat]))))] = (Inference.nondeterministic_pairs _),
  strategy: List[Nat.nat] => List[Nat.nat] => IEFSM => Nat.nat = (Blue_Fringe.score_merge_size _).curried,
  skip: Boolean = false,
  logLevel: Level = Level.DEBUG,
  logFile: String = null,
  trainFile: File = null,
  groups: File = null,
  train: List[List[Types.Event]] = List(),
  testFile: File = null,
  test: List[List[Types.Event]] = List(),
  k: Int = 1,
  gpIterations: Int = 50,
  var guardSeed: Int = 0,
  var outputSeed: Int = 0,
  var updateSeed: Int = 0,
  numTraces: Int = 30,
  mkdir: Boolean=false,
  blueFringe: Boolean=false,
  treeRepeats: Int = 2,
  transitionRepeats: Int = 2,
  ngen: Int = 100,
  pta : IEFSM = null
)

object Config {
  val builder = OParser.builder[Config]
  var config: Config = null
  var heuristics = (Inference.null_modifier _).curried
  var numStates: BigInt = 0
  var ptaNumStates: BigInt = 0
  var preprocessor: FSet.fset[(List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))] => (List[List[(String, (List[Value.value], List[Value.value]))]] => ((List[Nat.nat] => (List[Nat.nat] => (Nat.nat => (FSet.fset[(List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))] => (FSet.fset[(List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))] => (FSet.fset[(List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))] => ((FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])] => Boolean) => Option[FSet.fset[(List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]]))))))) => ((FSet.fset[(List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))] => FSet.fset[(Nat.nat, ((Nat.nat, Nat.nat), ((Transition.transition_ext[Unit], List[Nat.nat]), (Transition.transition_ext[Unit], List[Nat.nat]))))]) => FSet.fset[(List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]))) = null
  var postprocessor: FSet.fset[(List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))] => (List[List[(String, (List[Value.value], List[Value.value]))]] => ((List[Nat.nat] => (List[Nat.nat] => (Nat.nat => (FSet.fset[(List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))] => (FSet.fset[(List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))] => (FSet.fset[(List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))] => ((FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])] => Boolean) => Option[FSet.fset[(List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]]))))))) => ((FSet.fset[(List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))] => FSet.fset[(Nat.nat, ((Nat.nat, Nat.nat), ((Transition.transition_ext[Unit], List[Nat.nat]), (Transition.transition_ext[Unit], List[Nat.nat]))))]) => FSet.fset[(List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]))) = null

  implicit val heuristicsRead: scopt.Read[Heuristics.Value] = scopt.Read.reads(Heuristics withName _)
  implicit val proprocessorsRead: scopt.Read[Preprocessors.Value] = scopt.Read.reads(Preprocessors withName _)
  implicit val strategiesRead: scopt.Read[List[Nat.nat] => List[Nat.nat] => IEFSM => Nat.nat] =
    scopt.Read.reads {
      _.toLowerCase match {
        case "eq" => (SelectionStrategies.exactly_equal _).curried
        case "naive" => (SelectionStrategies.naive_score _).curried
        case "bluefringe" => (Blue_Fringe.score_merge_size _).curried
        case "naive_eq_bonus" => (SelectionStrategies.naive_score_eq_bonus _).curried
        case "rank" => (SelectionStrategies.naive_score_outputs _).curried
        case "comprehensive" => (SelectionStrategies.naive_score_comprehensive _).curried
        case "comprehensiveeq" => (SelectionStrategies.naive_score_comprehensive_eq_high _).curried
        case "leaves" => (SelectionStrategies.leaves _).curried
        case s =>
          throw new IllegalArgumentException(s"'${s}' is not a valid strategy ${Strategies.values}")
      }
    }
  implicit val levelRead: scopt.Read[Level] =
    scopt.Read.reads {
      _.toLowerCase match {
        case "debug" => Level.DEBUG
        case "warn" => Level.WARN
        case "info" => Level.INFO
        case "error" => Level.ERROR
        case "off" => Level.OFF
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
      opt[Int]('k', "k")
        .valueName("k")
        .action((x, c) => c.copy(k = x))
        .text("The depth of the k-tails (defaults to zero)"),
      opt[Int]('t', "numTraces")
        .valueName("numTraces")
        .action((x, c) => c.copy(numTraces = x))
        .text("The number of traces in the log to actually use"),
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
      opt[Unit]("blueFringe")
        .action((_, c) => c.copy(blueFringe = true))
        .text("Set this flag to use the blue fringe merging strategy"),
      opt[Unit]("mkdir")
        .action((_, c) => c.copy(mkdir = true))
        .text("Set this flag to skip all inference and just test the making of directories"),
      opt[Preprocessors.Preprocessor]('p', "preprocessor")
        .valueName("preprocessor")
        .action((x, c) => c.copy(prep = x))
        .text(s"Preprocessor to use before inference begins ${Preprocessors.values}"),
      opt[Preprocessors.Preprocessor]('q', "postprocessor")
        .valueName("postprocessor")
        .action((x, c) => c.copy(post = x))
        .text(s"Postprocessor to use after inference has finished ${Preprocessors.values}"),
      opt[Unit]("small")
        .action((_, c) => c.copy(skip = true))
        .text("Set this flag to map integers down to smaller values"),
      opt[Level]('l', "level")
        .valueName("level")
        .action((x, c) => c.copy(logLevel = x))
        .text(s"The log level {info, debug, warn, error}"),
      opt[String]('f', "logFile")
        .valueName("logFile")
        .action((x, c) => c.copy(logFile = x))
        .text(s"The name/location of the logFile"),
      opt[Int]('g', "guardSeed")
        .valueName("Random seed for guard GP")
        .action((x, c) => c.copy(guardSeed = x)),
      opt[Int]("treeRepeats")
        .valueName("Maximum number of times to backtrack up the tree")
        .action((x, c) => c.copy(treeRepeats = x)),
      opt[Int]("ngen")
        .valueName("Number of GP generations")
        .action((x, c) => c.copy(ngen = x)),
      opt[Int]("transitionRepeats")
        .valueName("Maximum number of times to retry inferring output and update functions for a given transition")
        .action((x, c) => c.copy(transitionRepeats = x)),
      opt[Int]('o', "outputSeed")
        .valueName("Random seed for output GP")
        .action((x, c) => c.copy(outputSeed = x)),
      opt[Int]('u', "updateSeed")
        .valueName("Random seed for update GP")
        .action((x, c) => c.copy(updateSeed = x)),
      opt[File]("groups")
        .action((x, c) => c.copy(groups = x))
        .text("The json file listing the transition groups"),
      arg[File]("trainFile")
        .required()
        .action((x, c) => c.copy(trainFile = x))
        .text("The json file listing the training traces"),
      arg[File]("testFile")
        .required()
        .action((x, c) => c.copy(testFile = x))
        .text("The json file listing the test traces"))
  }

  def parseArgs(args: Array[String]) = {
    OParser.parse(parser1, args, Config()) match {
      case Some(configuration) => {
        var config = configuration
        if (config.logFile == null)
          config = config.copy(logFile = config.dotfiles + "/log")
        if (!Files.exists(Paths.get(config.dotfiles)))
          if (!new java.io.File(config.dotfiles).mkdirs)
            throw new IllegalStateException(s"Could not create directory ${config.dotfiles}")
        if (Files.list(Paths.get(config.dotfiles)).findAny().isPresent())
          throw new IllegalArgumentException(s"Dotfiles directory '${config.dotfiles}' is not empty")
        if (Files.exists(Paths.get(config.logFile)))
          throw new IllegalArgumentException(s"Log file '${config.logFile}' already exists")
        if (config.k < 0)
          throw new IllegalArgumentException(s"k must be greater than 0")
        if (config.prep == Preprocessors.ehw && config.groups == null)
          throw new IllegalArgumentException(s"Must provide a groups file to use ehw preprocessing")

        // Set up the logs
        val trainParsed = parse(Source.fromFile(config.trainFile).getLines.mkString).values.asInstanceOf[List[List[Map[String, Any]]]]
        config = config.copy(train = trainParsed.take(config.numTraces).map(run => run.map(x => TypeConversion.toEventTuple(x))))

        val testParsed = parse(Source.fromFile(config.testFile).getLines.mkString).values.asInstanceOf[List[List[Map[String, Any]]]]
        config = config.copy(test = testParsed.map(run => run.map(x => TypeConversion.toEventTuple(x))))

        // MAKE SURE THIS HAPPENS WHEN WE BUILD THE PTA IN THE CODE TOO, SPECIFICALLY IN distinguish
        config = config.copy(pta = Inference.breadth_first_label(Inference.make_pta(config.train)))

        // Set up the heuristics
        val heuristics = scala.collection.immutable.Map(
          Heuristics.store -> (Store_Reuse.heuristic_1 _).curried(config.train),
          Heuristics.inputgen -> (Store_Reuse.heuristic_2 _).curried(config.train),
          Heuristics.inc -> (Increment_Reset.insert_increment_2 _).curried,
          Heuristics.distinguish -> (Distinguishing_Guards.distinguish _).curried(config.pta)(config.train),
          Heuristics.same -> (Same_Register.same_register _).curried,
          Heuristics.ws -> (Weak_Subsumption.weak_subsumption _).curried,
          Heuristics.lob -> (Least_Upper_Bound.lob _).curried
        )

        var transitionGroups: List[((String, (List[PTA_Generalisation.value_type], List[PTA_Generalisation.value_type])),
               List[(List[Nat.nat], Transition.transition_ext[Unit])])] = null

        if (config.groups != null) {
          val parsedGroups = parse(Source.fromFile(config.groups).getLines.mkString).values.asInstanceOf[List[Map[String, Any]]]
          transitionGroups = parsedGroups.map(x =>
            (
              (
                x("label").asInstanceOf[String],
                (
                  x("inputs").asInstanceOf[List[String]].map(i => TypeConversion.value_type(i)),
                  x("outputs").asInstanceOf[List[String]].map(i => TypeConversion.value_type(i)),
                )
              ),
              x("transitions").asInstanceOf[List[List[BigInt]]].map(t =>
                (
                  t.map(n => Code_Numeral.nat_of_integer(n)),
                  Inference.get_by_ids(config.pta, t.map(n => Code_Numeral.nat_of_integer(n)))
                )
              )
            )
          )
         }

        // Set up the preprocessor
        val preprocessors = scala.collection.immutable.Map(
          Preprocessors.ehw -> (PTA_Generalisation.derestrict _).curried(transitionGroups)(Nat.Nata(config.treeRepeats))(Nat.Nata(config.transitionRepeats)),
          Preprocessors.gp -> (PTA_Generalisation.historical_derestrict _).curried(Nat.Nata(config.treeRepeats))(Nat.Nata(config.transitionRepeats)),
          Preprocessors.dropGuards -> (PTA_Generalisation.drop_pta_guards _).curried
        )
        // Set up the postprocessor
        val postprocessors = scala.collection.immutable.Map(
          Preprocessors.gp -> (PTA_Generalisation.historical_derestrict _).curried(Nat.Nata(config.treeRepeats))(Nat.Nata(config.transitionRepeats)),
          Preprocessors.dropGuards -> (PTA_Generalisation.drop_pta_guards _).curried
        )

        this.heuristics = Inference.try_heuristics_check((EFSM.accepts_log _).curried(Set.seta(config.train)), config.heuristics.map(x => heuristics(x)).toList)
        this.config = config
        if (config.prep != null && config.prep != Preprocessors.none)
          this.preprocessor = preprocessors(config.prep)
        if (config.post != null && config.post != Preprocessors.none) {
          this.postprocessor = postprocessors(config.post)
        }

      }
      case _ =>
        System.exit(1)
    }
  }

}
