import net.liftweb.json._
import scala.io.Source
import com.microsoft.z3
// PrintWriter
import java.io._
import org.apache.commons.io.FilenameUtils;
import scala.collection.mutable.ListBuffer
import scopt.OParser

object Heuristics extends Enumeration {
  type Heuristic = Value
  val store, inc, same, ignore, ignoret = Value
}

object Nondeterminisms extends Enumeration {
  type Nondeterminism = Value
  val basic, labar = Value
}

object FrontEnd {
  implicit val heuristicsRead: scopt.Read[Heuristics.Value] =
    scopt.Read.reads(Heuristics withName _)
  implicit val nondeterminismsRead: scopt.Read[Nondeterminisms.Value] =
    scopt.Read.reads(Nondeterminisms withName _)

  def main(args: Array[String]): Unit = {
    case class Config(
      heuristics: Seq[Heuristics.Heuristic] = Seq(),
      file: File = null,
      outputname: String = null,
      nondeterminism: Nondeterminisms.Nondeterminism = Nondeterminisms.basic
    )

    val builder = OParser.builder[Config]
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
        opt[Nondeterminisms.Nondeterminism]('n', "nondeterminism")
          .valueName("nondeterminism checker")
          .action((x, c) => c.copy(nondeterminism = x))
          .text(s"The preferred definition of nondeterminism - defaults to label, arity, and guard check ${Nondeterminisms.values}"),
        arg[File]("filename")
          .required()
          .action((x, c) => c.copy(file = x))
          .text("The json file listing the traces"))
    }

    println("=================================================================")
    val t1 = System.nanoTime
    OParser.parse(parser1, args, Config()) match {
      case Some(config) =>
        val rawJson = Source.fromFile(config.file).getLines.mkString
        val parsed = (parse(rawJson))
        val list = parsed.values.asInstanceOf[List[List[Map[String, Any]]]]
        val log = list.map(run => run.map(x => TypeConversion.toEventTuple(x)))

        val heuristics = scala.collection.immutable.Map(
          Heuristics.store -> Store_Reuse.heuristic_1(log),
          Heuristics.inc -> (Increment_Reset.insert_increment_2 _).curried,
          Heuristics.same -> (Same_Register.same_register _).curried,
          Heuristics.ignore -> (Ignore_Inputs.drop_inputs _).curried,
          Heuristics.ignoret -> (Ignore_Inputs.transitionwise_drop_inputs _).curried
        )

        val nondeterminisms = scala.collection.immutable.Map(
          Nondeterminisms.basic -> (Inference.nondeterministic_pairs _),
          Nondeterminisms.labar -> (Inference.nondeterministic_pairs_labar _)
        )

        println("Building PTA")
        val pta = Inference.make_pta(log, FSet.bot_fset)
        TypeConversion.efsmToSALTranslator(pta, "pta-old")
        val np_labar = Inference.nondeterministic_pairs_labar(Inference.toiEFSM(pta))
        // println(PrettyPrinter.nondeterministicPairsToString(np_labar))

        val inferred = Inference.learn(
          log,
          (SelectionStrategies.naive_score_rank_one_final_state _).curried,
          Inference.try_heuristics(config.heuristics.map(x => heuristics(x)).toList, nondeterminisms(config.nondeterminism)),
          nondeterminisms(config.nondeterminism))

        inferred match {
          case None => println("No EFSM could be inferred")
          case Some(inferred) => {
            println("The inferred machine is " +
              (if (Inference.nondeterministic(Inference.toiEFSM(inferred), Inference.nondeterministic_pairs)) "non" else "") + "deterministic")
            println(Inference.nondeterministic_pairs(Inference.toiEFSM(inferred)))

            val basename = (if (config.outputname == null) (FilenameUtils.getBaseName(config.file.getName()).replace("-", "_")) else config.outputname.replace("-", "_"))

            TypeConversion.efsmToSALTranslator(inferred, basename)
          }
        }

      case _ =>
        System.exit(1)
    }
    val seconds = (System.nanoTime - t1) / 1e9d
    val minutes = (seconds/60)%60
    val hours = seconds/3600
    println(s"Completed in ${if (hours > 0) s"${hours.toInt}h " else ""}${if (minutes > 0) s"${minutes.toInt}m " else ""}${seconds%60}s")
    println("=================================================================")
  }
}
