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
  val store, inc, same, ignore = Value
}

object FrontEnd {
  type UpdateModifier = Nat.nat => (Nat.nat => (Nat.nat => (FSet.fset[(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))] => (FSet.fset[(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))] => Option[FSet.fset[(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]]))))

  implicit val heuristicsRead: scopt.Read[Heuristics.Value] =
  scopt.Read.reads(Heuristics withName _)

  def main(args: Array[String]): Unit = {
    case class Config(
      heuristics: Seq[Heuristics.Heuristic] = Seq(),
      file: File = null,
      outputname: String = null
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
          .text("heuristics to give the inference process (store,inc,same,ignore)"),
        opt[String]('o', "output")
          .valueName("filename")
          .action((x, c) => c.copy(outputname = x))
          .text("The preferred name of the file to output the SAL and DOT representations of the inferred model to - defaults to the input file name"),
        arg[File]("filename")
          .required()
          .action((x, c) => c.copy(file = x))
          .text("The json file listing the traces"))
    }

    println("=================================================================")
    OParser.parse(parser1, args, Config()) match {
      case Some(config) =>
        val rawJson = Source.fromFile(config.file).getLines.mkString
        val parsed = (parse(rawJson))
        val list = parsed.values.asInstanceOf[List[List[Map[String, Any]]]]
        val log = list.map(run => run.map(x => TypeConversion.toEventTuple(x)))

        val heuristics = scala.collection.immutable.Map[Heuristics.Heuristic, UpdateModifier](
          Heuristics.store -> Store_Reuse.heuristic_1(log),
          Heuristics.inc -> (Increment_Reset.insert_increment_2 _).curried,
          Heuristics.same -> (Same_Register.same_register _).curried,
          Heuristics.ignore -> (Ignore_Inputs.drop_inputs _).curried
        )

        val inferred = Inference.learn(log, (SelectionStrategies.naive_score_one_final_state _).curried, Inference.try_heuristics(config.heuristics.map(x => heuristics(x)).toList))

        inferred match {
          case None => println("No EFSM could be inferred")
          case Some(inferred) => {
            println("The inferred machine is " +
              (if (Inference.nondeterministic(Inference.toiEFSM(inferred))) "non" else "") + "deterministic")

            val basename = (if (config.outputname == null) (FilenameUtils.getBaseName(config.file.getName()).replace("-", "_")) else config.outputname.replace("-", "_"))

            TypeConversion.efsmToSALTranslator(inferred, basename)
          }
        }

      case _ =>
        System.exit(1)
    }

    println("=================================================================")
  }
}
