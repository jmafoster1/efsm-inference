import scala.io.Source
import com.microsoft.z3
// PrintWriter
import java.io._
import org.apache.commons.io.FilenameUtils;
import scala.collection.mutable.ListBuffer

object FrontEnd {
  def main(args: Array[String]): Unit = {

    val t1 = System.nanoTime
    Config.parseArgs(args)

    Log.root.info("Building PTA")
    val pta = Inference.make_pta(Config.log, FSet.bot_fset)
    TypeConversion.efsmToSALTranslator(pta, "pta")
    PrettyPrinter.EFSM2dot(pta, s"pta_gen")

    val inferred = Inference.learn(
      Nat.Nata(Config.config.k),
      Config.log,
      Config.config.strategy,
      Config.heuristics,
      Config.config.nondeterminismMetric)

    // val lst = FSet.sorted_list_of_fset(inferred)
    // val t = lst(0)._2
    // println(Dirties.canTake(Inference.toiEFSM(inferred), Nat.Nata(0), t))

    TypeConversion.doubleEFSMToSALTranslator(pta, "pta", inferred, "vend1", "compositionTest")

    Log.root.info("The inferred machine is " +
      (if (Inference.nondeterministic(Inference.toiEFSM(inferred), Inference.nondeterministic_pairs)) "non" else "") + "deterministic")

    val basename = (if (Config.config.outputname == null) (FilenameUtils.getBaseName(Config.config.file.getName()).replace("-", "_")) else Config.config.outputname.replace("-", "_"))
    TypeConversion.efsmToSALTranslator(inferred, basename)

    PrettyPrinter.EFSM2dot(inferred, s"${basename}_gen")
    val seconds = (System.nanoTime - t1) / 1e9d
    val minutes = (seconds / 60) % 60
    val hours = seconds / 3600
    Log.root.info(s"Completed in ${if (hours > 0) s"${hours.toInt}h " else ""}${if (minutes > 0) s"${minutes.toInt}m " else ""}${seconds % 60}s")
  }
}
