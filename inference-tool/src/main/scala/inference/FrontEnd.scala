import scala.io.Source
import java.io._
import org.apache.commons.io.FilenameUtils
import scala.collection.mutable.ListBuffer
import Types._

object FrontEnd {
  def main(args: Array[String]): Unit = {

    val t1 = System.nanoTime
    Config.parseArgs(args)

    Log.root.info(args.mkString(" "))
    Log.root.info(s"Building PTA - ${Config.config.log.length} ${if (Config.config.log.length == 1) "trace" else "traces"}")

    var pta: IEFSM = null;

    if (Config.config.abs) {
      pta = Inference.make_pta_abstract(Config.config.log, FSet.bot_fset)
    }
    else {
      pta = Inference.make_pta(Config.config.log, FSet.bot_fset)
    }
    PrettyPrinter.iEFSM2dot(pta, s"pta_gen")

    Config.numStates = Code_Numeral.integer_of_nat(FSet.size_fset(Inference.S(pta)))
    Config.ptaNumStates = Config.numStates

    Log.root.info(s"PTA has ${Config.numStates} states")


    // TODO: Turn this into a switchable option
    val normalised_pta = PTA_Generalisation.normalised_pta(Config.config.log)
    PrettyPrinter.iEFSM2dot(normalised_pta, "normalised")

    val resolved_pta = PTA_Generalisation.derestrict(Config.config.log, Config.heuristics, Config.config.nondeterminismMetric)
    PrettyPrinter.iEFSM2dot(resolved_pta, "resolved")

    pta = resolved_pta
    // </TODO>

    TypeConversion.efsmToSALTranslator(Inference.tm(pta), "pta", false)

    try {
      val inferred = Inference.learn(
        Nat.Nata(Config.config.k),
        pta,
        Config.config.log,
        Config.config.strategy,
        Config.heuristics,
        Config.config.nondeterminismMetric)

        TypeConversion.doubleEFSMToSALTranslator(Inference.tm(pta), "pta", Inference.tm(inferred), "vend1", "compositionTest", false)
        TypeConversion.efsmToSALTranslator(Inference.tm(inferred), "inferred")

        Log.root.info("The inferred machine is " +
          (if (Inference.nondeterministic(inferred, Inference.nondeterministic_pairs)) "non" else "") + "deterministic")

        val basename = (if (Config.config.outputname == null) (FilenameUtils.getBaseName(Config.config.file.getName()).replace("-", "_")) else Config.config.outputname.replace("-", "_"))
        TypeConversion.efsmToSALTranslator(Inference.tm(inferred), basename)

        PrettyPrinter.iEFSM2dot(inferred, s"${basename}_gen")
        val seconds = (System.nanoTime - t1) / 1e9d
        val minutes = (seconds / 60) % 60
        val hours = seconds / 3600
        Log.root.info(s"Completed in ${if (hours > 0) s"${hours.toInt}h " else ""}${if (minutes > 0) s"${minutes.toInt}m " else ""}${seconds % 60}s")
        Log.root.info(s"states: ${FSet.size_fset(Inference.S(inferred))}")
        Log.root.info(s"transitions: ${FSet.size_fset(inferred)}")

        // for (tran <- FSet.sorted_list_of_fset(inferred)) {
        //   println(tran)
        // }

        TypeConversion.efsmToSALTranslator(Inference.tm(inferred), "inferred", false)

    }
    catch {
      case e: Throwable => {
        val sw: StringWriter = new StringWriter()
        e.printStackTrace(new PrintWriter(sw));
        Log.root.error(sw.toString())
      }
    }
  }
}
