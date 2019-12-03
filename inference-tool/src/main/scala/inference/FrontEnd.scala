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
    Config.numStates = Code_Numeral.integer_of_nat(FSet.size_fset(Inference.S(pta)))
    Config.ptaNumStates = Config.numStates

    Log.root.info(s"PTA has ${Config.numStates} states")

    val generalised = PTA_Generalisation.pta_generalise_outputs(Config.config.log)

    PrettyPrinter.iEFSM2dot(generalised, "generalised")
    PrettyPrinter.iEFSM2dot(pta, s"pta_gen")

    val values = Inference.enumerate_log_values(Config.config.log)

    val funs = Dirties.funMap.values.toList
    val updated1 = PTA_Generalisation.put_updates(Config.config.log, values, "coin", Nat.Nata(1), Nat.Nata(1), generalised, List((Nat.Nata(0), Some(funs(0)))), generalised)

    updated1 match {
      case Some(e1) => {
        PrettyPrinter.iEFSM2dot(e1, s"updated1")
        val updated2 = PTA_Generalisation.put_updates(Config.config.log, values, "vend", Nat.Nata(0), Nat.Nata(1), e1, List((Nat.Nata(0), Some(funs(1)))), e1)
        updated2 match {
          case Some(e2) => {
            PrettyPrinter.iEFSM2dot(e2, s"updated2")
            pta = e2
          }
        }
      }
    }

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
