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
    Log.root.info(s"Building PTA - ${Config.config.train.length} ${if (Config.config.train.length == 1) "trace" else "traces"}")

    var pta: IEFSM = Inference.make_pta(Config.config.train)

    PrettyPrinter.iEFSM2dot(pta, s"pta_gen")

    Config.numStates = Code_Numeral.integer_of_nat(FSet.size_fset(Inference.S(pta)))
    Config.ptaNumStates = Config.numStates

    Log.root.info(s"PTA has ${Config.numStates} states")

    if (Config.preprocessor != null) {
      val resolved_pta = Config.preprocessor(pta)(Config.config.train)(Config.heuristics)(Config.config.nondeterminismMetric)
      PrettyPrinter.iEFSM2dot(resolved_pta, "resolved")
      Log.root.info(s"Resolved PTA has ${Code_Numeral.integer_of_nat(FSet.size_fset(Inference.S(pta)))} states")
      pta = resolved_pta
    }

    try {
      val inferred = Inference.learn(
        Nat.Nata(Config.config.k),
        pta,
        Config.config.train,
        Config.config.strategy,
        Config.heuristics,
        Config.config.nondeterminismMetric)

        // TypeConversion.doubleEFSMToSALTranslator(Inference.tm(pta), "pta", Inference.tm(inferred), "vend1", "compositionTest", false)
        // TypeConversion.efsmToSALTranslator(Inference.tm(inferred), "inferred")

        Log.root.info("The inferred machine is " +
          (if (Inference.nondeterministic(inferred, Inference.nondeterministic_pairs)) "non" else "") + "deterministic")

        val basename = (if (Config.config.outputname == null) (FilenameUtils.getBaseName(Config.config.trainFile.getName()).replace("-", "_")) else Config.config.outputname.replace("-", "_"))
        TypeConversion.efsmToSALTranslator(Inference.tm(inferred), basename)

        PrettyPrinter.iEFSM2dot(inferred, s"${basename}_gen")
        val seconds = (System.nanoTime - t1) / 1e9d
        val minutes = (seconds / 60) % 60
        val hours = seconds / 3600
        Log.root.info(s"Completed in ${if (hours > 0) s"${hours.toInt}h " else ""}${if (minutes > 0) s"${minutes.toInt}m " else ""}${seconds % 60}s")
        Log.root.info(s"states: ${Code_Numeral.integer_of_nat(FSet.size_fset(Inference.S(inferred)))}")
        Log.root.info(s"transitions: ${Code_Numeral.integer_of_nat(FSet.size_fset(inferred))}")

        val eval = Inference.test_log(Config.config.test, inferred)
        val eval_json = s"""[\n  ${eval.map{
          case (trace, rejected) => s"""{\n    "trace": [${if (trace.length > 0) "\n      " else ""}${trace.map(event => PrettyPrinter.to_JSON(event)).mkString(",\n      ")}${if (trace.length > 0) "\n    " else ""}],\n    "rejected": [${if (rejected.length > 0) "\n      " else ""}${rejected.map(event => PrettyPrinter.to_JSON(event)).mkString(",\n      ")}${if (rejected.length > 0) "\n    " else ""}]\n  }"""}.mkString(",\n  ")}\n]"""

        val file = new File(Config.config.dotfiles + "/testLog.json")
        val bw = new BufferedWriter(new FileWriter(file))
        bw.write(eval_json)
        bw.close()
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
