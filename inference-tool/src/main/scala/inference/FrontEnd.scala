import scala.io.Source
import java.io._
import org.apache.commons.io.FilenameUtils
import scala.collection.mutable.ListBuffer
import Types._

object FrontEnd {
  def main(args: Array[String]): Unit = {

    val t1 = System.nanoTime
    Config.parseArgs(args)

    if (Config.config.mkdir) {
      Log.root.info("Successfully created directories")
      System.exit(0)
    }

    Log.root.info(args.mkString(" "))
    Log.root.info(s"Building PTA - ${Config.config.train.length} ${if (Config.config.train.length == 1) "trace" else "traces"}")
    PrettyPrinter.iEFSM2dot(Config.config.pta, s"pta_gen")

    if (!EFSM.accepts_log(Set.seta[List[(String, (List[Value.value], List[Value.value]))]](Config.config.train), Inference.tm(Config.config.pta))) {
      Log.root.error("PTA must accept the log.")
      System.exit(1)
    }
    if (Inference.nondeterministic(Config.config.pta, Inference.nondeterministic_pairs)) {
      Log.root.error("PTA must be deterministic.")
      System.exit(1)
    }
    PrettyPrinter.test_model(Config.config.pta, "ptaLog")


    Config.numStates = Code_Numeral.integer_of_nat(FSet.size_fset(Inference.S(Config.config.pta)))
    Config.ptaNumStates = Config.numStates

    Log.root.info(s"PTA has ${Config.numStates} states")
    Log.root.info(s"PTA has ${Code_Numeral.integer_of_nat(FSet.size_fset(Config.config.pta))} transitions")

    if (Config.preprocessor != null) {
      val resolved_pta = Config.preprocessor(Config.config.pta)(Config.config.train)(Config.heuristics)(Config.config.nondeterminismMetric)
      PrettyPrinter.EFSM2dot(Inference.tm(resolved_pta), "resolved")
      if (FSet.equal_fseta(Config.config.pta, resolved_pta)) {
        Log.root.info("Defaulting back to original PTA")
      }
      else {
        Config.config = Config.config.copy(pta = resolved_pta)
        Log.root.info(s"Resolved PTA has ${Code_Numeral.integer_of_nat(FSet.size_fset(Inference.S(Config.config.pta)))} states")
        Log.root.info(s"Resolved PTA has ${Code_Numeral.integer_of_nat(FSet.size_fset(Config.config.pta))} transitions")
      }
      val seconds = (System.nanoTime - t1) / 1e9d
      val minutes = (seconds / 60) % 60
      val hours = seconds / 3600
      Log.root.info(s"Preprocessing completed in ${if (hours > 0) s"${hours.toInt}h " else ""}${if (minutes > 0) s"${minutes.toInt}m " else ""}${seconds % 60}s")
    }

    try {
      var learn = Inference.learn _
      if (Config.config.blueFringe) {
        learn = Blue_Fringe.learn
      }
      var inferred = learn(
        Nat.Nata(Config.config.k),
        Config.config.pta,
        Config.config.train,
        Config.config.strategy,
        Config.heuristics,
        Config.config.nondeterminismMetric)

        if (Config.postprocessor != null) {
          val postprocessed = Config.postprocessor(inferred)(Config.config.train)(Config.heuristics)(Config.config.nondeterminismMetric)
          PrettyPrinter.EFSM2dot(Inference.tm(postprocessed), "postprocessed")
          if (FSet.equal_fseta(inferred, postprocessed)) {
            Log.root.info("Defaulting back to original")
          }
          else {
            inferred = postprocessed
            Log.root.info(s"Postprocessed has ${Code_Numeral.integer_of_nat(FSet.size_fset(Inference.S(postprocessed)))} states")
            Log.root.info(s"Postprocessed PTA has ${Code_Numeral.integer_of_nat(FSet.size_fset(postprocessed))} transitions")
          }
          val sseconds = (System.nanoTime - t1) / 1e9d
          val mminutes = (sseconds / 60) % 60
          val hhours = sseconds / 3600
          Log.root.info(s"Postprocessing completed in ${if (hhours > 0) s"${hhours.toInt}h " else ""}${if (mminutes > 0) s"${mminutes.toInt}m " else ""}${sseconds % 60}s")
        }

      Log.root.info("The inferred machine is " +
        (if (Inference.nondeterministic(inferred, Inference.nondeterministic_pairs)) "non" else "") + "deterministic")

      val basename = (if (Config.config.outputname == null) (FilenameUtils.getBaseName(Config.config.trainFile.getName()).replace("-", "_")) else Config.config.outputname.replace("-", "_"))

      PrettyPrinter.EFSM2dot(Inference.tm(inferred), s"${basename}_gen")
      val seconds = (System.nanoTime - t1) / 1e9d
      val minutes = (seconds / 60) % 60
      val hours = seconds / 3600
      Log.root.info(s"Completed in ${if (hours > 0) s"${hours.toInt}h " else ""}${if (minutes > 0) s"${minutes.toInt}m " else ""}${seconds % 60}s")
      Log.root.info(s"states: ${Code_Numeral.integer_of_nat(FSet.size_fset(Inference.S(inferred)))}")
      Log.root.info(s"transitions: ${Code_Numeral.integer_of_nat(FSet.size_fset(inferred))}")

      val eval = Inference.test_log(Config.config.test, inferred)
      val eval_json = s"""[\n  ${
        eval.map {
          case (trace, rejected) => s"""{\n    "trace": [${if (trace.length > 0) "\n      " else ""}${trace.map(event => PrettyPrinter.to_JSON(event)).mkString(",\n      ")}${if (trace.length > 0) "\n    " else ""}],\n    "rejected": [${if (rejected.length > 0) "\n      " else ""}${rejected.map(event => PrettyPrinter.to_JSON(event)).mkString(",\n      ")}${if (rejected.length > 0) "\n    " else ""}]\n  }"""
        }.mkString(",\n  ")
      }\n]"""

      val file = new File(Config.config.dotfiles + "/testLog.json")
      val bw = new BufferedWriter(new FileWriter(file))
      bw.write(eval_json)
      bw.close()
    } catch {
      case e: Throwable => {
        val sw: StringWriter = new StringWriter()
        e.printStackTrace(new PrintWriter(sw));
        Log.root.error(sw.toString())
      }
    }
  }
}
