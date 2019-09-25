import scala.io.Source
import com.microsoft.z3
// PrintWriter
import java.io._
import org.apache.commons.io.FilenameUtils
import scala.collection.mutable.ListBuffer
import Types._

object FrontEnd {
  def main(args: Array[String]): Unit = {
    // implicit def `Int.equal`: HOL.equal[Int] = new HOL.equal[Int] {
    //   val `HOL.equal` = (a: Int, b: Int) => a == b
    // }
    // implicit def `Int.ord_nat`: Orderings.linorder[Int] = new Orderings.linorder[Int] {
    //   val `Orderings.less_eq` = (a: Int, b: Int) => a < b
    //   val `Orderings.less` = (a: Int, b: Int) => a <= b
    // }
    //
    // println(FSet.sorted_list_of_fset(FSet.fset_of_list((1 to 476349).reverse.toList)))
    // println(List(1, 2, 3, 2, 5, 4, 5, 5, 10).sortWith((Orderings.less)))


    val t1 = System.nanoTime
    Config.parseArgs(args)

    Log.root.info(args.mkString(" "))
    Log.root.info(s"Building PTA - ${Config.log.length} ${if (Config.log.length == 1) "trace" else "traces"}")

    if (Config.config.smallInts) {
      Config.log = Use_Small_Numbers.use_smallest_ints(Config.log)
    }

    var pta: TransitionMatrix = null;

    if (Config.config.abs) {
      pta = Inference.make_pta_abstract(Config.log, FSet.bot_fset)
    }
    else {
      pta = Inference.make_pta(Config.log, FSet.bot_fset)
    }
    PrettyPrinter.EFSM2dot(pta, s"pta_gen")

    try {
      val inferred = Inference.learn(
        Nat.Nata(Config.config.k),
        pta,
        Config.log,
        Config.config.strategy,
        Config.heuristics,
        Config.config.nondeterminismMetric)

        // TypeConversion.doubleEFSMToSALTranslator(pta, "pta", inferred, "vend1", "compositionTest")

        Log.root.info("The inferred machine is " +
          (if (Inference.nondeterministic(Inference.toiEFSM(inferred), Inference.nondeterministic_pairs)) "non" else "") + "deterministic")

        val basename = (if (Config.config.outputname == null) (FilenameUtils.getBaseName(Config.config.file.getName()).replace("-", "_")) else Config.config.outputname.replace("-", "_"))
        TypeConversion.efsmToSALTranslator(inferred, basename)

        PrettyPrinter.EFSM2dot(inferred, s"${basename}_gen")
        val seconds = (System.nanoTime - t1) / 1e9d
        val minutes = (seconds / 60) % 60
        val hours = seconds / 3600
        Log.root.info(s"Completed in ${if (hours > 0) s"${hours.toInt}h " else ""}${if (minutes > 0) s"${minutes.toInt}m " else ""}${seconds % 60}s")
        Log.root.info(s"states: ${FSet.size_fset(EFSM.S(inferred))}")
        Log.root.info(s"transitions: ${FSet.size_fset(inferred)}")
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
