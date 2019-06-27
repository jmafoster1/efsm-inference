import net.liftweb.json._
import scala.io.Source
import com.microsoft.z3
// PrintWriter
import java.io._
import org.apache.commons.io.FilenameUtils;
import scala.collection.mutable.ListBuffer

object FrontEnd {

  def main(args: Array[String]): Unit = {
    println("=================================================================")

    type Execution = List[(String, (List[Value.value], List[Value.value]))]
    type Log = List[Execution]


    // val filename = "sample-traces/vend1.json"
    val filename = args(0)
    val rawJson = Source.fromFile(filename).getLines.mkString
    val parsed = (parse(rawJson))

    val list = parsed.values.asInstanceOf[List[List[Map[String, Any]]]]

    val log = list.map(run => run.map(x => TypeConversion.toEventTuple(x)))

    var heuristicsToTry = new ListBuffer[Nat.nat => (Nat.nat => (Nat.nat => (FSet.fset[(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))] => (FSet.fset[(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))] => Option[FSet.fset[(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]]))))]();

    if (args contains "-s") {
      heuristicsToTry += (Same_Register.same_register _).curried
    }
    if (args contains "-i") {
      heuristicsToTry += (Increment_Reset.insert_increment_2 _).curried
    }
    if (args contains "-r") {
      heuristicsToTry += Store_Reuse.heuristic_1(log)
    }
    if (args contains "-I") {
      heuristicsToTry += (Ignore_Inputs.drop_inputs _).curried
    }

    val heuristic = Inference.try_heuristics(heuristicsToTry.toList)

    println("Hello inference!")

    // iterative_learn [] naive_score (iterative_try_heuristics [(λx. insert_increment), (λx. heuristic_1 x)])
    val inferred = Inference.learn(log, (SelectionStrategies.naive_score _).curried, heuristic)

    println("The inferred machine is " +
      (if (Inference.nondeterministic(Inference.toiEFSM(inferred))) "non" else "") + "deterministic")

    val basename = FilenameUtils.getBaseName(filename).replace("-", "_")

    println("Goodbye inference!")

    TypeConversion.efsmToSALTranslator(inferred, basename)

    for (move <- TypeConversion.fset_to_list(inferred)) {
      println(PrettyPrinter.transitionToString(move._2))

    }

    println("=================================================================")
  }
}
