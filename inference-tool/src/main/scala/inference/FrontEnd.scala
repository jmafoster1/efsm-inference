import net.liftweb.json._
import scala.io.Source
import com.microsoft.z3
// PrintWriter
import java.io._

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

    val coin = list(0)(0)("inputs").asInstanceOf[List[Any]].map(x => TypeConversion.toValue(x))
    val log = list.map(run => run.map(x => TypeConversion.toEventTuple(x)))

    val heuristic = (l:Log) => Code_Generation.iterative_try_heuristics_print(List(
      (x:Log) => (Same_Register.same_register _).curried,
      (x:Log) => (Increment_Reset.insert_increment _).curried,
      (x:Log) => Trace_Matches.heuristic_1(x)
    ), l)

    println("Hello inference!")
    // iterative_learn [] naive_score (iterative_try_heuristics [(λx. insert_increment), (λx. heuristic_1 x)])
    val inferred = (Inference.iterative_learn(log, (SelectionStrategies.naive_score _).curried, heuristic))

    println("The inferred machine is "+(if (Inference.nondeterministic(Inference.toiEFSM(inferred))) "non" else "")+"deterministic")

    val pw = new PrintWriter(new File("dotfiles/vend1.dot" ))
    pw.write(EFSM_Dot.efsm2dot(inferred))
    pw.close

    println("Goodbye inference!")

    TypeConversion.efsmToSALTranslator(inferred)

    // val ctx = new z3.Context
    // val sort = ctx.mkUninterpretedSort("U")
    // val id = ""
    // println(R(5).toZ3(ctx, sort, id))

    println("=================================================================")
  }
}
