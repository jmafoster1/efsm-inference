import net.liftweb.json._
import scala.io.Source
import com.microsoft.z3
// PrintWriter
import java.io._

object FrontEnd {

  def main(args: Array[String]): Unit = {
    println("=================================================================")

    val filename = "sample-traces/vend2.json"
    val rawJson = Source.fromFile(filename).getLines.mkString
    val parsed = (parse(rawJson))

    val list = parsed.values.asInstanceOf[List[List[Map[String, Any]]]]

    val coin = list(0)(0)("inputs").asInstanceOf[List[Any]].map(x => TypeConversion.toValue(x))
    val log = list.map(run => run.map(x => TypeConversion.toEventTuple(x)))

    println("Hello inference!")
    val inferred = (Inference.learn(log, (SelectionStrategies.naive_score _).curried, (Inference.null_generator _).curried, (Inference.null_modifier _).curried))

    // println("The inferred machine is deterministic?"+Inference.nondeterminism(Inference.toiEFSM(inferred)))

    val pw = new PrintWriter(new File("dotfiles/drinks.dot" ))
    pw.write(EFSM_Dot.efsm2dot(inferred))
    pw.close

    println("Goodbye inference!")

    // val ctx = new z3.Context
    // val sort = ctx.mkUninterpretedSort("U")
    // val id = ""
    // println(R(5).toZ3(ctx, sort, id))

    println("=================================================================")
  }
}
