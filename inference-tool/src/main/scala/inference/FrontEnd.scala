import net.liftweb.json._
import scala.io.Source
import native.R
import com.microsoft.z3


object FrontEnd {

  def main(args: Array[String]): Unit = {
    println("=================================================================")

    val filename = "sample-traces/vend1.json"
    val rawJson = Source.fromFile(filename).getLines.mkString
    val parsed = (parse(rawJson))

    val list = parsed.values.asInstanceOf[List[List[Map[String, Any]]]]

    val coin = list(0)(0)("inputs").asInstanceOf[List[Any]].map(x => TypeConversion.toValue(x))
    val log = list.map(run => run.map(x => TypeConversion.toEventTuple(x)))

    println("Hello inference!")
    println((Inference.learn(log, (SelectionStrategies.naive_score _).curried, (Inference.null_generator _).curried, (Inference.null_modifier _).curried)))
    println("Goodbye inference!")

    val ctx = new z3.Context
    val sort = ctx.mkUninterpretedSort("U")
    val id = ""
    println(R(5).toZ3(ctx, sort, id))

    println("=================================================================")
  }
}
