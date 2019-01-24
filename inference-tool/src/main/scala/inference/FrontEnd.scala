import net.liftweb.json._
import scala.io.Source

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
    println(PrettyPrinter.efsm2dot(Inference.learn(log, (SelectionStrategies.naive_score _).curried, (Inference.null_generator _).curried, (Inference.null_modifier _).curried)))
    println("Goodbye inference!")

    println("=================================================================")
  }
}
