import org.slf4j.LoggerFactory
import ch.qos.logback.classic.Level
import ch.qos.logback.classic.Logger

object Log {
  val root =  LoggerFactory.getLogger("root").asInstanceOf[Logger]
  root.setLevel(Config.config.logLevel)

  def logStates(s_1: Nat.nat, s_2: Nat.nat) = {
    root.debug(s"${Code_Numeral.integer_of_nat(s_2)} -> ${Code_Numeral.integer_of_nat(s_1)}")
  }

}
