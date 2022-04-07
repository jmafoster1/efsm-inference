import org.slf4j.LoggerFactory
import ch.qos.logback.classic.Level
import ch.qos.logback.classic.Logger

object Log {
	System.setProperty("log.name", Config.config.logFile);

  val root =  LoggerFactory.getLogger("root").asInstanceOf[Logger]
  root.setLevel(Config.config.logLevel)

  def logStates(e: Types.IEFSM, s_2: Nat.nat) = {
		val s_1 = FSet.size_fset(Inference.S(e))
		Config.numStates = Code_Numeral.integer_of_nat(s_1)
		PrettyPrinter.iEFSM2dot(e, f"${PrettyPrinter.show(s_2)}-${PrettyPrinter.show(s_1)}")
    root.debug(s"${Code_Numeral.integer_of_nat(s_2)} -> ${Code_Numeral.integer_of_nat(s_1)}")
  }

  def logBFStates(e: Types.IEFSM, f: Map[Nat.nat, Blue_Fringe.colour], s_2: Nat.nat) = {
		val s_1 = FSet.size_fset(Inference.S(e))
		Config.numStates = Code_Numeral.integer_of_nat(s_1)
		PrettyPrinter.iefsm2dot_red_blue(e, f, f"${PrettyPrinter.show(s_2)}-${PrettyPrinter.show(s_1)}")
    root.debug(s"${Code_Numeral.integer_of_nat(s_2)} -> ${Code_Numeral.integer_of_nat(s_1)}")
  }

}
