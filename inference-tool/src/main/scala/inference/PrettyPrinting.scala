import java.io._
import Types._

object PrettyPrinter {

  def natToString(n: Nat.nat): String = {
    n match {
      case Nat.Nata(m) => m.toString()
    }
  }

  def nataPairToString(nn: (Nat.nat, Nat.nat)): String = {
    (natToString(nn._1), natToString(nn._2)).toString()
  }

  def valueToString(v: Value.value): String =
    v match {
      case Value.Numa(Int.int_of_integer(n)) => n.toString
      case Value.Str(s) => "\"" + s + "\""
    }

  def vnameToString(v: VName.vname): String = {
    v match {
      case VName.I(Nat.Nata(n)) => "i" + n
      case VName.R(Nat.Nata(n)) => "r" + n
    }
  }

  def aexpToString(a: AExp.aexp): String = {
    a match {
      case AExp.L(v) => valueToString(v)
      case AExp.V(v) => vnameToString(v)
      case AExp.Plus(a1, a2) => aexpToString(a1) + " + " + aexpToString(a2)
      case AExp.Minus(a1, a2) => aexpToString(a1) + " - " + aexpToString(a2)
      case AExp.Times(a1, a2) => aexpToString(a1) + " * " + aexpToString(a2)
    }
  }

  def gexpToString(g: GExp.gexp): String = s"(${gexpToString_aux(g)})"

  def gexpToString_aux(g: GExp.gexp): String = g match {
    case GExp.Bc(v) => v.toString()
    case GExp.Eq(a, b) => (aexpToString(a) + "=" + aexpToString(b))
    case GExp.Gt(a, b) => (aexpToString(a) + ">" + aexpToString(b))
    case GExp.Null(v) => (aexpToString(v) + "= NULL")
    case GExp.In(v, l) => s"${vnameToString(v)} E {${l.map(valueToString).mkString(", ")}}"
    case GExp.Nor(g1, g2) => {
      if (g1 == GExp.Bc(true) && g2 == GExp.Bc(true))
        return "false"
      if (g1 == GExp.Bc(false) && g2 == GExp.Bc(false))
        return "true"
      if (g1 == g2)
        return s"! ${gexpToString(g1)}"

      val g1Str = gexpToString(g1)
      val g2Str = gexpToString(g2)

      if (g1Str == "(false)")
        return g2Str

      if (g2Str == "(false)")
        return g1Str

      return s"! (or ${g1Str} ${g2Str})"
    }
  }

  def guardsToString(g: List[GExp.gexp]): String = {
    "[" + g.map(x => gexpToString(x)).mkString(", ") + "]"
  }

  def outputsToString(g: List[AExp.aexp]): String = {
    g.zipWithIndex.map(x => "o" + (x._2 + 1) + ":=" + aexpToString(x._1)).mkString(", ")
  }

  def updatesToString(g: List[(Nat.nat, AExp.aexp)]): String = {
    "[" + g.map(a => (vnameToString(VName.R(a._1)) + ":=" + aexpToString(a._2))).mkString(", ") + "]"
  }

  def transitionToString(t: Transition.transition_ext[Unit]): String = {
    Transition.Label(t) +
      ":" + natToString(Transition.Arity(t)) +
      guardsToString(Transition.Guard(t)) +
      "/" +
      outputsToString(Transition.Outputs(t)) +
      updatesToString(Transition.Updates(t))
  }

  def efsmToStringAux(t: ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])): String = {
    nataPairToString(t._1) + transitionToString(t._2) + "\n"
  }

  def efsmToString(e: TransitionMatrix): String = {
    var string = "{"
    for (move <- TypeConversion.indexWithInts(FSet.sorted_list_of_fset(e)).sortBy(_._1)) {
      string += (s"  ((${move._1._1}, ${move._1._2}), ${transitionToString(move._2)})\n")
    }
    return string + ("}")
  }

  def traceToString(x1: List[(String, (List[Value.value], List[Value.value]))]): String = x1 match {
    case Nil => ""
    case (label, (inputs, outputs)) :: t => s"        ${label}(${inputs.map(valueToString)})/${outputs.map(valueToString)}\n" + traceToString(t)
  }

  def inputsToString(i: List[Value.value], join: String = ", ") = s"[${i.map(valueToString).mkString(join)}]"

  def outputToString(o: Option[Value.value]) = o match {
    case Some(p) => valueToString(p)
    case None => "NONE!!!"
  }

  def optOutputsToString(o: List[Option[Value.value]]) = o.map(outputToString).mkString(", ")
  def litOutputsToString(o: List[Value.value]) = inputsToString(o)

  def pairToString(x: (Nat.nat, ((Nat.nat, Nat.nat), ((Transition.transition_ext[Unit], Nat.nat), (Transition.transition_ext[Unit], Nat.nat))))) = x match {
    case (Nat.Nata(a), ((Nat.Nata(b), Nat.Nata(c)), ((t, Nat.Nata(d)), (t_prime, Nat.Nata(e))))) =>
      (a, ((b, c), ((transitionToString(t), d), (transitionToString(t_prime), e))))
  }

  def nondeterministicPairsToString(p: FSet.fset[(Nat.nat, ((Nat.nat, Nat.nat), ((Transition.transition_ext[Unit], Nat.nat), (Transition.transition_ext[Unit], Nat.nat))))]): String = {
    return FSet.sorted_list_of_fset(p).map(pairToString).mkString(" \n")
  }

  def nondeterministicPairsToString(p: List[(Nat.nat, ((Nat.nat, Nat.nat), ((Transition.transition_ext[Unit], Nat.nat), (Transition.transition_ext[Unit], Nat.nat))))]): String = {
    val better = p.map(pairToString)
    return better.mkString(", \n")
  }

  def iEFSM2dot(eo: Option[IEFSM], f: String) = eo match {
    case Some(e) => {
      val pw = new PrintWriter(new File(f"${Config.config.dotfiles}/${f}.dot"))
      pw.write(EFSM_Dot.iefsm2dot(e))
      pw.close
    }
    case None => println("IEFSM was none!")
  }

  def iEFSM2dot(e: IEFSM, f: String) = {
    val pw = new PrintWriter(new File(f"${Config.config.dotfiles}/${f}.dot"))
    pw.write(EFSM_Dot.iefsm2dot(e))
    pw.close
  }

  def iEFSM2dot(e: IEFSM, f: Nat.nat) = {
    val pw = new PrintWriter(new File(f"${Config.config.dotfiles}/step_${Code_Numeral.integer_of_nat(f)}%03d.dot"))
    pw.write(EFSM_Dot.iefsm2dot(e))
    pw.close
  }

  def iEFSM2dot(e: IEFSM, f: Int) = {
    val pw = new PrintWriter(new File(f"${Config.config.dotfiles}/step_${f}%03d.dot"))
    pw.write(EFSM_Dot.iefsm2dot(e))
    pw.close
  }

  def EFSM2dot(e: TransitionMatrix, f: String) = {
    val pw = new PrintWriter(new File(s"${Config.config.dotfiles}/${f}.dot"))
    pw.write(EFSM_Dot.efsm2dot(e))
    pw.close
  }

  def event2String(e: (String, (List[Value.value], List[Value.value]))): String = e match {
    case (label, (inputs, outputs)) =>
      return label + s"(${inputs.map(i => valueToString(i)).mkString(", ")})" + s"/[${outputs.map(i => valueToString(i)).mkString(", ")}]"
  }

  def releventsToString(l: List[(Nat.nat, (Nat.nat, (String, (List[Value.value], List[Value.value]))))]): String = {
    s"[${
      l.map {
        case (tIndex: Nat.nat, (eIndex: Nat.nat, (label: String, (inputs: List[Value.value], outputs: List[Value.value])))) =>
          (label, (inputsToString(inputs), inputsToString(outputs)))
      }.mkString(", ")
    }]"
  }

  def regsToString(r: Map[Nat.nat, Option[Value.value]]): String = {
    val pairs = r.map {
      case (k: Nat.nat, v: Option[Value.value]) =>
        "r" + natToString(k) + ":=" + (v match {
          case None => throw new IllegalStateException("Got None from registers")
          case Some(Value.Numa(Int.int_of_integer(n))) => n.toString
          case Some(Value.Str(s)) => s
        })
    }
    return s"<${pairs.mkString(", ")}>"
  }

  def eventInfoToString(e: (Nat.nat, (Map[Nat.nat, Option[Value.value]], (List[Value.value], (List[Nat.nat], Transition.transition_ext[Unit]))))): String = e match {
    case (state, (extraRegs, (inputs, (tids, tran)))) => {
      return s"(${natToString(state)}, ${regsToString(extraRegs)}, [${inputsToString(inputs)}], [${tids.map(tid => natToString(tid)).mkString(", ")}], ${transitionToString(tran)})"
    }
  }

  def targetInfoToString(e: (Map[Nat.nat, Option[Value.value]], (Nat.nat, (Map[Nat.nat, Option[Value.value]], (List[Value.value], (List[Nat.nat], Transition.transition_ext[Unit])))))): String = e match {
    case (target, (state, (extraRegs, (inputs, (tids, tran))))) => {
      return s"(${regsToString(target)}, ${natToString(state)}, ${regsToString(extraRegs)}, [${inputsToString(inputs)}], [${tids.map(tid => natToString(tid)).mkString(", ")}], ${transitionToString(tran)})"
    }
  }

  def i_stepToString(s: (List[Nat.nat], (Nat.nat, Transition.transition_ext[Unit]))) = s match {
    case (ids, (s_prime, t)) => ("[" + ids.map(id => natToString(id)).mkString(",") + "]", natToString(s_prime), transitionToString(t))
  }
}
