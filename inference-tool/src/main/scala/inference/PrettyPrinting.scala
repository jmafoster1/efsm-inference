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

  def valueToString(v: Value.value): String = {
    v match {
      case Value.Numa(Int.int_of_integer(n)) => n.toString()
      case Value.Str(s) => "\"" + s + "\""
    }
  }

  def vnameToString(v: VName.vname): String = {
    v match {
      case VName.I(Nat.Nata(n)) => "i" + (n + 1)
      case VName.R(Nat.Nata(n)) => "r" + n
    }
  }

  def aexpToString(a: AExp.aexp): String = {
    a match {
      case AExp.L(v) => valueToString(v)
      case AExp.V(v) => vnameToString(v)
      case AExp.Plus(a1, a2) => aexpToString(a1) + " + " + aexpToString(a2)
      case AExp.Minus(a1, a2) => aexpToString(a1) + " - " + aexpToString(a2)
    }
  }

  def gexpToString(g: GExp.gexp): String = g match {
    case GExp.Bc(v) => v.toString()
    case GExp.Eq(a, b) => (aexpToString(a) + "=" + aexpToString(b))
    case GExp.Gt(a, b) => (aexpToString(a) + ">" + aexpToString(b))
    case GExp.Null(v) => (aexpToString(v) + "= NULL")
    case GExp.In(v, l) => s"${vnameToString(v)} E {${l.map(valueToString).mkString(", ")}}"
    case GExp.Nor(g1, g2) => ("!(" + gexpToString(g1) + "||" + gexpToString(g2) + ")")
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

  def aexpToString(a: AExp.aexp, types: Map[VName.vname, Type_Inference.typea]): String = a match {
    case AExp.L(v) => valueToString(v)
    case AExp.V(v) => vnameToString(v) + "::" + types(v)
    case AExp.Plus(a1, a2) => aexpToString(a1, types) + " + " + aexpToString(a2, types)
    case AExp.Minus(a1, a2) => aexpToString(a1, types) + " + " + aexpToString(a2, types)
  }

  def gexpToString(g: GExp.gexp, types: Map[VName.vname, Type_Inference.typea]): String =  g match {
    case GExp.Bc(a) => a.toString()
    case GExp.Eq(a1, a2) => aexpToString(a1, types) + " = " + aexpToString(a2, types)
    case GExp.Gt(a1, a2) => aexpToString(a1, types) + " > " + aexpToString(a2, types)
    case GExp.In(v, l) => s"${vnameToString(v)} E {${l.map(valueToString).mkString(", ")}}"
    case GExp.Nor(g1, g2) => "¬(" + gexpToString(g1, types) + " = " + gexpToString(g2, types) + ")"
    case GExp.Null(v) => null
  }

  def efsmToString(e: TransitionMatrix): String = {
    var string = "{"
    for (move <- TypeConversion.indexWithInts(FSet.sorted_list_of_fset(e)).sortBy(_._1)) {
      string += (s"  ((${move._1._1}, ${move._1._2}), ${PrettyPrinter.transitionToString(move._2)})\n")
    }
    return string + ("}")
  }

  def traceToString(x1: List[(String, (List[Value.value], List[Value.value]))]): String = x1 match {
    case Nil => ""
    case (label, (inputs, outputs))::t => s"        ${label}(${inputs.map(valueToString)})/${outputs.map(valueToString)}\n" + traceToString(t)
  }

  def inputsToString(i: List[Value.value]) = i.map(PrettyPrinter.valueToString).mkString(", ")

  def outputToString(o: Option[Value.value]) = o match {
    case Some(p) => valueToString(p)
  }

  def optOutputsToString(o: List[Option[Value.value]]) = o.map(PrettyPrinter.outputToString).mkString(", ")
  def litOutputsToString(o: List[Value.value]) = inputsToString(o)

  def pairToString(x:(Nat.nat, ((Nat.nat, Nat.nat), ((Transition.transition_ext[Unit], Nat.nat), (Transition.transition_ext[Unit], Nat.nat))))) = x match {
    case (Nat.Nata(a),((Nat.Nata(b),Nat.Nata(c)), ((t,Nat.Nata(d)),(t_prime,Nat.Nata(e))))) =>
    (a,((b, c), ((transitionToString(t), d),(transitionToString(t_prime), e))))
  }

  def nondeterministicPairsToString(p: FSet.fset[(Nat.nat, ((Nat.nat, Nat.nat), ((Transition.transition_ext[Unit], Nat.nat), (Transition.transition_ext[Unit], Nat.nat))))]): String = {
    return FSet.sorted_list_of_fset(p).map(pairToString).mkString(" \n")
  }

  def nondeterministicPairsToString(p: List[(Nat.nat, ((Nat.nat, Nat.nat), ((Transition.transition_ext[Unit], Nat.nat), (Transition.transition_ext[Unit], Nat.nat))))]): String = {
    val better = p.map(pairToString)
    return better.mkString(", \n")
  }

  def iEFSM2dot(e: IEFSM, f: Nat.nat) = {
    val pw = new PrintWriter(new File(f"${Config.config.dotfiles}/step_${Code_Numeral.integer_of_nat(f)}%02d.dot"))
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
}
