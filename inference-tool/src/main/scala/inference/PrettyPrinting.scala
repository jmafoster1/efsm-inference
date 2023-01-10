import java.io._
import Types._

object PrettyPrinter {

  def show(n: Nat.nat): String = {
    n match {
      case Nat.Nata(m) => m.toString()
    }
  }

  def show(r: Real.real): String = {
    TypeConversion.toDouble(r).toString
  }

  def nataPairToString(nn: (Nat.nat, Nat.nat)): String = {
    (show(nn._1), show(nn._2)).toString()
  }

  def show(id: List[Nat.nat], t: Transition.transition_ext[Unit]): String = {
    show(id)+show(t)
  }

  def show(s: Inference.score_ext[Unit]): String = {
    f"(${Inference.S1(s)}, ${Inference.S2(s)}) -> ${Inference.Score(s)}"
  }

  def show(s: Set.set[AExp.aexp[VName.vname]]): String = s match {
    case Set.seta(l) => f"{${l.map(x => show(x)).mkString(", ")}}"
  }

  def show(v: Value.value): String =
    v match {
      case Value.Inta(Int.int_of_integer(n)) => n.toString
      case Value.Reala(Real.Ratreal(rat)) => TypeConversion.toDouble(rat).toString
      case Value.Str(s) => "\"" + s + "\""
    }

  def vnameToString(v: VName.vname): String = {
    v match {
      case VName.I(Nat.Nata(n)) => "i" + n
      case VName.R(Nat.Nata(n)) => "r" + n
    }
  }

  def show(a: AExp.aexp[VName.vname]): String = {
    a match {
      case AExp.L(v) => show(v)
      case AExp.V(v) => vnameToString(v)
      case AExp.Plus(a1, a2) => show(a1) + " + " + show(a2)
      case AExp.Minus(a1, a2) => show(a1) + " - " + show(a2)
      case AExp.Times(a1, a2) => show(a1) + " * " + show(a2)
      case AExp.Divide(a1, a2) => show(a1) + " / " + show(a2)
    }
  }

  def show(g: GExp.gexp[VName.vname]): String = g match {
    case GExp.Bc(v) => v.toString()
    case GExp.Eq(a, b) => s"(= ${show(a)} ${show(b)})"
    case GExp.Gt(a, b) => s"(> ${show(a)} ${show(b)})"
    case GExp.In(v, l) => s"${vnameToString(v)} E {${l.map(show).mkString(", ")}}"
    case GExp.Nor(g1, g2) => {
      if (g1 == g2)
        return s"(not ${show (g1)})"
      else
        return s"(not (or ${show(g1)} ${show(g2)}))"
    }
  }

  def guardsToString(g: List[GExp.gexp[VName.vname]]): String = {
    "[" + g.map(x => show(x)).mkString(", ") + "]"
  }

  def outputsToString(g: List[AExp.aexp[VName.vname]]): String = {
    g.zipWithIndex.map(x => "o" + (x._2) + ":=" + show(x._1)).mkString(", ")
  }

  def updatesToString(g: List[(Nat.nat, AExp.aexp[VName.vname])]): String = {
    "[" + g.map(a => (vnameToString(VName.R(a._1)) + ":=" + show(a._2))).mkString(", ") + "]"
  }

  def show(t: Transition.transition_ext[Unit]): String = {
    Transition.Label(t) +
      ":" + show(Transition.Arity(t)) +
      guardsToString(Transition.Guards(t)) +
      "/" +
      outputsToString(Transition.Outputs(t)) +
      updatesToString(Transition.Updates(t))
  }

  def show(event: (Nat.nat, (Map[Nat.nat,Option[Value.value]], (Map[Nat.nat,Option[Value.value]], (List[Value.value], (List[Nat.nat], Transition.transition_ext[Unit])))))): String = event match {
    case (s, (oldRegs, (newRegs, (inputs, (id, t))))) => s"(${show(s)}, ${show(oldRegs)}, ${show(newRegs)}, ${show(inputs)}, ${show(id)}, ${show(t)})"
  }

  def efsmToStringAux(t: ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])): String = {
    nataPairToString(t._1) + show(t._2) + "\n"
  }

  def efsmToString(e: TransitionMatrix): String = {
    var string = "{"
    for (move <- TypeConversion.indexWithInts(FSet.sorted_list_of_fset(e)).sortBy(_._1)) {
      string += (s"  ((${move._1._1}, ${move._1._2}), ${show(move._2)})\n")
    }
    return string + ("}")
  }

  def traceToString(x1: List[(String, (List[Value.value], List[Value.value]))]): String = x1 match {
    case Nil => ""
    case (label, (inputs, outputs)) :: t => s"        ${label}(${inputs.map(show)})/${outputs.map(show)}\n" + traceToString(t)
  }

  def show(i: List[Value.value], join: String = ", "): String = s"[${i.map(show).mkString(join)}]"

  def outputToString(o: Option[Value.value]): String = o match {
    case Some(p) => show(p)
    case None => "NONE!!!"
  }

  def show[X: ClassManifest](o: List[Option[Value.value]]) = s"""[${o.map(outputToString).mkString(", ")}]"""

  def pairToString(x: (Nat.nat, ((Nat.nat, Nat.nat), ((Transition.transition_ext[Unit], Nat.nat), (Transition.transition_ext[Unit], Nat.nat))))) = x match {
    case (Nat.Nata(a), ((Nat.Nata(b), Nat.Nata(c)), ((t, Nat.Nata(d)), (t_prime, Nat.Nata(e))))) =>
      (a, ((b, c), ((show(t), d), (show(t_prime), e))))
  }

  def nondeterministicPairsToString(p: FSet.fset[(Nat.nat, ((Nat.nat, Nat.nat), ((Transition.transition_ext[Unit], Nat.nat), (Transition.transition_ext[Unit], Nat.nat))))]): String = {
    return FSet.sorted_list_of_fset(p).map(pairToString).mkString(" \n")
  }

  def nondeterministicPairsToString(p: List[(Nat.nat, ((Nat.nat, Nat.nat), ((Transition.transition_ext[Unit], Nat.nat), (Transition.transition_ext[Unit], Nat.nat))))]): String = {
    val better = p.map(pairToString)
    return better.mkString(", \n")
  }

  def test_model(model: IEFSM, filename: String) = {
    val eval = Inference.test_log(Config.config.test, model)
    val eval_json = s"""[\n  ${
      eval.map {
        case (trace, rejected) => s"""{\n    "trace": [${if (trace.length > 0) "\n      " else ""}${trace.map(event => PrettyPrinter.to_JSON(event)).mkString(",\n      ")}${if (trace.length > 0) "\n    " else ""}],\n    "rejected": [${if (rejected.length > 0) "\n      " else ""}${rejected.map(event => PrettyPrinter.to_JSON(event)).mkString(",\n      ")}${if (rejected.length > 0) "\n    " else ""}]\n  }"""
      }.mkString(",\n  ")
    }\n]"""

    val file = new File(f"${Config.config.dotfiles}/$filename.json")
    val bw = new BufferedWriter(new FileWriter(file))
    bw.write(eval_json)
    bw.close()
  }

  def iEFSM2dot(eo: Option[IEFSM], f: String) = eo match {
    case Some(e) => {
      val pw = new PrintWriter(new File(f"${Config.config.dotfiles}/${f}.dot"))
      pw.write(EFSM_Dot.iefsm2dot(e))
      pw.close
    }
    case None => println("IEFSM was none!")
  }

  def show(c: Blue_Fringe.colour) = Blue_Fringe.show_colour(c)

  def iefsm2dot_red_blue(e: IEFSM, fun: Map[Nat.nat, Blue_Fringe.colour], f: String) = {
    val pw = new PrintWriter(new File(f"${Config.config.dotfiles}/${f}.dot"))
    pw.write(Blue_Fringe.iefsm2dot_red_blue(e, fun))
    pw.close
  }

  def iEFSM2dot(e: IEFSM, f: String) = {
    val pw = new PrintWriter(new File(f"${Config.config.dotfiles}/${f}.dot"))
    pw.write(EFSM_Dot.iefsm2dot(e))
    pw.close
  }

  def runinfo2dot(e: IEFSM, run_info: List[(Map[Nat.nat, Option[Value.value]], (Nat.nat, (Map[Nat.nat, Option[Value.value]], (Map[Nat.nat, Option[Value.value]], (List[Value.value], (List[Nat.nat], Transition.transition_ext[Unit]))))))], f: String) = {
    val pw = new PrintWriter(new File(f"${Config.config.dotfiles}/${f}.dot"))
    pw.write(Run_Info_DOT.runinfo2dot(e, run_info))
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
      return label + s"(${inputs.map(i => show(i)).mkString(", ")})" + s"/[${outputs.map(i => show(i)).mkString(", ")}]"
  }

  def releventsToString(l: List[(Nat.nat, (Nat.nat, (String, (List[Value.value], List[Value.value]))))]): String = {
    s"[${
      l.map {
        case (tIndex: Nat.nat, (eIndex: Nat.nat, (label: String, (inputs: List[Value.value], outputs: List[Value.value])))) =>
          (label, (show(inputs), show(outputs)))
      }.mkString(", ")
    }]"
  }

  def show(ns: List[Nat.nat]): String =
    s"[${ns.map(n => show(n)).mkString(", ")}]"

  def show(r: Map[Nat.nat, Option[Value.value]]): String = {
    val pairs = r.map {
      case (k: Nat.nat, v: Option[Value.value]) =>
        "r" + show(k) + ":=" + (v match {
          case None => return "None"
          case Some(Value.Inta(Int.int_of_integer(n))) => n.toString
          case Some(Value.Str(s)) => s
          case Some(Value.Reala(d)) => TypeConversion.toDouble(d).toString
        })
    }
    return s"<${pairs.mkString(", ")}>"
  }

  def dot(r: Map[Nat.nat, Option[Value.value]]): String = {
    val pairs = r.map {
      case (k: Nat.nat, v: Option[Value.value]) =>
        "r" + show(k) + ":=" + (v match {
          case None => return "None"
          case Some(Value.Inta(Int.int_of_integer(n))) => n.toString
          case Some(Value.Str(s)) => s
          case Some(Value.Reala(d)) => TypeConversion.toDouble(d).toString
        })
    }
    return s"{${pairs.mkString(", ")}}"
  }

  def eventInfoToString(e: (Nat.nat, (Map[Nat.nat, Option[Value.value]], (List[Value.value], (List[Nat.nat], Transition.transition_ext[Unit]))))): String = e match {
    case (state, (extraRegs, (inputs, (tids, tran)))) => {
      return s"(${show(state)}, ${show(extraRegs)}, [${show(inputs)}], [${tids.map(tid => show(tid)).mkString(", ")}], ${show(tran)})"
    }
  }

  def targetInfoToString(e: (Map[Nat.nat, Option[Value.value]], (Nat.nat, (Map[Nat.nat, Option[Value.value]], (Map[Nat.nat, Option[Value.value]], (List[Value.value], (List[Nat.nat], Transition.transition_ext[Unit]))))))): String = e match {
    case (target, (state, (oldRegs, (extraRegs, (inputs, (tids, tran)))))) => {
      return s"(${show(state)}, ${show(oldRegs)}, ${show(extraRegs)}, ${show(target)}, [${show(inputs)}], [${tids.map(tid => show(tid)).mkString(", ")}], ${show(tran)})"
    }
  }

  def show(t: Option[Transition.transition_ext[Unit]]): String = t match {
    case None => "None"
    case Some(t) => show(t)
  }

  def i_stepToString(s: (List[Nat.nat], (Nat.nat, Transition.transition_ext[Unit]))) = s match {
    case (ids, (s_prime, t)) => ("[" + ids.map(id => show(id)).mkString(",") + "]", show(s_prime), show(t))
  }

  def to_JSON(r: Map[Nat.nat, Option[Value.value]]): String = {
    val pairs = r.map {
      case (k: Nat.nat, v: Option[Value.value]) =>
        s""""r${show(k)}":""" + (v match {
          case None => "null"
          case Some(Value.Inta(Int.int_of_integer(n))) => n.toString
          case Some(Value.Reala(d)) => TypeConversion.toDouble(d).toString
          case Some(Value.Str(s)) => s""""$s""""
        })
    }
    return s"{${pairs.mkString(", ")}}"
  }

  def to_JSON(e: (String, (List[Value.value], (Nat.nat, (Nat.nat, (Map[Nat.nat,Option[Value.value]], (List[Nat.nat], (List[Value.value], List[Option[Value.value]])))))))): String = e match {
    case (label, (inputs, (currentState, (nextState, (regs, (tids, (expected, actual))))))) => s"""{"label": "$label", "inputs": ${show(inputs)}, "currentState": ${show(currentState)}, "nextState": ${show(nextState)}, "regs": ${to_JSON(regs)}, "transition": ${show(tids)}, "expected": ${show(expected)}, "actual": ${show(actual)}}"""
  }

  def to_JSON[X: ClassManifest](e: (String, (List[Value.value], List[Value.value]))): String = e match {
    case (label, (inputs, outputs)) => s"""{"label": "$label", "inputs": ${show(inputs)}, "outputs": ${show(outputs)}}"""
  }

  def stringify(x: Object): String = x match {
    case x: Transition.transition_ext[Unit] => show(x)
    case ((s1: Nat.nat, s2: Nat.nat), t: Transition.transition_ext[Unit]) => ((show(s1), show(s2)), show(t)).toString
    case (id: List[Nat.nat], ((s1: Nat.nat, s2: Nat.nat), t: Transition.transition_ext[Unit])) => "  " + ((show(s1), show(s2)), show(t)) + "\n"
    case _ => x.toString
  }

  def print(x: Object): Unit = x match {
    case t: Transition.transition_ext[Unit] => println(show(t))
    case FSet.fset_of_list(l) => print(l.distinct)
    case l: List[_] => println(l.asInstanceOf[List[Object]].map(x => stringify(x)))
    case _ => println(x)
  }
}
