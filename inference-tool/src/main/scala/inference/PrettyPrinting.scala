object PrettyPrinter {

  def natToString(n: Nat.nat): String = {
    n match {
      case Nat.Nata(m) => m.toString()
    }
  }

  def nataPairToString(nn: (Nat.nat, Nat.nat)): String = {
    (natToString(Product_Type.fst(nn)), natToString(Product_Type.snd(nn))).toString()
  }

  def valueToString(v: Value.value): String = {
    v match {
      case Value.Numa(Int.int_of_integer(n)) => n.toString()
      case Value.Str(s) => s
    }
  }

  def vnameToString(v: VName.vname): String = {
    v match {
      case VName.I(Nat.Nata(n)) => "i" + (n+1)
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

  def efsmToStringAux(t: ((Nat.nat, Nat.nat),
  Transition.transition_ext[Unit])): String = {
    nataPairToString(Product_Type.fst(t))  +
    transitionToString(Product_Type.snd(t))
  }

  def efsmToString(e: FSet.fset[((Nat.nat, Nat.nat),
  Transition.transition_ext[Unit])]): String = {
    FSet.fimage(efsmToStringAux, e).toString()
  }

  def pp(x: (Nat.nat, ((Nat.nat, Nat.nat), ((Transition.transition_ext[Unit], Nat.nat), (Transition.transition_ext[Unit], Nat.nat))))) : String = x match {
    case (Nat.Nata(from), ((Nat.Nata(to1), Nat.Nata(to2)), ((t1, Nat.Nata(u1)), (t2, Nat.Nata(u2))))) => {
      ((from, (to1, to2), (transitionToString(t1), u1), (transitionToString(t2), u2))).toString()
    }
  }

  // def efsm2dot(e: TypeConversion.TransitionMatrix): String = {
  //   (EFSM_Dot.efsm2dot(e))
  // }
}
