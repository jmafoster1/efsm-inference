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
      case Value.Numa(n) => n.toString()
      case Value.Str(s) => String.implode(s)
    }
  }

  def vnameToString(v: VName.vname): String = {
    v match {
      case VName.I(n) => "i"+n
      case VName.R(n) => "r"+n
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

  def transitionToString(t: Transition.transition_ext[Unit]): String = {
    String.implode(Transition.Label(t)) +
    ":" + natToString(Transition.Arity(t))
  }

  def efsmToStringAux(t: ((Nat.nat, Nat.nat),
  Transition.transition_ext[Unit])): String = {
    nataPairToString(Product_Type.fst(t)) +
    transitionToString(Product_Type.snd(t))
  }

  def efsmToString(e: FSet.fset[((Nat.nat, Nat.nat),
  Transition.transition_ext[Unit])]): String = {
    FSet.fimage(efsmToStringAux, e).toString()
  }

  // def efsm2dot(e: TypeConversion.TransitionMatrix): String = {
  //   String.implode(EFSM_Dot.efsm2dot(e))
  // }
}
