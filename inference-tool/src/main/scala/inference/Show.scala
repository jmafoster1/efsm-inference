abstract class Showable {
  def show: String
}

object ShowImplicits {
  implicit class ValueTypeWithShow(s: PTA_Generalisation.value_type) extends Showable {
    override def show(): String = s match {
      case PTA_Generalisation.I() => "Int"
      case PTA_Generalisation.R() => "Real"
      case PTA_Generalisation.S() => "String"
    }
  }

  implicit class NatWithShow(a: Nat.nat) extends Showable {
    override def show(): String = PrettyPrinter.show(a)
  }

  implicit class VNameWithShow(a: VName.vname) extends Showable {
    override def show(): String = PrettyPrinter.vnameToString(a)
  }

  implicit class ValueWithShow(a: Value.value) extends Showable {
    override def show(): String = PrettyPrinter.show(a)
  }

  implicit class VNameAExpWithShow(a: AExp.aexp[VName.vname]) extends Showable {
    override def show(): String = a match {
      case AExp.L(v) => v.show
      case AExp.V(v) => v.show
      case AExp.Plus(a1, a2) => f"${a1.show} + ${a2.show}"
      case AExp.Minus(a1, a2) => f"${a1.show} - ${a2.show}"
      case AExp.Times(a1, a2) => f"${a1.show} * ${a2.show}"
      case AExp.Divide(a1, a2) => f"${a1.show} / ${a2.show}"
    }
  }

  implicit class ListAExpWithShow(l: List[AExp.aexp[VName.vname]]) extends Showable {
    override def show(): String = "[" + l.map(a => a.show).mkString(", ") + "]"
  }

  implicit class ListNatWithShow(l: List[Nat.nat]) extends Showable {
    override def show(): String = "[" + l.map(a => a.show).mkString(", ") + "]"
  }

  implicit class SetAExpWithShow(s: Set.set[AExp.aexp[VName.vname]]) extends Showable {
    override def show(): String = s match {
      case Set.seta(l) => "[" + l.map(a => a.show).mkString(", ") + "]"
    }
  }

  implicit class FunMemWithShow(l: Map[String, List[(AExp.aexp[VName.vname], Map[VName.vname, PTA_Generalisation.value_type])]]) extends Showable {
    override def show(): String = {
      "{" + l.map { case (label: String, funs: List[(AExp.aexp[VName.vname], Map[VName.vname, PTA_Generalisation.value_type])]) => f"$label: ${funs.map(x => x._1).show})" }.mkString(", ") + "}"
    }
  }

  implicit class ListTGroupWithShow(l: List[(List[Nat.nat], Transition.transition_ext[Unit])]) extends Showable {
    override def show(): String = "[" + l.map(a => a.show).mkString(", ") + "]"
  }

  implicit class TGroupWithShow(l: (List[Nat.nat], Transition.transition_ext[Unit])) extends Showable {
    override def show(): String = "(" + l._1.show + ", " + l._2.show + ")"
  }

  implicit class TransitionWithShow(t: Transition.transition_ext[Unit]) extends Showable {
    override def show(): String = PrettyPrinter.show(t)
  }

  implicit class BadMemWithShow(l: Map[List[Nat.nat], List[AExp.aexp[VName.vname]]]) extends Showable {
    override def show(): String = {
      "{" + l.map(x => f"${x._1.show}: ${x._2.show}") + "}"
    }
  }

  implicit class ValueListWithShow(l: List[Value.value]) extends Showable {
    override def show(): String = "[" + l.map(a => a.show).mkString(", ") + "]"
  }

  implicit class TrainingSetWithShow(l: List[(List[Value.value], (Map[Nat.nat,Option[Value.value]], (Value.value, List[Nat.nat])))]) extends Showable {
    override def show(): String = "  " + l.map(a => a.show).mkString("\n  ")
  }

  implicit class TrainingSetRowWithShow(l: (List[Value.value], (Map[Nat.nat,Option[Value.value]], (Value.value, List[Nat.nat])))) extends Showable {
    override def show(): String = f"(${l._1.show}, ${l._2.show})"
  }

  implicit class TrainingSetDetailsWithShow(l: (Map[Nat.nat,Option[Value.value]], (Value.value, List[Nat.nat]))) extends Showable {
    override def show(): String = f"(${l._1.show}, ${l._2.show})"
  }

  implicit class TrainingSetDetails1WithShow(l: Map[Nat.nat,Option[Value.value]]) extends Showable {
      override def show(): String = PrettyPrinter.show(l)
  }

  implicit class TrainingSetDetails2WithShow(l: (Value.value, List[Nat.nat])) extends Showable {
    override def show(): String = f"(${l._1.show}, ${l._2.show})"
  }



  // implicit class AnyWithShow(l: Any) extends Showable {
  //   def show(): String = l.toString
  // }
  //
  // implicit class ListWithShow(l: List[Any]) extends Showable {
  //   override def show(): String = "[" + l.map(a => a.show).mkString(", ") + "]"
  // }
  //
  // implicit class MapWithShow(l: Map[Any, Any]) extends Showable {
  //   override def show(): String = "{" + l.map(a => f"${a._1.show}: ${a._2.show}").mkString(", ") + "}"
  // }
  //
  // implicit class SetWithShow(s: Set.set[Any]) extends Showable {
  //   override def show(): String = s match {
  //     case Set.seta(l) => "{" + l.map(a => a.show).mkString(", ") + "}"
  //   }
  // }
}
