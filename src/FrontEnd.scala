object FrontEnd {

  // def null_modifier(a: Transition.transition_ext[Unit])
  //                  (b: Transition.transition_ext[Unit])
  //                  (c: Nat.nat)
  //                  (d: FSet.fset[(Nat.nat,
  //                                   ((Nat.nat, Nat.nat),
  //                                     Transition.transition_ext[Unit]))])
  //                  (e: FSet.fset[(Nat.nat,
  //                                   ((Nat.nat, Nat.nat),
  //                                     Transition.transition_ext[Unit]))]):
  //       Option[(FSet.fset[(Nat.nat,
  //                           ((Nat.nat, Nat.nat),
  //                             Transition.transition_ext[Unit]))],
  //                (Nat.nat => Nat.nat, Nat.nat => Nat.nat))]
  //   =
  //   None

  def main(args: Array[String]): Unit = {
    println("Hello inference!")
    println(Inference.learn(List(), (SelectionStrategies.naive_score _).curried, (Inference.null_generator _).curried, (Inference.null_modifier _).curried))
    println("Goodbye inference!")
  }
}
