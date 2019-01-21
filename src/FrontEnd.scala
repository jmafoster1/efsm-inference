object FrontEnd {

  def generator(a:FSet.fset[(Nat.nat,((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))] =>
       Nat.nat =>
         (Transition.transition_ext[Unit]) =>
           Nat.nat =>
             (Transition.transition_ext[Unit])):
               Option[Transition.transition_ext[Unit]] = None

  def modifier(a:Transition.transition_ext[Unit] =>
       (Transition.transition_ext[Unit]) =>
         Nat.nat =>
           (FSet.fset[(Nat.nat,
                        ((Nat.nat, Nat.nat),
                          Transition.transition_ext[Unit]))]) =>
             (FSet.fset[(Nat.nat,
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))])):
               Option[(FSet.fset[(Nat.nat,
  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                        (Nat.nat => Nat.nat, Nat.nat => Nat.nat))] = None

  def main(args: Array[String]): Unit = {
    Inference.learn(List(), SelectionStrategies.naive_score, generator, modifier)
  }
}
