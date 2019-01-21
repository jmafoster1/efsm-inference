object SelectionStrategies {

def naive_score(t1: FSet.fset[Transition.transition_ext[Unit]],
                 t2: FSet.fset[Transition.transition_ext[Unit]]):
      Nat.nat
  =
  FSet.size_fseta[(Transition.transition_ext[Unit],
                    Transition.transition_ext[Unit])].apply(FSet.ffilter[(Transition.transition_ext[Unit],
                                   Transition.transition_ext[Unit])](((a:
                                 (Transition.transition_ext[Unit],
                                   Transition.transition_ext[Unit]))
                                =>
                               {
                                 val (x, y):
                                       (Transition.transition_ext[Unit],
 Transition.transition_ext[Unit])
                                   = a;
                                 (Lista.equal_list[String.char](Transition.Label[Unit](x),
                         Transition.Label[Unit](y))) && (Nat.equal_nat(Transition.Arity[Unit](x),
                                Transition.Arity[Unit](y)))
                               }),
                              FSet_Utils.fprod[Transition.transition_ext[Unit],
        Transition.transition_ext[Unit]](t1, t2)))

} /* object SelectionStrategies */
