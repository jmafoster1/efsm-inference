theory Transition_Ordering
  imports "../EFSM/Transition"
    GExp_Orderings
    "HOL-Library.Product_Lexorder"
begin

instantiation "transition_ext" :: (linorder) linorder begin

definition less_transition_ext :: "'a::linorder transition_scheme \<Rightarrow> 'a transition_scheme \<Rightarrow> bool" where
"less_transition_ext t1 t2 = ((Label t1, Arity t1, Guard t1, Outputs t1, Updates t1, more t1) < (Label t2, Arity t2, Guard t2, Outputs t2, Updates t2, more t2))"

definition less_eq_transition_ext :: "'a::linorder transition_scheme \<Rightarrow> 'a transition_scheme \<Rightarrow> bool" where
"less_eq_transition_ext t1 t2 = (t1 < t2 \<or> t1 = t2)"

instance
  apply standard
  unfolding less_eq_transition_ext_def less_transition_ext_def
      apply auto[1]
     apply simp
  using less_trans apply blast
  using less_imp_not_less apply blast
  by (metis Pair_inject equality neqE)
end
end