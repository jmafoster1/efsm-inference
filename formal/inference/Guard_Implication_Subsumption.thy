theory Guard_Implication_Subsumption
imports Inference
begin

lemma guard_implication:
  "Label t1 = Label t2 \<Longrightarrow>
  Arity t1 = Arity t2 \<Longrightarrow>
  Outputs t1 = Outputs t2 \<Longrightarrow>
  Updates t1 = Updates t2 \<Longrightarrow>
  (\<forall>s. apply_guards (Guard t1) s \<longrightarrow> apply_guards (Guard t2) s) \<Longrightarrow>
  subsumes t2 c t1"
  apply (rule subsumption)
  unfolding can_take_transition_def can_take_def
  using can_take_transition_def can_take_def posterior_def posterior_separate_def can_take_def by auto

definition gexp_implies :: "'a gexp \<Rightarrow> 'a gexp \<Rightarrow> bool" where
  "gexp_implies g1 g2 = (\<forall>s. gval g1 s = true \<longrightarrow> gval g2 s = true)"
declare gexp_implies_def [code del]
code_printing constant gexp_implies \<rightharpoonup> (Scala) "Dirties.gexpImplies"

definition guard_implication_subsumption :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "guard_implication_subsumption t1 t2 = (
    Label t1 = Label t2 \<and>
    Arity t1 = Arity t2 \<and>
    Outputs t1 = Outputs t2 \<and>
    Updates t1 = Updates t2 \<and>
    gexp_implies (fold gAnd (Guard t1) (Bc True)) (fold gAnd (Guard t2) (Bc True))
  )"

lemma guard_implication_subsumption:
  "guard_implication_subsumption t1 t2 \<Longrightarrow> directly_subsumes m1 m2 s1 s2 t2 t1"
  apply (rule subsumes_in_all_contexts_directly_subsumes)
  apply (rule subsumption)
  unfolding guard_implication_subsumption_def can_take_transition_def can_take_def
  using gexp_implies_def apply_guards_fold can_take_transition_def can_take_def
        posterior_def posterior_separate_def can_take_def by auto



end