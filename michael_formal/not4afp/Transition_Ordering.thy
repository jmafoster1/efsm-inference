theory Transition_Ordering
imports "../Transition" GExp_Orderings
begin

definition updates2gexps :: "update_function list \<Rightarrow> gexp list" where
"updates2gexps = map (\<lambda>u. (Eq (V (fst u)) (snd u)))"

lemma injective_updates2gexps: "inj updates2gexps"
  apply (simp add: updates2gexps_def)
  by (simp add: inj_def)

lemma updates2gexps_determinism: "(updates2gexps x = updates2gexps y) = (x = y)"
proof
  show "updates2gexps x = updates2gexps y \<Longrightarrow> x = y"
    by (meson injD injective_updates2gexps)
next
  show "x = y \<Longrightarrow> updates2gexps x = updates2gexps y"
    by simp
qed

instantiation "transition_ext" :: (linorder) linorder begin
definition less_eq_transition_ext :: "'a::linorder transition_scheme \<Rightarrow> 'a transition_scheme \<Rightarrow> bool" where
"less_eq_transition_ext t1 t2 = (if Label t1 = Label t2 then
                                   (if Arity t1 = Arity t2 then
                                      (if (conjoin (Guard t1)) = (conjoin (Guard t2)) then
                                         (if (sum (Outputs t1)) = (sum (Outputs t2)) then
                                            (if conjoin (updates2gexps (Updates t1)) = conjoin (updates2gexps (Updates t2)) then
                                               less_eq (more t1) (more t2)
                                           else conjoin (updates2gexps (Updates t1)) < conjoin (updates2gexps (Updates t2)))
                                         else (sum (Outputs t1)) < (sum (Outputs t2)))
                                       else (conjoin (Guard t1)) < (conjoin (Guard t2)))
                                    else (Arity t1) < (Arity t2))
                                 else Label t1 < Label t2)"

definition less_transition_ext :: "'a::linorder transition_scheme \<Rightarrow> 'a transition_scheme \<Rightarrow> bool" where
"less_transition_ext t1 t2 = (if Label t1 = Label t2 then
                                   (if Arity t1 = Arity t2 then
                                      (if (conjoin (Guard t1)) = (conjoin (Guard t2)) then
                                         (if (sum (Outputs t1)) = (sum (Outputs t2)) then
                                            (if conjoin (updates2gexps (Updates t1)) = conjoin (updates2gexps (Updates t2)) then
                                               less (more t1) (more t2)
                                           else conjoin (updates2gexps (Updates t1)) < conjoin (updates2gexps (Updates t2)))
                                         else (sum (Outputs t1)) < (sum (Outputs t2)))
                                       else (conjoin (Guard t1)) < (conjoin (Guard t2)))
                                    else (Arity t1) < (Arity t2))
                                 else Label t1 < Label t2)"

instance proof
  fix x y::"'a transition_ext"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    using less_eq_transition_ext_def less_transition_ext_def by auto
  fix x::"'a transition_ext" 
  show "x \<le> x"
    by (simp add: less_eq_transition_ext_def)
  fix x y z::"'a transition_ext"
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (smt less_eq_transition_ext_def less_trans not_less_iff_gr_or_eq order_trans)
  fix x y::"'a transition_ext"
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    apply (simp add: less_eq_transition_ext_def)
    apply (case_tac "Label x = Label y")
     apply simp
     apply (case_tac "Arity x = Arity y")
      apply simp
      apply (case_tac "conjoin (Guard x) = conjoin (Guard y)")
       apply simp
       apply (case_tac "AExp.sum (Outputs x) = AExp.sum (Outputs y)")
        apply simp
        apply (case_tac "conjoin (updates2gexps (Updates x)) = conjoin (updates2gexps (Updates y))")
         apply (simp add: conjoin_determinism updates2gexps_determinism sum_determinism)
    by simp_all
  fix x y::"'a transition_ext"
  show "x \<le> y \<or> y \<le> x"
    using less_eq_transition_ext_def by fastforce
qed
end
end