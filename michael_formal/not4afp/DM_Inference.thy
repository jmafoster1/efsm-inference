theory DM_Inference
imports Inference "../examples/Drinks_Machine_2"
begin

lemma merge_q1_q2: "merge_states q1 q2 (T drinks2) = (\<lambda> (a,b) .
  if (a, b) = (q0, q1) then {|select|} else
  if (a, b) = (q1,q1) then {|vend_nothing, coin, vend_fail|} else
  if (a, b) = (q1, q3) then {|vend|} else {||})"
  apply (rule ext)
  apply clarify
  apply (simp add: merge_states_def drinks2_def merge_with_def)
  by auto

lemma defined_drinks2: "(defined (T drinks2)) = {(q0,q1), (q1,q1), (q1,q2), (q2,q2), (q2,q3)}"
  apply (simp add: defined_def drinks2_def)
  using prod.inject by fastforce

lemma finite_defined_drinks2: "finite (defined (T drinks2))"
  by (simp add: defined_drinks2)

lemma possible_transitions: "t \<noteq> select \<Longrightarrow> t \<noteq> vend_nothing \<Longrightarrow> t \<noteq> coin \<Longrightarrow> t \<noteq> vend_fail \<Longrightarrow> t \<noteq> vend \<Longrightarrow> t \<notin> (if s' = q0 \<and> s2 = q1 then {select} else if (s', s2) = (q1, q1) then {vend_nothing, coin, vend_fail} else if (s', s2) = (q1, q3) then {vend} else {})"
  by simp

lemma unequal_labels[simp]: "Label t1 \<noteq> Label t2 \<Longrightarrow> t1 \<noteq> t2"
  by auto

lemma unequal_arities[simp]: "Arity t1 \<noteq> Arity t2 \<Longrightarrow> t1 \<noteq> t2"
  by auto

lemma vend_vend_nothing_nondeterminism: "nondeterministic_pairs (merge_states q1 q2 (T drinks2)) \<noteq> {}"
  apply (simp add: nondeterministic_pairs_def merge_q1_q2)
  apply (rule_tac x=q1 in exI)
  apply (rule_tac x=q3 in exI)
  apply simp
  apply (rule_tac x=q1 in exI)
  apply simp
  apply (rule_tac x=vend_nothing in exI)
  apply (simp add: choice_def)
  apply (simp add: transitions)
  apply (rule_tac x="<R 2 := Num 100>" in exI)
  by simp

lemma nondeterminism_example: "(q1, (q1, q1), vend_nothing, vend_fail) \<in> nondeterministic_pairs (merge_states q1 q2 (T drinks2))"
  apply (simp add: merge_q1_q2 nondeterministic_pairs_def)
  apply (simp add: transitions choice_def)
  apply (rule_tac x="<R 2 := Num 0>" in exI)
  by simp

lemma nond_transitions_not_none: "nondeterministic_transitions (merge_states q1 q2 (T drinks2)) \<noteq> None"
  apply (simp add: nondeterministic_transitions_def)
  apply (simp add: vend_vend_nothing_nondeterminism)
  by (metis surj_pair)

lemma no_nondeterminism_q0: "\<forall>aa b ab ba. (q0, (aa, b), ab, ba) \<notin> nondeterministic_pairs (merge_states q1 q2 (T drinks2))"
  by (simp add: merge_q1_q2 nondeterministic_pairs_def)

lemma no_nondeterminism_q0_2: "\<forall>aa b ab ba. nondeterministic_transitions (merge_states q1 q2 (T drinks2)) \<noteq> Some (q0, (aa, b), ab, ba)"
  apply (simp add: nondeterministic_transitions_def)
  by (metis no_nondeterminism_q0 nondeterminism_example some_eq_ex)

lemma no_nondeterminism_q2: "\<forall>aa b ab ba. (q2, (aa, b), ab, ba) \<notin> nondeterministic_pairs (merge_states q1 q2 (T drinks2))"
  by (simp add: merge_q1_q2 nondeterministic_pairs_def)

lemma no_nondeterminism_q2_2: "\<forall>aa b ab ba. nondeterministic_transitions (merge_states q1 q2 (T drinks2)) \<noteq> Some (q2, (aa, b), ab, ba)"
  apply (simp add: nondeterministic_transitions_def)
  by (metis no_nondeterminism_q2 nondeterminism_example some_eq_ex)

lemma no_nondeterminism_q3: "\<forall>aa b ab ba. (q3, (aa, b), ab, ba) \<notin> nondeterministic_pairs (merge_states q1 q2 (T drinks2))"
  by (simp add: merge_q1_q2 nondeterministic_pairs_def)

lemma no_nondeterminism_q3_2: "\<forall>aa b ab ba. nondeterministic_transitions (merge_states q1 q2 (T drinks2)) \<noteq> Some (q3, (aa, b), ab, ba)"
  apply (simp add: nondeterministic_transitions_def)
  by (metis no_nondeterminism_q3 nondeterminism_example some_eq_ex)

lemma only_nondeterminism_q1: "nondeterministic_transitions (merge_states q1 q2 (T drinks2)) = Some (a, (aa, b), aaa, ba) \<Longrightarrow> a = q1"
  apply (case_tac a)
  apply (simp add: no_nondeterminism_q0_2)
    apply simp
   apply (simp add: no_nondeterminism_q2_2)
  by (simp add: no_nondeterminism_q3_2)

lemma no_transitions_to_q0: "aa = q0 \<or> b = q0 \<Longrightarrow> (a, (aa, b), ab, ba) \<notin> nondeterministic_pairs (merge_states q1 q2 (T drinks2))"
  apply (cases a)
     apply (simp add: no_nondeterminism_q0)
    apply (case_tac "aa = q0")
     apply (simp add: merge_q1_q2 nondeterministic_pairs_def)
    apply (simp add: merge_q1_q2 nondeterministic_pairs_def)
   apply (simp add: no_nondeterminism_q2)
  by (simp add: no_nondeterminism_q3)

lemma no_transitions_to_q0_2: "aa = q0 \<or> b = q0 \<Longrightarrow> nondeterministic_transitions (merge_states q1 q2 (T drinks2)) \<noteq> Some (a, (aa, b), ab, ba)"
  apply (cases a)
     apply (simp add: no_nondeterminism_q0_2)
    apply (case_tac "aa = q0")
     apply (metis no_transitions_to_q0 nondeterminism_example nondeterministic_transitions_def option.inject some_eq_ex vend_vend_nothing_nondeterminism)
    apply (metis no_transitions_to_q0 nondeterminism_example nondeterministic_transitions_def option.inject some_eq_ex vend_vend_nothing_nondeterminism)
   apply (simp add: no_nondeterminism_q2_2)
  by (simp add: no_nondeterminism_q3_2)

lemma q1_nondeterminism_options: "(q1, (q1, q1), ab, ba) \<in> nondeterministic_pairs (merge_states q1 q2 (T drinks2)) \<Longrightarrow> ab = vend_fail \<and> ba = vend_nothing \<or> ab = vend_nothing \<and> ba = vend_fail"
  apply (simp add: nondeterministic_pairs_def merge_q1_q2 choice_def)
  apply safe
  by (simp_all add: transitions)

lemma q1_nondeterminism_options_2: "nondeterministic_transitions (merge_states q1 q2 (T drinks2)) = Some (q1, (q1, q1), ab, ba) \<Longrightarrow> ab = vend_fail \<and> ba = vend_nothing \<or> ab = vend_nothing \<and> ba = vend_fail"
  apply (simp add: nondeterministic_transitions_def vend_vend_nothing_nondeterminism)
  by (metis nondeterminism_example q1_nondeterminism_options some_eq_ex)

lemma merge_self_state: "merge_states x x t = t"
  by (simp add: merge_states_def)

lemma "let t' = merge_states q1 q2 (T drinks2); t'a = merge_states q1 q1 t'
        in \<exists>x. nondeterministic_transitions t'a = Some x"
  apply (simp add: merge_q1_q2 nondeterministic_transitions_def nondeterministic_pairs_def)
  apply (simp only: merge_self_state)
  apply simp
  oops
  
  

lemma "merge drinks2 q1 q2 = Some (\<lambda> (a,b) .
  if (a, b) = (q0, q1) then {|select|} else
  if (a, b) = (q1,q1) then {|vend_nothing, coin, vend_fail|} else
  if (a, b) = (q1, q3) then {|vend|} else {||})"
  apply (simp add: s0_drinks2)
  apply (case_tac "nondeterministic_transitions (merge_states q1 q2 (T drinks2))")
   apply (simp add: nond_transitions_not_none)
  apply clarify
  apply (simp add: only_nondeterminism_q1)
  apply (case_tac a)
     apply (simp add: no_nondeterminism_q0_2)
    prefer 2
    apply (simp add: no_nondeterminism_q2_2)
  prefer 2
   apply (simp add: no_nondeterminism_q3_2)
  apply simp
  apply (case_tac aa)
     apply simp
     apply (simp add: no_transitions_to_q0_2)
    apply simp
    apply (case_tac b)
       apply simp
       apply (simp add: no_transitions_to_q0_2)
      apply simp



  



end