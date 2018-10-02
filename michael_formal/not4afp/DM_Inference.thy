theory DM_Inference
imports Inference "../examples/Drinks_Machine_2"
begin
lemma merge_q1_q2: "merge_states q1 q2 (T drinks2) = (\<lambda> (a,b) .
  if (a, b) = (q0, q1) then {select} else
  if (a, b) = (q1,q1) then {vend_nothing, coin, vend_fail} else
  if (a, b) = (q1, q3) then {vend} else {})"
  apply (rule ext)
  apply clarify
  apply (simp add: merge_states_def drinks2_def merge_with_def)
  by auto

lemma "nondeterminism (merge_states q1 q2 (T drinks2))"
  apply (simp add: nondeterminism_def merge_q1_q2 choice_def nondeterministic_pairs_def)
  apply (rule_tac x=q1 in exI)
  apply simp
  apply (rule_tac x=q3 in exI)
  apply simp
  apply (rule_tac x=q1 in exI)
  apply simp
  apply (rule_tac x=vend_nothing in exI)
  apply safe
  apply (simp add: vend_def vend_nothing_def)
  apply (simp add: vend_def vend_nothing_def)
  apply (simp add: vend_def vend_nothing_def)
  apply (rule_tac x="<R 2 := Num 100>" in exI)
  by (simp add: vend_def vend_nothing_def)

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

lemma nondeterministic_transitions_q1_q2: "nondeterministic_transitions (merge_states q1 q2 (T drinks2)) \<noteq> None"
  by (simp add: nondeterministic_transitions_def nondeterministic_pairs_q1_q2)  

lemma "merge \<lbrakk>\<rbrakk> (T drinks2) q1 q2 = Some (\<lambda> (a,b) .
  if (a, b) = (q0, q1) then {select} else
  if (a, b) = (q1,q1) then {vend_nothing, coin, vend_fail} else
  if (a, b) = (q1, q3) then {vend} else {})"
  apply (simp add: finite_defined_drinks2)
  apply (case_tac "nondeterministic_transitions (merge_states q1 q2 (T drinks2))")
   apply (simp add: nondeterministic_transitions_q1_q2)
  apply simp
  apply (case_tac a)
  apply simp
  apply (case_tac b)
  apply simp
  

end