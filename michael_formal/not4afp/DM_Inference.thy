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
  apply safe
  apply (rule_tac x=q1 in exI)
  apply (rule_tac x=vend_nothing in exI)
  apply (rule_tac x=vend_fail in exI)
  apply simp
  apply safe
  apply (simp add: vend_nothing_def vend_fail_def)
  apply (simp add: vend_nothing_def vend_fail_def)
  apply (rule_tac x=q1 in exI)
  apply (simp add: vend_nothing_def vend_fail_def)
  apply (rule_tac x="<R 2 := Num 0>" in exI)
  by simp
end