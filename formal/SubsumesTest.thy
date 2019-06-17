theory SubsumesTest
imports Contexts
begin

definition "coin50 = \<lparr>Label= STR ''coin'', Arity=1, Guard=[Eq (V (I 1)) (L (Num 50))], Outputs=[L (Num 50)], Updates = [(1, L (Num 50))]\<rparr>"
definition "coin = \<lparr>Label= STR ''coin'', Arity=1, Guard=[], Outputs=[V (I 1)], Updates = [(1, Plus (V (R 1)) (V (I 1)))]\<rparr>"

lemma must_be_zero: "m 1 \<noteq> Some (Num 0) \<Longrightarrow> value_plus (m 1) (Some (Num 50)) \<noteq> Some (Num 50)"
  using option.inject value.inject(1) value_plus.elims by force

lemma inconsistent_updates: "m 1 \<noteq> Some (Num 0) \<Longrightarrow> (\<exists>p1 p2.
        (\<exists>i. posterior coin (join_ir i m) = Some p2 \<and> posterior coin50 (join_ir i m) = Some p1) \<and>
        (\<exists>P r'. P (p2 r') \<and> (\<exists>y. p1 r' = Some y) \<and> \<not> P (p1 r')))"
  apply standard
  apply standard
  apply standard
  apply (rule_tac x="[Num 50]" in exI)
   apply (simp add: posterior_def)
   apply (simp add: apply_guards_def coin_def coin50_def gval.simps ValueEq_def join_ir_def input2state_def)
  apply simp
  apply (rule_tac x="\<lambda>x. x \<noteq> Some (Num 50)" in exI)
  apply (simp add: input2state_def)
  apply (rule_tac x=1 in exI)
  by (simp add: must_be_zero)

lemma "m 1 \<noteq> Some (Num 0) \<Longrightarrow> \<not> subsumes coin m coin50"
  by (simp add: subsumes_def inconsistent_updates )

lemma "m 1 = Some (Num 0) \<Longrightarrow> subsumes coin m coin50"
  apply (rule subsumption)
      apply (simp add: coin_def coin50_def)
     apply (simp add: can_take_def apply_guards_def coin_def coin50_def)
    apply (simp add: can_take_def apply_guards_def coin_def coin50_def gval.simps ValueEq_def join_ir_def input2state_def apply_outputs_def)
    apply (simp add: posterior_def can_take_def apply_guards_def coin_def coin50_def gval.simps ValueEq_def join_ir_def input2state_def apply_outputs_def)
   apply auto[1]
    apply (simp add: posterior_def can_take_def apply_guards_def coin_def coin50_def gval.simps ValueEq_def join_ir_def input2state_def apply_outputs_def)
  by auto

end