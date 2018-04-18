theory drinks_machine2
  imports drinks_machine Constraints
begin

abbreviation vend2 :: "efsm" where
(* Effectively this is the drinks_machine which has had the loop unrolled by one iteration *)
"vend2 \<equiv> \<lparr> S = [1,2,3,4],
          s0 = 1,
          T = \<lambda> (a,b) . 
              if (a,b) = (1,2) then [t1]
              else if (a,b) = (2,3) then [t2]
              else if (a,b) = (3,3) then [t2]
              else if (a,b) = (3,4) then [t3]
              else []
         \<rparr>"

lemma "observe_trace vend2 (s0 vend2) <> [] = []"
  by simp

lemma "observe_trace vend2 (s0 vend2) <> [(''select'', [1])] = [[]]"
  by (simp add: step_def t1_def)

lemma "observe_trace vend2 (s0 vend2) <> [(''select'', [1]), (''coin'', [50])] = [[], [50]]"
  by (simp add: step_def shows_stuff index_def join_def t1_def t2_def)

lemma "observe_trace vend2 (s0 vend2) <> [(''select'', [1]), (''coin'', [50]), (''coin'', [50])] = [[], [50], [100]]"
  by (simp add: step_def shows_stuff index_def join_def transitions)

lemma "observe_trace vend2 (s0 vend2) <> [(''select'', [1]), (''coin'', [50]), (''coin'', [50]), (''vend'', [])] = [[], [50], [100], [1]]"
  by (simp add: step_def shows_stuff index_def join_def transitions)

lemma "equiv vend vend2 [(''select'', [1]), (''coin'', [50]), (''coin'', [50]), (''vend'', [])]"
  by (simp add: equiv_def step_def vend_def transitions shows_stuff index_def join_def)

abbreviation t1_posterior :: "constraints" where
  "t1_posterior \<equiv> (\<lambda>x. if x=''r2'' then Eq 0 else Bc True)"

lemma "posterior empty t1 = t1_posterior"
  by (simp add: posterior_def consistent_def t1_def)

lemma "apply_plus empty (V a) (V b) = Bc True"
  by (simp add: apply_plus.psimps)

lemma "posterior t1_posterior t2 = empty"
  by (simp add: t2_def posterior_def consistent_def)

lemma not_all_r2: "((\<forall>r. r = ''r2'') \<longrightarrow> (\<forall>i. i < 100))"
  by auto

lemma "cexp_equiv (Or (Gt 100) (Eq 100)) (Geq 100)"
  by auto

value "(Constraints.guard2constraints empty (Ge ''r1'' (N 100)))"
value "(Constraints.guard2constraints empty (gOr (gexp.Gt ''r1'' (N 100)) (gexp.Eq ''r1'' (N 100))))"

lemma "(gOr (gexp.Gt ''r1'' (N 100)) (gexp.Eq ''r1'' (N 100))) = gexp.Not (gexp.And (gexp.Not (gexp.Gt ''r1'' (N 100))) (gexp.Not (gexp.Eq ''r1'' (N 100))))"
  by simp

lemma "constraints_equiv (Constraints.apply_guard empty (Ge ''r1'' (N 100))) (Constraints.apply_guard empty (gOr (gexp.Gt ''r1'' (N 100)) (gexp.Eq ''r1'' (N 100))))"
  apply simp
  apply (simp add: constraints_equiv_def)
  by auto

lemma "constraints_equiv (posterior empty t3) (\<lambda>i. if i = ''r2'' then Geq 100 else Bc True)"
  apply (simp add: posterior_def consistent_def t3_def constraints_equiv_def)
  by auto

(* You can't take t3 immediately after taking t1 *)
lemma "\<not>Constraints.can_take t3 t1_posterior"
  by (simp add: consistent_def t3_def)

lemma "consistent t1_posterior"
  by (simp add: consistent_def)

lemma "\<forall>n. consistent (posterior_n n t2 t1_posterior)"
  sorry
end