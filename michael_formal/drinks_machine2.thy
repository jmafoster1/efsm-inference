theory drinks_machine2
  imports drinks_machine Constraints
begin

definition vend2 :: "efsm" where
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
  by (simp add: vend2_def transitions step_def)

lemma "observe_trace vend2 (s0 vend2) <> [(''select'', [1]), (''coin'', [50])] = [[], [50]]"
  by (simp add: step_def vend2_def transitions shows_stuff index_def join_def)

lemma "observe_trace vend2 (s0 vend2) <> [(''select'', [1]), (''coin'', [50]), (''coin'', [50])] = [[], [50], [100]]"
  by (simp add: step_def vend2_def transitions shows_stuff index_def join_def)

lemma "observe_trace vend2 (s0 vend2) <> [(''select'', [1]), (''coin'', [50]), (''coin'', [50]), (''vend'', [])] = [[], [50], [100], [1]]"
  by (simp add: step_def vend2_def transitions shows_stuff index_def join_def)

lemma "equiv vend vend2 [(''select'', [1]), (''coin'', [50]), (''coin'', [50]), (''vend'', [])]"
  by (simp add: equiv_def step_def vend_def vend2_def transitions shows_stuff index_def join_def)

abbreviation t1_posterior :: "constraints" where
  "t1_posterior \<equiv> (\<lambda>x. if x=''r2'' then Eq 0 else Bc True)"

lemma "posterior empty t1 = t1_posterior"
  by (simp add: t1_def posterior_def update_def consistent_def)

lemma "apply_plus empty (V a) (V b) = Bc True"
  by (simp add: apply_plus.psimps)

lemma "posterior t1_posterior t2 = empty"
  apply (simp add: posterior_def t2_def update_def consistent_def)
  apply (rule ext)
  by (simp add: Constraints.apply_plus.psimps(4))

lemma "constraints_equiv (posterior empty t3) (\<lambda>i. if i = ''r2'' then Geq 100 else Bc True)"
  apply (simp add: t3_def constraints_equiv_def posterior_def consistent_def update_def)
  by auto

end