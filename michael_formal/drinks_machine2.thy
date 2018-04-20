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

lemma can_take_no_guards: "\<forall> c. (Constraints.consistent c \<and> (Guard t) = []) \<longrightarrow> Constraints.can_take t c"
  by (simp add: consistent_def)

lemma can_take_t2: "consistent c \<longrightarrow> Constraints.can_take t2 c"
  by (simp add: t2_def)

 lemma apply_plus_consistent: "(\<forall>r. satisfiable (c r)) \<longrightarrow> satisfiable (compose_plus (c x) (c y))"
  proof (cases "c x")
    case (Bc x1)
    then show ?thesis
      apply simp
      apply (case_tac "x1 = True")
       apply simp
      apply simp
      by (metis ceval.simps(1) consistent_def)
    next
      case (Eq x2)
      then show ?thesis
        apply simp
        apply (cases "c y")
             apply (case_tac "x1 = True")
              apply simp_all
            apply (metis ceval.simps(1) consistent_def)
           apply presburger
          apply presburger
         apply (case_tac "x5")
        apply simp
              apply (metis (full_types) ceval.simps(1) ceval.simps(5) consistent_def)
             apply simp
            apply auto[1]
           apply auto[1]
        apply simp
    next
      case (Lt x3)
      then show ?thesis sorry
    next
      case (Gt x4)
      then show ?thesis sorry
    next
      case (Not x5)
      then show ?thesis sorry
    next
      case (And x61 x62)
      then show ?thesis sorry
  qed


lemma posterior_t2_consistent: "consistent c \<longrightarrow> consistent (posterior c t2)"
  apply (simp add: t2_def posterior_def consistent_def)

lemma "consistent (posterior_n n t2 t1_posterior)"
  apply (induct_tac "n")
   apply (simp add: consistent_def)
  apply (simp add: consistent_def t2_def)
  apply (simp add: can_take_t2)
end