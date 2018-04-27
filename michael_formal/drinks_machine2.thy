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
  "t1_posterior \<equiv> (\<lambda>x. if x=''r2'' then Eq 0 else vend_start x)"

lemma "posterior vend_start t1 = t1_posterior"
  apply (rule ext)
  by (simp add: posterior_def t1_def)

lemma "apply_plus empty (V a) (V b) = Bc True"
  by (simp add: apply_plus.psimps)

lemma "posterior t1_posterior t2 = vend_start"
  apply (rule ext)
  by (simp add: t2_def posterior_def)

lemma not_all_r2: "((\<forall>r. r = ''r2'') \<longrightarrow> (\<forall>i. i < 100))"
  by auto

lemma "cexp_equiv (Or (Gt 100) (Eq 100)) (Geq 100)"
  by auto

lemma "(gOr (gexp.Gt ''r1'' (N 100)) (gexp.Eq ''r1'' (N 100))) = gexp.Not (gexp.And (gexp.Not (gexp.Gt ''r1'' (N 100))) (gexp.Not (gexp.Eq ''r1'' (N 100))))"
  by simp

lemma "constraints_equiv (Constraints.apply_guard empty (Ge ''r1'' (N 100))) (Constraints.apply_guard empty (gOr (gexp.Gt ''r1'' (N 100)) (gexp.Eq ''r1'' (N 100))))"
  apply simp
  by auto

lemma "(posterior vend_start t3) = (\<lambda>i. if i = ''r2'' then Geq 100 else vend_start i)"
  apply (simp add: posterior_def t3_def)
  by auto

(* You can't take t3 immediately after taking t1 *)
lemma "\<not>Constraints.can_take t3 t1_posterior"
  apply (simp add: t3_def)
  apply (rule_tac x="''r2''" in exI)
  apply simp  
  done

lemma "consistent t1_posterior"
  by simp

lemma can_take_no_guards: "\<forall> c. (Constraints.consistent c \<and> (Guard t) = []) \<longrightarrow> Constraints.can_take t c"
  by simp

lemma can_take_t2: "consistent c \<longrightarrow> Constraints.can_take t2 c"
  by (simp add: t2_def)

lemma t2_with_empty: "constraints_equiv x empty \<longrightarrow> constraints_equiv (posterior x t2) (posterior empty t2)"
  apply (simp add: posterior_def t2_def)
  by auto

lemma t2_empty: "(posterior vend_start t2) = vend_start"
  apply (rule ext)
  apply (simp add: posterior_def t2_def)
  by auto

lemma valid_t2_empty: "valid_constraints (posterior vend_start t2)"
  by (simp add: posterior_def t2_def)

lemma valid_true: "valid c \<longrightarrow> cexp_equiv c (Bc True)"
  by simp

lemma valid_empty: "(\<forall>r. valid(c r)) \<longrightarrow> constraints_equiv c empty"
  by simp

lemma posterior_n_t2_empty: "(posterior_n n t2 vend_start) = vend_start"
  apply (induct_tac n)
   apply simp
  apply (insert t2_with_empty t2_empty valid_empty)
  by simp

lemma posterior_t2_empty: "posterior vend_start t2 = vend_start"
  apply (simp add: t2_def posterior_def)
  apply safe
  apply (rule ext)
  by simp

lemma posterior_t2_is_empty: "(posterior t1_posterior t2) = vend_start"
  apply (rule ext)
  by (simp add: t2_def posterior_def)

(* We can go round t2 as many times as we like *)
lemma consistent_posterior_n_t2: "consistent (posterior_n n t2 t1_posterior)"
  apply (induct_tac n)
   apply simp
  by (simp add: posterior_t2_is_empty posterior_n_t2_empty)

(* We have to do a "coin" before we can do a "vend"*)
lemma "Constraints.can_take t3 (posterior_n n t2 (posterior vend_start t1)) \<longrightarrow> n > 0"
  apply (simp add: posterior_def t1_def)
  apply (case_tac "n = 0")
  apply (simp add: t3_def)
  apply (rule_tac x="''r2''" in exI)
   apply simp
  by (simp add: t3_def t2_def)

lemma equiv_t1_posterior: "(\<lambda>r. if r = ''r2'' then cexp.Eq 0 else if r = ''r1'' then cexp.Bc True else no_regs r) = t1_posterior"
  apply (rule ext)
  by (simp add: t1_def)

lemma can_take_t3: "Constraints.can_take t3 (posterior_n n t2 vend_start)"
  apply (induct_tac n)
   apply (simp add: t3_def)
   apply auto[1]
  apply (simp)
  by (simp add: posterior_t2_empty)

(* We can do any number of "coin"s before doing a "vend" *)
lemma "n > 0 \<longrightarrow> Constraints.can_take t3 (posterior_n n t2 (posterior vend_start t1))"
  apply (simp add: posterior_def t1_def)
  apply (induct_tac n)
   apply simp
  apply simp
  apply (simp add: equiv_t1_posterior)
  apply (simp add: posterior_t2_is_empty)
  apply (simp add: can_take_t3)
  by auto
end