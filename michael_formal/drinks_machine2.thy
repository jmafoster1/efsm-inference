theory drinks_machine2
  imports drinks_machine Contexts
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

abbreviation t1_posterior :: "context" where
  "t1_posterior \<equiv> \<lbrakk>(V ''r1'') \<mapsto> Bc True, (V ''r2'') \<mapsto> Eq 0 \<rbrakk>"

lemma "consistent (medial empty (Guard t1))"
  by (simp add: t1_def)

lemma empty_not_undef: "empty r \<noteq> Undef \<longrightarrow> empty r = Bc True"
  apply (insert consistent_empty_1)
  by auto

lemma empty_never_false: "cexp.Bc False \<noteq> Contexts.empty x"
  apply (cases x)
  by simp_all

lemma foo: "\<not> (x \<noteq> V ''r1'' \<and> x \<noteq> V ''r2'' \<and> (x = V ''r1'' \<or> x = V ''r2''))"
  by auto

lemma "posterior t1_posterior t2 = \<lbrakk>(V ''r1'') \<mapsto> Bc True, (V ''r2'') \<mapsto> Bc True\<rbrakk>"
  apply (rule ext)
  apply (simp add: t2_def posterior_def satisfiable_def consistent_def valid_def)
  apply (simp add: empty_never_false)
  apply (rule_tac x="<>" in exI)
  by (metis (no_types, lifting) cexp2gexp.simps(1) empty_not_undef gval.simps(1) null_state_def)

lemma not_all_r2: "((\<forall>r. r = ''r2'') \<longrightarrow> (\<forall>i. i < 100))"
  by auto

lemma "cexp_equiv (Or (Gt 100) (Eq 100)) (Geq 100)"
  by (simp add: cexp_equiv_def)

lemma "gexp_equiv (gOr (gexp.Gt (V ''r1'') (N 100)) (gexp.Eq (V ''r1'') (N 100)))  (Ge (V ''r1'') (N 100))"
  apply (simp add: gexp_equiv_def)
  by auto

lemma "gval (Ge x y) = gval (gOr (gexp.Eq x y) (gexp.Gt x y))"
  apply (rule ext)
  by auto

lemma "Ge (V ''r1'') (N 100) = Nor (gexp.Lt (V ''r1'') (N 100)) (gexp.Lt (V ''r1'') (N 100))"
  by simp

lemma "gval (Ge (V ''r1'') (N 100)) r = gval (gOr (gexp.Gt (V ''r1'') (N 100)) (gexp.Eq (V ''r1'') (N 100))) r"
  by auto

lemma "(gOr (gexp.Gt (V ''r1'') (N 100)) (gexp.Eq (V ''r1'') (N 100))) = Nor (Nor (gexp.Gt (V ''r1'') (N 100)) (gexp.Eq (V ''r1'') (N 100))) (Nor (gexp.Gt (V ''r1'') (N 100)) (gexp.Eq (V ''r1'') (N 100)))"
  by simp

lemma "context_equiv (Contexts.apply_guard \<lbrakk>(V ''r1'') \<mapsto> Bc True\<rbrakk> (Ge (V ''r1'') (N 100))) 
                         (Contexts.apply_guard \<lbrakk>(V ''r1'') \<mapsto> Bc True\<rbrakk> (gOr (gexp.Gt (V ''r1'') (N 100)) (gexp.Eq (V ''r1'') (N 100))))"
  apply (simp add: context_equiv_def cexp_equiv_def)
  apply (rule allI)
  apply (case_tac r)
  by simp_all

lemma "context_equiv (medial \<lbrakk>(V ''r1'') \<mapsto> Bc True, (V ''r2'') \<mapsto> Bc True\<rbrakk> (Guard t3)) \<lbrakk>(V ''r1'') \<mapsto> Bc True, (V ''r2'') \<mapsto> Geq 100\<rbrakk>"
  apply (simp add: t3_def cexp_equiv_def context_equiv_def, rule allI)
  apply (case_tac "r = V ''r1''")
   apply simp
  apply (case_tac r)
  by simp_all

(* You can't take t3 immediately after taking t1 *)
lemma "\<not>Contexts.can_take t3 t1_posterior"
  apply (simp add: t3_def Contexts.can_take_def consistent_def)
  apply (rule allI)
  by (rule_tac x="V ''r2''" in exI, simp)


lemma consistent_t1_posterior: "consistent t1_posterior"
  apply (simp add: consistent_def)
  apply (rule_tac x="<>" in exI)
  apply (simp add: null_state_def)
  apply (rule allI)
  apply (case_tac r)
  by simp_all

lemma can_take_no_guards: "\<forall> c. (Contexts.consistent c \<and> (Guard t) = []) \<longrightarrow> Contexts.can_take t c"
  by (simp add: consistent_def Contexts.can_take_def)

lemma can_take_t2: "consistent c \<longrightarrow> Contexts.can_take t2 c"
  by (simp add: t2_def consistent_def Contexts.can_take_def)

abbreviation r1_r2_true :: "context" where
"r1_r2_true \<equiv> \<lbrakk>(V ''r1'') \<mapsto> Bc True, (V ''r2'') \<mapsto> Bc True\<rbrakk>"

lemma consistent_r1_r2_true: "consistent r1_r2_true"
  apply (simp add: consistent_def)
  apply (rule_tac x="<>" in exI)
  apply (simp add: null_state_def)
  using consistent_empty_1 by force

lemma t1_posterior: "(posterior r1_r2_true t1) = t1_posterior"
  apply (simp add: posterior_def t1_def consistent_def)
  using consistent_empty_1 by force

lemma posterior_r1_r2_true_t2: "(posterior r1_r2_true t2) = r1_r2_true"
  apply (simp add: posterior_def t2_def consistent_def satisfiable_def valid_def)
  apply safe
   apply auto[1]
  using consistent_empty_1 by force

lemma t2_empty: "(posterior r1_r2_true t2) = r1_r2_true"
  apply (rule ext)
  apply (simp add: posterior_def t2_def satisfiable_def consistent_def)
  using empty_not_undef by force

lemma valid_t2_empty: "valid_context (posterior r1_r2_true t2)"
  apply (simp add: posterior_r1_r2_true_t2)
  apply (simp add: valid_context_def)
  using consistent_empty_1 by force

lemma valid_true: "valid c \<longrightarrow> cexp_equiv c (Bc True)"
  apply (simp add: valid_def cexp_equiv_def)
  by auto

lemma posterior_t2_true: "(posterior (\<lambda>a. if a = V ''r2'' then cexp.Eq 0 else if a = V ''r1'' then cexp.Bc True else \<lbrakk>\<rbrakk> a) t2) = r1_r2_true"
  apply (rule ext)
  apply (simp add: t2_def posterior_def consistent_def valid_def satisfiable_def)
  using empty_not_undef by fastforce

lemma posterior_t2_true_true: "(posterior (\<lambda>a. if a = V ''r2'' then cexp.Bc True else if a = V ''r1'' then cexp.Bc True else \<lbrakk>\<rbrakk> a) t2) = r1_r2_true"
  apply (rule ext)
  apply (simp add: posterior_def t2_def consistent_def valid_def satisfiable_def)
  using empty_not_undef by fastforce

lemma posterior_n_t2_true_true: "(posterior_n n t2 r1_r2_true) = r1_r2_true"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by (simp add: posterior_t2_true_true fun_upd_def)
qed

(* We can go round t2 as many times as we like *)
lemma consistent_posterior_n_t2: "consistent (posterior_n n t2 t1_posterior)"
proof(induct n)
  case 0
  then show ?case 
    apply (simp add: consistent_def)
    apply (rule_tac x="<>" in exI)
    by (metis (no_types, lifting) cexp2gexp.simps(1) empty_not_undef gval.simps(1) null_state_def)
next
  case (Suc n)
  then show ?case
    apply (simp add: posterior_t2_true posterior_n_t2_true_true consistent_def)
    apply (rule_tac x="<>" in exI)
    using empty_not_undef by fastforce
  qed

(* We have to do a "coin" before we can do a "vend"*)
lemma "Contexts.can_take t3 (posterior_n n t2 (posterior r1_r2_true t1)) \<longrightarrow> n > 0"
  apply (simp add: Contexts.can_take_def consistent_def t3_def)
  apply (case_tac "n = 0")
   apply (simp add: t1_posterior)
   apply (rule allI)
   apply (rule_tac x="V ''r2''" in exI, simp)
  by (simp)

lemma posterior_n_t2_true_2: "(posterior_n (Suc n) t2 t1_posterior) = r1_r2_true"
proof (induct n)
  case 0
  then show ?case
    apply (rule ext)
    by (simp add: posterior_t2_true)
next
  case (Suc n)
  then show ?case
    by (simp add: posterior_t2_true posterior_n_t2_true_true)
qed

lemma can_take_t3: "0 < Suc n \<longrightarrow> Contexts.can_take t3 r1_r2_true"
  apply (simp add: can_take_def consistent_def t3_def)
  apply (rule_tac x="<''r2'' := 100>" in exI, simp)
  using consistent_empty_1 by fastforce
 
(* We can do any number of "coin"s before doing a "vend" *)
lemma "n > 0 \<longrightarrow> Contexts.can_take t3 (posterior_n n t2 (posterior r1_r2_true t1))"
  apply (induct_tac n)
   apply simp
  apply (simp only: t1_posterior posterior_n_t2_true_2 can_take_t3)
  by simp
end