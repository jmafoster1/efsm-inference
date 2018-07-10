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
  by (simp add: step_def t1_def t2_def)

lemma "observe_trace vend2 (s0 vend2) <> [(''select'', [1]), (''coin'', [50]), (''coin'', [50])] = [[], [50], [100]]"
  by (simp add: step_def transitions)

lemma "observe_trace vend2 (s0 vend2) <> [(''select'', [1]), (''coin'', [50]), (''coin'', [50]), (''vend'', [])] = [[], [50], [100], [1]]"
  by (simp add: step_def transitions)

lemma "equiv vend vend2 [(''select'', [1]), (''coin'', [50]), (''coin'', [50]), (''vend'', [])]"
  by (simp add: equiv_def step_def vend_def transitions)

abbreviation t1_posterior :: "context" where
  "t1_posterior \<equiv> \<lbrakk>(V (R 1)) \<mapsto> Bc True, (V (R 2)) \<mapsto> Eq 0 \<rbrakk>"

lemma "consistent (medial empty (Guard t1))"
  by (simp add: t1_def)

lemma empty_not_undef: "empty r \<noteq> Undef \<longrightarrow> empty r = Bc True"
  apply (insert consistent_empty_1)
  by auto

lemma empty_never_false: "cexp.Bc False \<noteq> Contexts.empty x"
  apply (cases x)
     prefer 2
    apply (case_tac x2)
  by simp_all

lemma foo: "\<not> (x \<noteq> V (R 1) \<and> x \<noteq> V (R 2) \<and> (x = V (R 1) \<or> x = V (R 2)))"
  by auto

lemma consistent_medial_t2: "consistent \<lbrakk>V (R (Suc 0)) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq 0\<rbrakk>"
  apply (simp add: consistent_def)
  apply (rule_tac x="<R 1 := Some 0, R 2 := Some 0>" in exI)
  apply simp
  using consistent_empty_4 by auto

lemma posterior_t2_first: "posterior t1_posterior t2 = \<lbrakk>(V (R 1)) \<mapsto> Bc True, (V (R 2)) \<mapsto> Bc True\<rbrakk>"
  apply (simp add: posterior_def consistent_medial_t2)
  apply (simp add: t2_def valid_def satisfiable_def)
  apply (rule ext)
  by simp

lemma consistent_medial_t2_2: "consistent \<lbrakk>V (R (Suc 0)) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Bc True\<rbrakk>"
  apply (simp add: consistent_def)
  apply (rule_tac x="<>" in exI)
  apply simp
  using consistent_empty_4 by auto

lemma posterior_t2_subsequent: "posterior \<lbrakk>V (R (Suc 0)) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Bc True\<rbrakk> t2 = \<lbrakk>V (R (Suc 0)) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Bc True\<rbrakk>"
  apply (simp add: posterior_def consistent_medial_t2_2)
  apply (simp add: t2_def valid_def satisfiable_def)
  apply (rule ext)
  by simp

lemma "Ge (V (R 1)) (N 100) = Nor (gexp.Lt (V (R 1)) (N 100)) (gexp.Lt (V (R 1)) (N 100))"
  by simp

lemma "gval (Ge (V (R 1)) (N 100)) r = gval (gOr (gexp.Gt (V (R 1)) (N 100)) (gexp.Eq (V (R 1)) (N 100))) r"
  by auto

lemma "(gOr (gexp.Gt (V (R 1)) (N 100)) (gexp.Eq (V (R 1)) (N 100))) = Nor (Nor (gexp.Gt (V (R 1)) (N 100)) (gexp.Eq (V (R 1)) (N 100))) (Nor (gexp.Gt (V (R 1)) (N 100)) (gexp.Eq (V (R 1)) (N 100)))"
  by simp

lemma "context_equiv (Contexts.apply_guard \<lbrakk>(V (R 1)) \<mapsto> Bc True\<rbrakk> (Ge (V (R 1)) (N 100))) 
                         (Contexts.apply_guard \<lbrakk>(V (R 1)) \<mapsto> Bc True\<rbrakk> (gOr (gexp.Gt (V (R 1)) (N 100)) (gexp.Eq (V (R 1)) (N 100))))"
  apply (simp add: context_equiv_def cexp_equiv_def)
  apply (rule allI)
  apply (case_tac r)
  by simp_all

(* You can't take t3 immediately after taking t1 *)
lemma "\<not>Contexts.can_take t3 t1_posterior"
  apply (simp add: t3_def Contexts.can_take_def consistent_def)
  apply (rule allI)
  by (rule_tac x="V (R 2)" in exI, simp)


lemma consistent_t1_posterior: "consistent t1_posterior"
  apply (simp add: consistent_def)
  apply (rule_tac x="<R 1 := Some 0, R 2 := Some 0>" in exI)
  apply simp
  apply (rule allI)
  apply (case_tac r)
     prefer 2
     apply (case_tac x2)
  by simp_all

lemma can_take_no_guards: "\<forall> c. (Contexts.consistent c \<and> (Guard t) = []) \<longrightarrow> Contexts.can_take t c"
  by (simp add: consistent_def Contexts.can_take_def)

lemma can_take_t2: "consistent c \<longrightarrow> Contexts.can_take t2 c"
  by (simp add: t2_def consistent_def Contexts.can_take_def)

abbreviation r1_r2_true :: "context" where
"r1_r2_true \<equiv> \<lbrakk>(V (R 1)) \<mapsto> Bc True, (V (R 2)) \<mapsto> Bc True\<rbrakk>"

lemma consistent_r1_r2_true: "consistent r1_r2_true"
  apply (simp add: consistent_def)
  apply (rule_tac x="<>" in exI)
  apply simp
  using consistent_empty_1 by force

lemma t1_posterior: "(posterior empty t1) = t1_posterior"
  apply (simp add: posterior_def t1_def)
  apply (rule ext)
  by simp

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
  apply (simp add: posterior_t2_subsequent)
  by (simp add: consistent_empty_4)

lemma valid_true: "valid c \<longrightarrow> cexp_equiv c (Bc True)"
  apply (simp add: valid_def cexp_equiv_def)
  by auto

lemma consistent_medial_t2_3: "consistent (\<lambda>a. if a = V (R 2) then cexp.Eq 0 else if a = V (R 1) then cexp.Bc True else \<lbrakk>\<rbrakk> a)"
  apply (simp add: consistent_def)
  apply (rule_tac x="<R 1 := Some 0, R 2 := Some 0>" in exI)
  apply simp
  by (simp add: consistent_empty_4)

lemma posterior_t2_true: "(posterior (\<lambda>a. if a = V (R 2) then cexp.Eq 0 else if a = V (R 1) then cexp.Bc True else \<lbrakk>\<rbrakk> a) t2) = r1_r2_true"
  apply (simp add: posterior_def)
  apply (simp add: consistent_medial_t2_3)
  apply (simp add: t2_def valid_def satisfiable_def)
  apply (rule ext)
  by simp

lemma r1_r2_true_equiv: "(\<lambda>a. if a = V (R 2) then cexp.Bc True else if a = V (R (Suc 0)) then cexp.Bc True else \<lbrakk>\<rbrakk> a) = r1_r2_true"
  apply (rule ext)
  by simp

lemma posterior_t2_true_true: "(posterior (\<lambda>a. if a = V (R 2) then cexp.Bc True else if a = V (R (Suc 0)) then cexp.Bc True else \<lbrakk>\<rbrakk> a) t2) = r1_r2_true"
  by (simp only: r1_r2_true_equiv t2_empty)

lemma r2_0_r1_true_equiv: "(\<lambda>a. if a = V (R 2) then cexp.Eq 0 else if a = V (R (Suc 0)) then cexp.Bc True else \<lbrakk>\<rbrakk> a) = t1_posterior"
  apply (rule ext)
  by simp

lemma posterior_n_t2_true_true: "(posterior_n n t2 r1_r2_true) = r1_r2_true"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    apply (simp add: r1_r2_true_equiv posterior_t2_subsequent)
    apply (rule ext)
    by simp
qed

lemma t1_posterior_eq: "\<lbrakk>V (R (Suc 0)) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq 0\<rbrakk> = t1_posterior"
  apply (rule ext)
  by simp

(* We can go round t2 as many times as we like *)
lemma consistent_posterior_n_t2: "consistent (posterior_n n t2 t1_posterior)"
proof(induct n)
  case 0
  then show ?case 
    apply (simp add: consistent_def)
    apply (rule_tac x="<R 1 := Some 0, R 2 := Some 0>" in exI)
    apply simp
    using consistent_empty_4 by blast
next
  case (Suc n)
  then show ?case
    apply simp
    apply (simp add: r2_0_r1_true_equiv)
    apply (simp only: t1_posterior_eq posterior_t2_first posterior_n_t2_true_true)
    using consistent_r1_r2_true by blast
  qed

(* We have to do a "coin" before we can do a "vend"*)
lemma "Contexts.can_take t3 (posterior_n n t2 (posterior \<lbrakk>\<rbrakk> t1)) \<longrightarrow> n > 0"
  apply (simp add: t1_posterior)
  apply (simp add: Contexts.can_take_def consistent_def t3_def)
  apply (case_tac "n = 0")
   apply (simp add: t1_posterior)
   apply (rule allI)
   apply (rule_tac x="V (R 2)" in exI, simp)
  by simp

lemma posterior_n_t2_true_2: "(posterior_n (Suc n) t2 t1_posterior) = r1_r2_true"
proof (induct n)
  case 0
  then show ?case
    apply simp
    apply (simp only: r2_0_r1_true_equiv posterior_t2_first)
    apply (rule ext)
    by simp
next
  case (Suc n)
  then show ?case
    apply simp
    apply (simp only: r2_0_r1_true_equiv posterior_t2_first)
    apply (simp only: r1_r2_true_equiv)
    apply (simp add: posterior_t2_subsequent)
    apply (rule ext)
    by simp
qed

lemma can_take_t3: "0 < Suc n \<longrightarrow> Contexts.can_take t3 r1_r2_true"
  apply (simp add: can_take_def consistent_def t3_def)
  apply (rule_tac x="<R 1 := Some 0, R 2 := Some 100>" in exI)
  by (simp add: consistent_empty_4)

lemma medial_t3: "medial r1_r2_true (Guard t3) = \<lbrakk>(V (R 1)) \<mapsto> Bc True, (V (R 2)) \<mapsto> And (Geq 100) (Geq 100)\<rbrakk>"
  apply (simp add: t3_def)
  apply (rule ext)
  by simp

lemma consistent_medial_t3: "consistent \<lbrakk>(V (R 1)) \<mapsto> Bc True, (V (R 2)) \<mapsto> And (Geq 100) (Geq 100)\<rbrakk>"
  apply (simp add: consistent_def)
  apply (rule_tac x="<R 1 := Some 0, R 2 := Some 100>" in exI)
  apply simp
  using consistent_empty_4 by auto
 
(* We can do any number of "coin"s before doing a "vend" *)
lemma "n > 0 \<longrightarrow> Contexts.can_take t3 (posterior_n n t2 (posterior empty t1))"
proof (induct n)
case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    apply simp
    apply (simp only: t1_posterior posterior_t2_first posterior_n_t2_true_true Contexts.can_take_def)
    by (simp only: medial_t3 consistent_medial_t3)
qed
end