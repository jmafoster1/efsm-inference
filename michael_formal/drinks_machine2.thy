theory drinks_machine2
  imports drinks_machine Contexts
begin

abbreviation drinks2 :: "efsm" where
(* Effectively this is the drinks_machine which has had the loop unrolled by one iteration *)
"drinks2 \<equiv> \<lparr> S = [1,2,3,4],
          s0 = 1,
          T = \<lambda> (a,b) . 
              if (a,b) = (1,2) then [select]
              else if (a,b) = (2,3) then [coin]
              else if (a,b) = (3,3) then [coin]
              else if (a,b) = (3,4) then [vend]
              else []
         \<rparr>"

lemma "observe_trace drinks2 (s0 drinks2) <> [] = []"
  by simp

lemma "observe_trace drinks2 (s0 drinks2) <> [(''select'', [Str ''coke''])] = [[]]"
  by (simp add: step_def select_def)

lemma "observe_trace drinks2 (s0 drinks2) <> [(''select'', [Str ''coke'']), (''coin'', [Num 50])] = [[], [Num 50]]"
  by (simp add: step_def select_def coin_def)

lemma "observe_trace drinks2 (s0 drinks2) <> [(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 50])] = [[], [Num 50], [Num 100]]"
  by (simp add: step_def transitions)

lemma "observe_trace drinks2 (s0 drinks2) <> [(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 50]), (''vend'', [])] = [[], [Num 50], [Num 100], [Str ''coke'']]"
  by (simp add: step_def transitions)

lemma "equiv drinks drinks2 [(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 50]), (''vend'', [])]"
  by (simp add: equiv_def step_def drinks_def transitions)

abbreviation select_posterior :: "context" where
  "select_posterior \<equiv> \<lbrakk>(V (R 1)) \<mapsto> Bc True, (V (R 2)) \<mapsto> Eq (Num 0) \<rbrakk>"

lemma "consistent (medial empty (Guard select))"
  by (simp add: select_def)

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

lemma consistent_medial_coin: "consistent \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk>"
  apply (simp add: consistent_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num 0>" in exI)
  apply (simp del: Nat.One_nat_def)
  using consistent_empty_4 by auto

lemma posterior_coin_first: "posterior select_posterior coin = \<lbrakk>(V (R 1)) \<mapsto> Bc True, (V (R 2)) \<mapsto> Bc True\<rbrakk>"
  apply (simp add: posterior_def consistent_medial_coin del: Nat.One_nat_def)
  apply (simp add: coin_def valid_def satisfiable_def)
  apply (rule ext)
  by simp

lemma consistent_medial_coin_2: "consistent \<lbrakk>V (R (Suc 0)) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Bc True\<rbrakk>"
  apply (simp add: consistent_def)
  apply (rule_tac x="<>" in exI)
  apply (simp del: Nat.One_nat_def)
  using consistent_empty_4 by auto

lemma posterior_coin_subsequent: "posterior \<lbrakk>V (R (Suc 0)) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Bc True\<rbrakk> coin = \<lbrakk>V (R (Suc 0)) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Bc True\<rbrakk>"
  apply (simp add: posterior_def consistent_medial_coin_2)
  apply (simp add: coin_def valid_def satisfiable_def)
  apply (rule ext)
  by simp

lemma value_lt_aval: "aval x r = Some a \<Longrightarrow> aval y r = Some aa \<Longrightarrow> ValueLt (Some a) (Some aa) = Some ab \<Longrightarrow> \<exists>n n'. a = Num n \<and> aa = Num n'"
  by (metis MaybeBoolInt.elims option.distinct(1) option.sel)

lemma ge_equiv: "gval (Ge x y) r = gval (gOr (gexp.Gt x y) (gexp.Eq x y)) r"
  apply simp
  apply (cases "aval x r")
   apply (cases "aval y r")
    apply simp
   apply simp
  apply (cases "aval y r")
   apply simp
  apply simp
  apply (case_tac "ValueLt (Some a) (Some aa)")
   apply simp
   apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some a) (Some aa)")
    apply simp
   apply simp
  using MaybeBoolInt.elims apply force
  apply simp
  apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some a) (Some aa)")
   apply simp
  using MaybeBoolInt.elims apply force
  apply simp
  using value_lt_aval by fastforce

lemma "(gOr (gexp.Gt (V (R 1)) (N 100)) (gexp.Eq (V (R 1)) (N 100))) = Nor (Nor (gexp.Gt (V (R 1)) (N 100)) (gexp.Eq (V (R 1)) (N 100))) (Nor (gexp.Gt (V (R 1)) (N 100)) (gexp.Eq (V (R 1)) (N 100)))"
  by simp

lemma "gval x = gval y \<Longrightarrow> context_equiv (Contexts.apply_guard c x) (Contexts.apply_guard c y)"
  apply (simp add: context_equiv_def cexp_equiv_def)
  apply (rule allI)
  apply safe
     apply (simp del: Nat.One_nat_def)
  sorry

lemma "context_equiv (Contexts.apply_guard \<lbrakk>(V (R 1)) \<mapsto> Bc True\<rbrakk> (Ge (V (R 1)) (L (Num 100))))
                         (Contexts.apply_guard \<lbrakk>(V (R 1)) \<mapsto> Bc True\<rbrakk> (gOr (gexp.Gt (V (R 1)) (L (Num 100))) (gexp.Eq (V (R 1)) (L (Num 100)))))"
  apply (simp add: context_equiv_def cexp_equiv_def del: Nat.One_nat_def)
  apply (rule allI)
  apply (case_tac r)
  by simp_all

(* You can't take vend immediately after taking select *)
lemma r2_0_vend: "\<not>Contexts.can_take vend select_posterior"
  apply (simp only: vend_def Contexts.can_take_def)
  apply (simp only: consistent_def)
  apply (simp del: Nat.One_nat_def)
  apply (rule allI)
  apply (case_tac "s (R 2)")
   apply (simp del: Nat.One_nat_def)
   apply fastforce
   apply (simp del: Nat.One_nat_def)
  apply (case_tac "ValueLt (Some a) (Some (Num 100))")
   apply (simp del: Nat.One_nat_def)
   apply fastforce
  apply (simp del: Nat.One_nat_def)
  by fastforce

lemma consistent_select_posterior: "consistent select_posterior"
  apply (simp add: consistent_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num 0>" in exI)
  apply (simp del: Nat.One_nat_def)
  apply (rule allI)
  apply (case_tac r)
     prefer 2
     apply (case_tac x2)
  by simp_all

lemma can_take_no_guards: "\<forall> c. (Contexts.consistent c \<and> (Guard t) = []) \<longrightarrow> Contexts.can_take t c"
  by (simp add: consistent_def Contexts.can_take_def)

lemma can_take_coin: "consistent c \<longrightarrow> Contexts.can_take coin c"
  by (simp add: coin_def consistent_def Contexts.can_take_def)

abbreviation r1_r2_true :: "context" where
"r1_r2_true \<equiv> \<lbrakk>(V (R 1)) \<mapsto> Bc True, (V (R 2)) \<mapsto> Bc True\<rbrakk>"

lemma consistent_r1_r2_true: "consistent r1_r2_true"
  apply (simp add: consistent_def)
  apply (rule_tac x="<>" in exI)
  apply (simp del: Nat.One_nat_def)
  using consistent_empty_1 by force

lemma select_posterior: "(posterior empty select) = select_posterior"
  apply (simp add: posterior_def select_def)
  apply (rule ext)
  by simp

lemma posterior_r1_r2_true_coin: "(posterior r1_r2_true coin) = r1_r2_true"
  apply (simp add: posterior_def coin_def consistent_def satisfiable_def valid_def)
  apply safe
   apply auto[1]
  using consistent_empty_1 by force

lemma coin_empty: "(posterior r1_r2_true coin) = r1_r2_true"
  apply (rule ext)
  apply (simp add: posterior_def coin_def satisfiable_def consistent_def)
  using empty_not_undef by force

lemma valid_coin_empty: "valid_context (posterior r1_r2_true coin)"
  apply (simp add: posterior_r1_r2_true_coin)
  apply (simp add: valid_context_def)
  apply (simp add: posterior_coin_subsequent)
  by (simp add: consistent_empty_4)

lemma valid_true: "valid c \<longrightarrow> cexp_equiv c (Bc True)"
  apply (simp add: valid_def cexp_equiv_def)
  by auto

lemma consistent_medial_coin_3: "consistent (\<lambda>a. if a = V (R 2) then cexp.Eq (Num 0) else if a = V (R 1) then cexp.Bc True else \<lbrakk>\<rbrakk> a)"
  apply (simp add: consistent_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num 0>" in exI)
  apply (simp del: Nat.One_nat_def)
  by (simp add: consistent_empty_4)

lemma posterior_coin_true: "(posterior (\<lambda>a. if a = V (R 2) then cexp.Eq (Num 0) else if a = V (R 1) then cexp.Bc True else \<lbrakk>\<rbrakk> a) coin) = r1_r2_true"
  apply (simp add: posterior_def)
  apply (simp add: consistent_medial_coin_3)
  apply (simp add: coin_def valid_def satisfiable_def)
  apply (rule ext)
  by simp

lemma r1_r2_true_equiv: "(\<lambda>a. if a = V (R 2) then cexp.Bc True else if a = V (R 1) then cexp.Bc True else \<lbrakk>\<rbrakk> a) = r1_r2_true"
  apply (rule ext)
  by simp

lemma posterior_coin_true_true: "posterior r1_r2_true coin = r1_r2_true"
  using posterior_r1_r2_true_coin by blast

lemma r2_0_r1_true_equiv: "(\<lambda>a. if a = V (R 2) then cexp.Eq (Num 0) else if a = V (R 1) then cexp.Bc True else \<lbrakk>\<rbrakk> a) = select_posterior"
  apply (rule ext)
  by simp

lemma posterior_n_coin_true_true: "(posterior_n n coin r1_r2_true) = r1_r2_true"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    apply (simp add: r1_r2_true_equiv posterior_coin_subsequent  del: Nat.One_nat_def)
    by (simp only: posterior_coin_true_true)
qed

(* We can go round coin as many times as we like *)
lemma consistent_posterior_n_coin: "consistent (posterior_n n coin select_posterior)"
proof(induct n)
  case 0
  then show ?case 
    apply (simp add: consistent_def)
    apply (rule_tac x="<R 1 := Num 0, R 2 := Num 0>" in exI)
    apply (simp del: Nat.One_nat_def)
    using consistent_empty_4 by blast
next
  case (Suc n)
  then show ?case
    apply (simp del: Nat.One_nat_def)
    apply (simp add: r2_0_r1_true_equiv del: Nat.One_nat_def)
    apply (simp only:  posterior_coin_first posterior_n_coin_true_true)
    using consistent_r1_r2_true by blast
qed

(* We have to do a "coin" before we can do a "vend"*)
lemma coin_before_vend: "Contexts.can_take vend (posterior_n n coin (posterior \<lbrakk>\<rbrakk> select)) \<longrightarrow> n > 0"
  apply (simp add: select_posterior del: Nat.One_nat_def)
  apply (cases n)
   apply (simp add: r2_0_vend del: Nat.One_nat_def)
  by simp

lemma posterior_n_coin_true_2: "(posterior_n (Suc n) coin select_posterior) = r1_r2_true"
proof (induct n)
  case 0
  then show ?case
    apply (simp del: Nat.One_nat_def)
    apply (simp only: r2_0_r1_true_equiv posterior_coin_first)
    apply (rule ext)
    by simp
next
  case (Suc n)
  then show ?case
    apply (simp del: Nat.One_nat_def)
    apply (simp only: r2_0_r1_true_equiv posterior_coin_first)
    apply (simp only: r1_r2_true_equiv)
    apply (simp add: posterior_coin_subsequent)
    apply (rule ext)
    by simp
qed

lemma can_take_vend: "0 < Suc n \<longrightarrow> Contexts.can_take vend r1_r2_true"
  apply (simp add: can_take_def consistent_def vend_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num 100>" in exI)
  by (simp add: consistent_empty_4)

lemma medial_vend: "medial r1_r2_true (Guard vend) = \<lbrakk>(V (R 1)) \<mapsto> Bc True, (V (R 2)) \<mapsto> And (Geq (Num 100)) (Geq (Num 100))\<rbrakk>"
  apply (simp add: vend_def)
  apply (rule ext)
  by simp

lemma consistent_medial_vend: "consistent \<lbrakk>(V (R 1)) \<mapsto> Bc True, (V (R 2)) \<mapsto> And (Geq (Num 100)) (Geq (Num 100))\<rbrakk>"
  apply (simp add: consistent_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num 100>" in exI)
  apply (simp del: Nat.One_nat_def)
  using consistent_empty_4 by auto
 
(* We can do any number of "coin"s before doing a "vend" *)
lemma "n > 0 \<longrightarrow> Contexts.can_take vend (posterior_n n coin (posterior empty select))"
proof (induct n)
case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    apply (simp del: Nat.One_nat_def)
    apply (simp only: select_posterior posterior_coin_first posterior_n_coin_true_true Contexts.can_take_def)
    by (simp only: medial_vend consistent_medial_vend)
qed
end