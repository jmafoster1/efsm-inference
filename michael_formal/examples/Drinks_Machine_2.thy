theory Drinks_Machine_2
  imports Drinks_Machine "../Contexts"
begin

definition drinks2 :: "statename efsm" where
(* Effectively this is the drinks_machine which has had the coin loop unrolled by one iteration *)
"drinks2 \<equiv> \<lparr>
          s0 = q0,
          T = \<lambda> (a,b) . 
              if (a,b) = (q0,q1) then {select}
              else if (a,b) = (q1,q2) then {coin}
              else if (a,b) = (q2,q2) then {coin}
              else if (a,b) = (q2,q3) then {vend}
              else {}
         \<rparr>"

lemma s0_drinks2 [simp]: "s0 drinks2 = q0"
  by (simp add: drinks2_def)

lemma label_select_q1: " Label b = ''select'' \<Longrightarrow> b \<in> T drinks2 (q0, s') \<Longrightarrow> b = select \<and> s' = q1"
  apply (simp add: drinks2_def)
  apply (cases s')
  by (simp_all add: select_def)

lemma label_coin_q1: "Label t = ''coin'' \<and> t \<in> T drinks2 (q1, s') \<Longrightarrow> t=coin \<and> s' = q2"
  apply (simp add: drinks2_def)
  apply (cases s')
  by (simp_all add: coin_def)

lemma label_coin_q2: "Label t = ''coin'' \<and> t \<in> T drinks2 (q2, s') \<Longrightarrow> t=coin \<and> s' = q2"
  apply (simp add: drinks2_def)
  apply (cases s')
     apply simp
    apply simp
   apply simp
  apply simp
  apply (simp add: vend_def)
  by auto

lemma label_vend_q3: " Label b = ''vend'' \<Longrightarrow>
           b \<in> T drinks2 (q2, a) \<Longrightarrow> b = vend \<and> a = q3"
  apply (cases a)
     apply (simp add: drinks2_def)
    apply (simp add: drinks2_def)
   apply (simp add: drinks2_def transitions(2))
  by (simp add: drinks2_def)

lemma possible_steps_q0:  "possible_steps drinks2 q0 Map.empty ''select'' [Str ''coke''] = {(q1, select)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (simp add: label_select_q1)
      apply (simp add: label_select_q1)
     apply (simp add: transitions(1))
    apply (simp add: drinks2_def)
   apply (simp add: transitions(1))
  by simp

lemma possible_steps_q1: "possible_steps drinks2 q1 r ''coin'' [Num 50] = {(q2, coin)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (simp add: label_coin_q1)
  using label_coin_q1 apply blast
     apply (simp add: transitions(2))
    apply (simp add: drinks2_def)
   apply (simp add: transitions(2))
  by simp

lemma possible_steps_q2_coin: "possible_steps drinks2 statename.q2 r ''coin'' [Num 50] = {(q2, coin)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (simp add: label_coin_q2)
      using label_coin_q2 apply blast
     apply (simp add: transitions(2))
    apply (simp add: drinks2_def)
   apply (simp add: transitions(2))
  by simp

lemma possible_steps_q2_vend: "possible_steps drinks2 statename.q2 <R (Suc 0) := Str ''coke'', R 2 := Num 100> ''vend'' [] = {(q3, vend)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (simp add: label_vend_q3)
      apply (simp add: label_vend_q3)
     apply (simp add: vend_def)
    apply (simp add: drinks2_def)
   apply (simp add: vend_def)
  by (simp add: vend_def)

lemma purchase_coke: "observe_trace drinks2 (s0 drinks2) <> [(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 50]), (''vend'', [])] = [[], [Num 50], [Num 100], [Str ''coke'']]"
  apply (simp add: possible_steps_q0)
  apply (simp add: possible_steps_q1)
  apply (simp add: possible_steps_q2_coin)
  by (simp add: possible_steps_q2_vend vend_def coin_def)

lemma "equiv drinks drinks2 [(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 50]), (''vend'', [])]"
  apply (simp add: equiv_def possible_steps_q0 Drinks_Machine.possible_steps_q0)
  apply (simp add:  possible_steps_q1 Drinks_Machine.possible_steps_q1_coin)
  apply (simp add: possible_steps_q2_coin Drinks_Machine.possible_steps_q1_coin_2)
  by (simp add: possible_steps_q2_vend Drinks_Machine.possible_steps_q2_vend)

lemma step_drinks_select: "length (snd a) = Suc 0 \<Longrightarrow> possible_steps drinks Drinks_Machine.statename.q0 Map.empty ''select'' (snd a) = {(Drinks_Machine.q1, select)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (case_tac aa)
         apply (simp add: drinks_def)
        apply (simp add: drinks_def)
       apply (simp add: drinks_def)
      apply (simp add: drinks_def)
      apply (meson Drinks_Machine.statename.distinct(1) empty_iff prod.inject singletonD)
  by (simp_all add: select_def drinks_def)

lemma step_drinks2_select: "length (snd a) = Suc 0 \<Longrightarrow> possible_steps drinks2 q0 Map.empty ''select'' (snd a) = {(q1, select)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (case_tac aa)
          apply (simp add: drinks2_def)
         apply (simp add: drinks2_def)
        apply (simp add: drinks2_def)
       apply (simp add: drinks2_def)
      apply (simp add: drinks2_def)
      apply (meson Drinks_Machine_2.statename.distinct(1) Drinks_Machine_2.statename.distinct(3) empty_iff prod.inject singletonD)
  by (simp_all add: select_def drinks2_def)

lemma step_drinks_q0_invalid: "\<not> (fst a = ''select'' \<and> length (snd a) = 1) \<Longrightarrow> (possible_steps drinks Drinks_Machine.statename.q0 Map.empty (fst a) (snd a)) = {}"
  apply (simp add: possible_steps_def)
  apply (rule allI)
  apply (rule allI)
  apply (case_tac aa)
    apply (simp add: drinks_def)
   apply (simp add: drinks_def select_def)
   apply auto[1]
  by (simp add: drinks_def)

lemma step_drinks2_q0_invalid: "\<not> (fst a = ''select'' \<and> length (snd a) = 1) \<Longrightarrow> (possible_steps drinks2 q0 Map.empty (fst a) (snd a)) = {}"
  apply (simp add: possible_steps_def)
  apply (rule allI)
  apply (rule allI)
  apply (case_tac aa)
     apply (simp add: drinks2_def)
    apply (simp add: drinks2_def select_def)
    apply auto[1]
   apply (simp add: drinks2_def)
  by (simp add: drinks2_def)

lemma select_updates: "length (snd a) = Suc 0 \<Longrightarrow> (EFSM.apply_updates (Updates select) (case_vname (\<lambda>n. index2state (snd a) (Suc 0) (I n)) Map.empty) Map.empty) = <R 1 := hd (snd a), R 2 := Num 0>"
  apply (rule ext)
  apply (simp add: select_def)
  by (metis index2state.simps(2) length_Suc_conv list.sel(1))

lemma step_drinks_coin: "length (snd aa) = Suc 0 \<Longrightarrow> (possible_steps drinks Drinks_Machine.statename.q1 r ''coin'' (snd aa)) = {(Drinks_Machine.statename.q1, coin)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (case_tac b)
       apply (simp add: drinks_def)
       apply (meson Drinks_Machine.label_coin_q1 transition.select_convs(1))
      apply (simp add: drinks_def)
  using Drinks_Machine.label_coin_q1 apply blast
  by (simp_all add: coin_def drinks_def)

lemma drinks_coin_q0: "possible_steps drinks Drinks_Machine.statename.q0 Map.empty ''coin'' (snd aa) = {}"
  apply (simp add: possible_steps_def)
  apply (rule allI)
  apply (rule allI)
  apply (case_tac a)
  by (simp_all add: drinks_def select_def)

lemma drinks2_coin_q0: "possible_steps drinks2 Drinks_Machine_2.statename.q0 Map.empty ''coin'' (snd aa) = {}"
  apply (simp add: possible_steps_def)
  apply safe
  apply (case_tac a)
          apply (simp add: drinks2_def)
         apply (simp add: drinks2_def)
    apply (simp add: select_def)
   apply (simp add: drinks2_def)
  by (simp add: drinks2_def)

lemma empty_not_singleton [simp]: "\<not> is_singleton {}"
  by (simp add: is_singleton_def)

lemma drinks2_coin_q1: "length (snd aa) = Suc 0 \<Longrightarrow> (possible_steps drinks2 q1 r ''coin'' (snd aa)) = {(q2, coin)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (case_tac a)
          apply (simp add: drinks2_def)
         apply (simp add: drinks2_def)
        apply (simp add: drinks2_def)
       apply (simp add: drinks2_def)
      apply (case_tac a)
  by (simp_all add: coin_def drinks2_def)

lemma updates_coin: "length i = 1 \<Longrightarrow> (EFSM.apply_updates (Updates coin) (case_vname (\<lambda>n. index2state i 1 (I n)) (\<lambda>n. if n = 2 then Some x else <R 1 := hd (snd a)> (R n)))
                  <R 1 := hd (snd a), R 2 := x>) = (\<lambda>e. if e = R 1 then Some (hd (snd a)) else (if e = R 2 then (value_plus (Some x) (Some (hd i))) else None))"
  apply (rule ext)
  by (simp add: coin_def hd_input2state del: One_nat_def)

lemma equal_q1_q2: "\<forall>r. observe_trace drinks2 Drinks_Machine_2.statename.q1 r t =
        observe_trace drinks2 Drinks_Machine_2.statename.q2 r t"
proof (induction t)
  case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case sorry
qed

lemma drinks_vend_none: "a = (''vend'', []) \<Longrightarrow>
    r (R 2) = None \<Longrightarrow>
    (possible_steps drinks Drinks_Machine.statename.q1 r ''vend'' []) = {}"
  sorry

lemma drinks2_vend_none: "r (R 2) = None \<Longrightarrow> possible_steps drinks2 Drinks_Machine_2.statename.q1 r ''vend'' [] = {}"
  sorry

lemma equal_vend_none: "a = (''vend'', []) \<Longrightarrow> r (R 2) = None \<Longrightarrow> observe_trace drinks Drinks_Machine.statename.q1 r (a # t) = observe_trace drinks2 Drinks_Machine_2.statename.q1 r (a # t)"
  by (simp add: drinks_vend_none is_singleton_def drinks2_vend_none)

lemma drinks_vend_insufficient: "r (R 2) = Some (Num x1) \<Longrightarrow>
               x1 < 100 \<Longrightarrow>
                (possible_steps drinks Drinks_Machine.statename.q1 r ''vend'' []) = {}"
  apply (simp add: possible_steps_def)
  apply (rule allI)
  apply (rule allI)
  apply (case_tac a)
    apply (simp add: drinks_def)
   apply (simp add: drinks_def coin_def)
  by (simp add: drinks_def vend_def)

lemma drinks2_vend_insufficient: "r (R 2) = Some (Num x1) \<Longrightarrow>
               x1 < 100 \<Longrightarrow>
               possible_steps drinks2 Drinks_Machine_2.statename.q1 r ''vend'' [] = {}"
  apply (simp add: possible_steps_def)
  apply (rule allI)
  apply (rule allI)
  by (simp add: drinks2_def coin_def)

lemma drinks_vend_sufficient: "r (R 2) = Some (Num x1) \<Longrightarrow>
               \<not> x1 < 100 \<Longrightarrow>
               (possible_steps drinks Drinks_Machine.statename.q1 r ''vend'' []) = {(Drinks_Machine.q2, vend)}"
  apply (simp add: possible_steps_def)
  apply safe
  apply (case_tac a)
         apply (simp add: drinks_def)
        apply (simp add: drinks_def coin_def)
       apply (simp add: drinks_def)
      apply (case_tac a)
        apply (simp add: drinks_def)
       apply (simp add: drinks_def coin_def)
      apply (simp add: drinks_def)
     apply (simp add: vend_def)
    apply (simp add: drinks_def)
   apply (simp add: vend_def)
  by (simp add: vend_def)

lemma drinks2_vend_q1: "r (R 2) = Some (Num x1) \<Longrightarrow>
               \<not> x1 < 100 \<Longrightarrow>
               (possible_steps drinks2 Drinks_Machine_2.statename.q1 r ''vend'' []) = {}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (case_tac a)
  apply (simp add: drinks2_def)
  apply (simp add: drinks2_def)
  apply (simp add: drinks2_def coin_def)
  by (simp add: drinks2_def)

lemma equal_q1_q1: "\<forall>r. observe_trace drinks Drinks_Machine.statename.q1 r t = observe_trace drinks2 Drinks_Machine_2.statename.q1 r t"
proof (induction t)
  case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case
    apply (case_tac "fst a = ''coin'' \<and> length (snd a) = 1")
     apply (simp add: drinks2_coin_q1 updates_coin possible_steps_q1_coin del: One_nat_def)
     apply (simp add: equal_q1_q2)
    apply (case_tac "a = (''vend'', [])")
    apply (rule allI)
     apply (case_tac "r (R 2)")
    using equal_vend_none apply blast
     apply (case_tac aa)
      apply (case_tac "x1 < 100")
       apply (simp add: drinks_vend_insufficient drinks2_vend_insufficient)
      apply simp
    apply (simp add: drinks_vend_sufficient drinks2_vend_q1)
qed

lemma "equiv drinks drinks2 t"
  proof (induct t)
  case Nil
    then show ?case by (simp add: equiv_def)
  next
  case (Cons a t)
  then show ?case
    apply (simp add: equiv_def)
    apply (case_tac "fst a = ''select'' \<and> length (snd a) = 1")
     prefer 2
     apply (simp add: step_drinks_q0_invalid step_drinks2_q0_invalid is_singleton_def)
    apply simp
    apply (simp add: step_drinks_select step_drinks2_select select_updates del: One_nat_def)
    by (simp add: equal_q1_q1)
  qed

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
  apply (case_tac aa)
  apply (case_tac a)
  by auto

lemma "(gOr (gexp.Gt (V (R 1)) (N 100)) (gexp.Eq (V (R 1)) (N 100))) = Nor (Nor (gexp.Gt (V (R 1)) (N 100)) (gexp.Eq (V (R 1)) (N 100))) (Nor (gexp.Gt (V (R 1)) (N 100)) (gexp.Eq (V (R 1)) (N 100)))"
  by simp

lemma apply_ge_100: "(apply_guard \<lbrakk>V (R 1) \<mapsto> cexp.Bc True\<rbrakk> (Ge (V (R 1)) (L (Num 100)))) = \<lbrakk>V (R 1) \<mapsto> Geq (Num 100)\<rbrakk>"
  apply (rule ext)
  by simp

lemma apply_gt_100_eq_100: "(apply_guard \<lbrakk>V (R 1) \<mapsto> cexp.Bc True\<rbrakk> (gOr (GExp.Lt (L (Num 100)) (V (R 1))) (gexp.Eq (V (R 1)) (L (Num 100))))) = \<lbrakk>V (R 1) \<mapsto> cexp.Not (And (Neq (Num 100)) (Leq (Num 100)))\<rbrakk>"
  apply (rule ext)
  by simp

lemma "cexp_equiv (cexp.Not (And (Neq (Num 100)) (Leq (Num 100)))) (Geq (Num 100))"
  apply (simp add: cexp_equiv_def)
  apply (rule allI)
  apply (case_tac i)
   apply auto[1]
  by simp

lemma "context_equiv (apply_guard \<lbrakk>(V (R 1)) \<mapsto> Bc True\<rbrakk> (Ge (V (R 1)) (L (Num 100))))
                      (apply_guard \<lbrakk>(V (R 1)) \<mapsto> Bc True\<rbrakk> (gOr (gexp.Gt (V (R 1)) (L (Num 100))) (gexp.Eq (V (R 1)) (L (Num 100)))))"
  apply (simp only: apply_ge_100 apply_gt_100_eq_100)
  apply (simp only: context_equiv_def cexp_equiv_def)
  apply safe
    apply (case_tac r)
       apply simp
      apply simp
      apply (case_tac i)
       apply auto[1]
      apply auto[1]
     apply (case_tac r)
        apply simp
       apply simp
      apply simp
     apply simp
    apply simp
   apply (case_tac r)
      apply simp
     apply (case_tac "x2=R 1")
      apply simp
     apply simp
    apply simp
   apply simp
  apply (case_tac r)
     apply simp
    apply (case_tac "x2=R 1")
     apply simp
    apply simp
   apply simp
  by simp

lemma medial_select_posterior_vend: "medial select_posterior (Guard vend) = \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> And (Eq (Num 0)) (Geq (Num 100))\<rbrakk>"
  apply (rule ext)
  by (simp add: guard_vend)

lemma "\<not> GExp.satisfiable (gAnd (gexp.Eq (V (R 2)) (L (Num 0))) (Ge (V (R 2)) (L (Num 100))))"
  apply (simp add: GExp.satisfiable_def)
  apply (rule allI)
  apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some (Num 100)) (s (R 2))")
   apply simp
  apply simp
  apply (case_tac "s (R 2) = Some (Num 0)")
   apply simp
  by simp

(* You can't take vend immediately after taking select *)
lemma r2_0_vend: "\<not>Contexts.can_take vend select_posterior"
  apply (simp only: can_take_def medial_select_posterior_vend)
  apply (simp add: consistent_def)
  apply (rule allI)
  apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some (Num 100)) (s (R 2))")
   apply fastforce
  apply simp
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
  proof (induction n)
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

lemma medial_vend: "medial r1_r2_true (Guard vend) = \<lbrakk>(V (R 1)) \<mapsto> Bc True, (V (R 2)) \<mapsto> (Geq (Num 100))\<rbrakk>"
  apply (simp add: vend_def)
  apply (rule ext)
  by simp

lemma consistent_medial_vend: "consistent \<lbrakk>(V (R 1)) \<mapsto> Bc True, (V (R 2)) \<mapsto> (Geq (Num 100))\<rbrakk>"
  apply (simp add: consistent_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num 100>" in exI)
  apply (simp del: Nat.One_nat_def)
  using consistent_empty_4 by auto
 
(* We can do any number of "coin"s before doing a "vend" *)
lemma "n > 0 \<longrightarrow> Contexts.can_take vend (posterior_n n coin (posterior empty select))"
  proof (induction n)
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