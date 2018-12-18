theory Simple_Drinks_Machine
imports "../Contexts" "../examples/Drinks_Machine_2" Inference
begin

declare One_nat_def [simp del]

definition t1 :: "transition" where
"t1 \<equiv> \<lparr>
        Label = ''select'',
        Arity = 1,
        Guard = [],
        Outputs = [],
        Updates = [(R 1, (V (I 1))), (R 2, (L (Num 0)))]
      \<rparr>"

definition coin50 :: "transition" where
"coin50 \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [(gexp.Eq (V (I 1)) (L (Num 50)))],
        Outputs = [(Plus (V (R 2)) (V (I 1)))],
        Updates = [(R 1, (V (R 1))),  (R 2, Plus (V (R 2)) (L (Num 50)))]
      \<rparr>"

lemma updates_coin50: "Updates coin50 = [(R 1, (V (R 1))),  (R 2, Plus (V (R 2)) (L (Num 50)))]"
  by (simp add: coin50_def)

definition coin :: "transition" where
"coin \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [],
        Outputs = [(Plus (V (R 2)) (V (I 1)))],
        Updates = [
                  (R 1, (V (R 1))),
                  (R 2, (Plus (V (R 2)) (V (I 1))))
                ]
      \<rparr>"

lemma guard_coin: "Guard coin = []"
  by (simp add: coin_def)

definition t3 :: "transition" where
"t3 \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [(Ge (V (R 2)) (L (Num 100)))],
        Outputs =  [(V (R 1))],
        Updates = [(R 1, (V (R 1))), (R 2, (V (R 2)))]
      \<rparr>"

definition vend :: transition_matrix where
"vend \<equiv>  {|
              ((0,1), t1), \<comment> \<open> If we want to go from state 1 to state 2, t1 will do that \<close>
              ((1,1), coin50), \<comment> \<open> If we want to go from state 2 to state 2, coin50 will do that \<close>
              ((1,2), t3) \<comment> \<open> If we want to go from state 2 to state 3, t3 will do that \<close>
         |}"

definition vend_equiv :: transition_matrix where
"vend_equiv \<equiv> {|
                ((0,1), t1),    \<comment> \<open> If we want to go from state 1 to state 2, t1 will do that \<close>
                ((1,1), coin),  \<comment> \<open> If we want to go from state 2 to state 2, coin will do that \<close>
                ((1,2), t3)     \<comment> \<open> If we want to go from state 2 to state 3, t3 will do that \<close>
              |}"


definition drinks2 :: transition_matrix where
"drinks2 \<equiv> {|
              ((0,1), select),
              ((1,1), vend_nothing),
              ((1,2), coin50),
              ((2,2), coin),
              ((2,2), vend_fail),
              ((2,3), Drinks_Machine.vend)
         |}"

lemmas transitions = Drinks_Machine_2.transitions coin_def coin50_def

lemma medial_coin50: "medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> (Guard coin50) = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n), V (I 1) \<mapsto> Eq (Num 50)\<rbrakk>"
  apply (simp add: coin50_def)
  apply (rule ext)
  by simp

lemma consistent_medial_coin50: "consistent (medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> (Guard coin50))"
  apply (simp add: coin50_def consistent_def)
  apply (rule_tac x="<R 1 := Num 1, R 2 := Num n, I 1 := Num 50>" in exI)
  by (simp add: consistent_empty_4)

lemma compose_plus_n_50: "(compose_plus (Eq (Num n)) (Eq (Num 50))) = Eq (Num (n+50))"
  apply (simp add: valid_def satisfiable_def)
  by auto

lemma coin50_posterior: "posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> coin50 = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> Eq (Num (n+50))\<rbrakk>"
  apply (simp add: posterior_def consistent_medial_coin50)
  apply (simp only: medial_coin50 updates_coin50)
  apply (simp add: compose_plus_n_50 del: compose_plus.simps)
  apply (rule ext)
  by (simp add: remove_input_constraints_def)

lemma consistent_medial_coin: "consistent (medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n), V (I 1) \<mapsto> cexp.Eq (Num 50)\<rbrakk> (Guard coin))"
  apply (simp add: coin_def consistent_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num n, I 1 := Num 50>" in exI)
  apply (simp)
  by (simp add: consistent_empty_4)

lemma consistent_medial_coin_2: "consistent (medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> (Guard coin))"
  apply (simp add: coin_def consistent_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num n, I 1 := Num 50>" in exI)
  apply (simp)
  by (simp add: consistent_empty_4)

lemma posterior_coin: "(posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> coin) = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> Bc True\<rbrakk>"
  apply (simp add: posterior_def consistent_medial_coin_2)
  apply (simp add: coin_def compose_plus_n_50 valid_def satisfiable_def remove_input_constraints_def)
  apply (rule ext)
  by simp

lemma medial_coin: "\<forall>c. medial c (Guard Simple_Drinks_Machine.coin) = c"
  by (simp add: coin_def)

lemma possible_steps_coin_50: "possible_steps Simple_Drinks_Machine.drinks2 1 r ''coin'' [Num 50] = {|(2, coin50)|}"
proof-
  have set_filter: "(Set.filter
       (\<lambda>((origin, dest), t).
           origin = 1 \<and>
           Label t = ''coin'' \<and> Suc 0 = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state [Num 50] 1 (I n)) (\<lambda>n. r (R n))))
       (fset Simple_Drinks_Machine.drinks2)) =
    {((1, 2), coin50)}"
    apply (simp add: Set.filter_def drinks2_def)
    apply safe
    by (simp_all add: select_def vend_nothing_def coin50_def)
  have abs_fset: "Abs_fset {((1, 2), coin50)} = {|((1, 2), coin50)|}"
    by (metis fset_inverse fset_simps(1) fset_simps(2))
  show ?thesis
    by (simp add: possible_steps_def ffilter_def set_filter abs_fset)
qed

lemma possible_steps_1_vend: "possible_steps Simple_Drinks_Machine.drinks2 1 r ''vend'' [] = {|(1, vend_nothing)|}"
proof-
  have set_filter: "(Set.filter
       (\<lambda>((origin, dest), t).
           origin = 1 \<and> Label t = ''vend'' \<and> Arity t = 0 \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state [] 1 (I n)) (\<lambda>n. r (R n))))
       (fset Simple_Drinks_Machine.drinks2)) =
    {((1, 1), vend_nothing)}"
    apply (simp add: drinks2_def Set.filter_def)
    apply safe
    by (simp_all add: select_def coin50_def vend_nothing_def)
  show ?thesis
    by (simp add: possible_steps_def ffilter_def set_filter abs_fset_singleton)
qed

lemma invalid_step: "\<not> (aa = ''coin'' \<and> b = [Num 50]) \<Longrightarrow> \<not> (aa = ''vend'' \<and> b = []) \<Longrightarrow> possible_steps Simple_Drinks_Machine.drinks2 1 r aa b = {||}"
proof-
  have set_filter: "\<not> (aa = ''coin'' \<and> b = [Num 50]) \<Longrightarrow> \<not> (aa = ''vend'' \<and> b = []) \<Longrightarrow> (Set.filter
       (\<lambda>((origin, dest), t).
           origin = 1 \<and> Label t = aa \<and> length b = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) (\<lambda>n. r (R n))))
       (fset Simple_Drinks_Machine.drinks2)) =
    {}"
    apply (simp add: drinks2_def Set.filter_def)
    apply safe
    apply (simp_all add: vend_nothing_def coin50_def)
     apply (metis One_nat_def input2state.simps(2) length_0_conv length_Suc_conv option.sel)
    by (metis One_nat_def input2state.simps(2) length_0_conv length_Suc_conv option.inject)
  show "\<not> (aa = ''coin'' \<and> b = [Num 50]) \<Longrightarrow> \<not> (aa = ''vend'' \<and> b = []) \<Longrightarrow> possible_steps Simple_Drinks_Machine.drinks2 1 r aa b = {||}"
    apply (simp add: possible_steps_def ffilter_def set_filter)
    by (simp add: bot_fset.abs_eq)
qed

lemma next_step_1: "step Simple_Drinks_Machine.drinks2 1 r aa b = Some (uw, s', ux, r') \<Longrightarrow> s' = 1 \<or> s' = 2"
  apply (case_tac "aa = ''coin'' \<and> b = [Num 50]")
   apply (simp add: step_def possible_steps_coin_50)
  apply (case_tac "aa = ''vend'' \<and> b = []")
   apply (simp add: step_def possible_steps_1_vend)
  apply (simp only: step_def)
  using invalid_step
  by simp

lemma set_filter_vend_fail: "ra (R 2) = Some (Num x1) \<and> x1 < 100 \<Longrightarrow> (Set.filter
       (\<lambda>((origin, dest), t).
           origin = 2 \<and> Label t = ''vend'' \<and> Arity t = 0 \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state [] 1 (I n)) (\<lambda>n. ra (R n))))
       (fset Simple_Drinks_Machine.drinks2)) =
    {((2, 2), vend_fail)}"
    apply (simp add: drinks2_def Set.filter_def)
    apply safe
    by (simp_all add: transitions)
lemma possible_steps_vend_fail: "ra (R 2) = Some (Num x1) \<and> x1 < 100 \<Longrightarrow> possible_steps Simple_Drinks_Machine.drinks2 2 ra ''vend'' [] = {|(2, vend_fail)|}"
    by (simp add: possible_steps_def ffilter_def set_filter_vend_fail)

lemma no_route_from_3_to_0: "\<forall>r. \<not>gets_us_to 0 Simple_Drinks_Machine.drinks2 3 r t"
proof (induct t)
  case Nil
  then show ?case
    apply clarify
    apply (rule gets_us_to.cases)
    by auto
next
  have set_filter: "\<forall>ra aa b. (Set.filter
       (\<lambda>((origin, dest), t).
           origin = 3 \<and> Label t = aa \<and> length b = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) (\<lambda>n. ra (R n))))
       (fset Simple_Drinks_Machine.drinks2)) = {}"
    by (simp add: drinks2_def Set.filter_def)
  have possible_steps: "\<forall>ra aa b. possible_steps Simple_Drinks_Machine.drinks2 3 ra aa b = {||}"
    apply (simp add: possible_steps_def ffilter_def set_filter)
    by (simp add: bot_fset.abs_eq)
  have step: "\<forall>ra aa b. step Simple_Drinks_Machine.drinks2 3 ra aa b = None"
    by (simp add: step_def possible_steps)
  case (Cons a t)
  then show ?case
    apply clarify
    apply (rule gets_us_to.cases)
       apply simp
      apply simp
     defer
     apply simp
    apply clarify
    apply simp
    using step
    by simp
qed

lemma next_step_2: "step Simple_Drinks_Machine.drinks2 2 ra aa b = Some (uw, s', u, r') \<Longrightarrow> s' = 2 \<or> s' = 3"
proof-
  assume premise: "step Simple_Drinks_Machine.drinks2 2 ra aa b = Some (uw, s', u, r')"
  have set_filter: "(Set.filter
       (\<lambda>((origin, dest), t).
           origin = 2 \<and> Label t = ''coin'' \<and> Arity t = 1 \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) (\<lambda>n. ra (R n))))
       (fset Simple_Drinks_Machine.drinks2)) =
    {((2, 2), Simple_Drinks_Machine.coin)}"
    apply (simp add: Set.filter_def drinks2_def)
    apply safe
    by (simp_all add: transitions)
  have possible_steps_coin: "length b = 1 \<Longrightarrow> possible_steps Simple_Drinks_Machine.drinks2 2 ra ''coin'' b = {|(2, coin)|}"
    by (simp add: possible_steps_def ffilter_def set_filter)
  have possible_steps_vend_r2_none: "\<nexists> n. ra (R 2) = Some (Num n) \<Longrightarrow> possible_steps Simple_Drinks_Machine.drinks2 2 ra ''vend'' [] = {||}"
  proof-
    assume premise: "\<nexists> n. ra (R 2) = Some (Num n)"
    have set_filter: "(Set.filter
       (\<lambda>((origin, dest), t).
           origin = 2 \<and> Label t = ''vend'' \<and> Arity t = 0 \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state [] 1 (I n)) (\<lambda>n. ra (R n))))
       (fset Simple_Drinks_Machine.drinks2)) = {}"
      using premise
      apply (simp add: Set.filter_def drinks2_def)
      apply safe
        apply (simp add: transitions)
       apply (simp add: transitions)
      using MaybeBoolInt.elims apply force
       apply (simp add: transitions)
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some (Num 100)) (ra (R 2))")
       apply simp
      apply simp
      by (metis MaybeBoolInt.elims option.simps(3))
    show ?thesis
      using premise
      apply (simp add: possible_steps_def ffilter_def set_filter)
      by (simp add: bot_fset_def)
  qed
  have set_filter_invalid: "\<not> (aa = ''coin'' \<and> length b = 1) \<Longrightarrow> \<not> (aa = ''vend'' \<and> b = []) \<Longrightarrow> (Set.filter
       (\<lambda>((origin, dest), t).
           origin = 2 \<and> Label t = aa \<and> length b = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) (\<lambda>n. ra (R n))))
       (fset Simple_Drinks_Machine.drinks2)) = {}"
    apply (simp add: drinks2_def Set.filter_def)
    apply safe
    by (simp_all add: transitions)
  have possible_steps_invalid: "\<not> (aa = ''coin'' \<and> length b = 1) \<Longrightarrow> \<not> (aa = ''vend'' \<and> b = []) \<Longrightarrow>
                      possible_steps Simple_Drinks_Machine.drinks2 2 ra aa b = {||}"
    apply (simp add: possible_steps_def ffilter_def set_filter_invalid)
    by (simp add: bot_fset_def)
  show ?thesis
    using premise
    apply (simp add: step_def)
    apply (case_tac "aa = ''coin'' \<and> length b = 1")
     apply clarify
     apply (simp add: possible_steps_coin)
    apply (case_tac "aa = ''vend'' \<and> b = []")
     apply clarify
     apply (case_tac "ra (R 2)")
      apply (simp add: possible_steps_vend_r2_none)
     apply (case_tac a)
      apply simp
      defer
      apply (simp add: possible_steps_vend_r2_none)
    using possible_steps_invalid
     apply simp
    apply (case_tac "x1 < 100")
     apply (simp add: possible_steps_vend_fail)



  sorry

lemma no_route_from_2_to_0: "\<forall>r. \<not>gets_us_to 0 Simple_Drinks_Machine.drinks2 2 r t"
proof (induct t)
  case Nil
  then show ?case
    apply safe
    apply (rule gets_us_to.cases)
    by auto
next
  case (Cons a t)
  then show ?case
    apply safe
    apply (rule gets_us_to.cases)
       apply simp
      apply simp
     defer
     apply simp
    apply clarify
    apply simp
    apply (case_tac "s' = 2")
     apply simp
    apply (case_tac "s' = 3")
    apply simp
     apply (simp add: no_route_from_3_to_0)
    using next_step_2 by blast
qed

lemma no_route_from_1_to_0: "\<forall>r. \<not>gets_us_to 0 Simple_Drinks_Machine.drinks2 1 r t"
proof(induct t)
  case Nil
  then show ?case
    apply safe
    apply (rule gets_us_to.cases)
    by auto
next
  case (Cons a t)
  then show ?case
    apply safe
    apply (rule gets_us_to.cases)
       apply simp
      apply simp
     defer
     apply simp
    apply clarify
    apply simp
    apply (case_tac "s' = 1")
     apply simp
    apply (case_tac "s' = 2")
     apply (simp add: no_route_from_2_to_0)
    using next_step_1 by blast
qed

(* Prove this to make sure that you've got "directly_subsumes" the right way round *)
lemma "directly_subsumes drinks2 0 coin coin50"
proof-
  have coin_subsumes_coin50: "subsumes \<lbrakk>\<rbrakk> Simple_Drinks_Machine.coin coin50"
  proof-
    have aux1: "(\<forall>r i. cval (medial \<lbrakk>\<rbrakk> (Guard coin50) r) i = Some True \<longrightarrow> cval (medial \<lbrakk>\<rbrakk> (Guard Simple_Drinks_Machine.coin) r) i = Some True)"
      apply (simp add: coin50_def coin_def)
      apply clarify
      apply (case_tac "cval (\<lbrakk>\<rbrakk> r) i")
       apply simp
      by simp
    have aux2: "(\<forall>i r. apply_guards (Guard coin50) (join_ir i r) \<longrightarrow>
           apply_outputs (Outputs coin50) (join_ir i r) = apply_outputs (Outputs Simple_Drinks_Machine.coin) (join_ir i r))"
      by (simp add: coin50_def coin_def)
    have medial_coin_50: "medial \<lbrakk>\<rbrakk> (Guard coin50) = \<lbrakk>V (I 1) \<mapsto> Eq (Num 50)\<rbrakk>"
      apply (rule ext)
      by (simp add: coin50_def)
    have consistent_medial_coin: "consistent \<lbrakk>V (I 1) \<mapsto> cexp.Eq (Num 50)\<rbrakk>"
      apply (simp add: consistent_def)
      apply (rule_tac x="<I 1 := Num 50>" in exI)
      apply (rule allI)
      by (simp add: consistent_empty_4)
    have posterior_coin50: "posterior \<lbrakk>\<rbrakk> coin50 = \<lbrakk>V (R 2) \<mapsto> Bc False\<rbrakk>"
      unfolding posterior_def Let_def
      apply (simp only: medial_coin_50)
      apply (simp add: consistent_medial_coin remove_input_constraints_def)
      apply (rule ext)
      by (simp add: coin50_def)
    have aux3: "(\<forall>r i. cval (posterior (medial \<lbrakk>\<rbrakk> (Guard coin50)) Simple_Drinks_Machine.coin r) i = Some True \<longrightarrow>
           cval (posterior \<lbrakk>\<rbrakk> coin50 r) i = Some True \<or> posterior \<lbrakk>\<rbrakk> coin50 r = Undef)"
    proof-
      have posterior_coin: "posterior \<lbrakk>V (I 1) \<mapsto> cexp.Eq (Num 50)\<rbrakk> Simple_Drinks_Machine.coin = \<lbrakk>V (R 2) \<mapsto> Bc False\<rbrakk>"
        unfolding posterior_def Let_def
        apply (simp add: medial_coin consistent_medial_coin remove_input_constraints_def)
        apply (rule ext)
        by (simp add: coin_def)
      show ?thesis
        apply (simp only: medial_coin_50)
        by (simp add: posterior_coin posterior_coin50)
    qed
    have aux4: "(consistent (posterior \<lbrakk>\<rbrakk> coin50) \<longrightarrow> consistent (posterior \<lbrakk>\<rbrakk> Simple_Drinks_Machine.coin))"
      apply (simp only: posterior_coin50)
      using possible_false_not_consistent
      by (meson fun_upd_same)
    show ?thesis
      unfolding subsumes_def
      using aux1 aux2 aux3 aux4
      by simp
  qed
  have step_select: "\<forall>i. length i = 1 \<longrightarrow> step Simple_Drinks_Machine.drinks2 0 Map.empty ''select'' i = Some (select, 1, [], <R 1 := hd i, R 2 := Num 0>)"
  proof-
    have possible_steps: "\<forall>i. length i = 1 \<longrightarrow> possible_steps Simple_Drinks_Machine.drinks2 0 Map.empty ''select'' i = {|(1, select)|}"
    proof-
      have set_filter: "\<forall>i. length i = 1 \<longrightarrow> (Set.filter
            (\<lambda>((origin, dest), t).
                origin = 0 \<and> Label t = ''select'' \<and> Arity t = 1 \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state i 1 (I n)) Map.empty))
            (fset Simple_Drinks_Machine.drinks2)) = {((0, 1), select)}"
        apply (simp add: Set.filter_def drinks2_def)
        apply safe
        by (simp_all add: transitions)
      have abs_fset: "Abs_fset {((0, 1), select)} = {|((0, 1), select)|}"
        by (metis fset_inverse fset_simps(1) fset_simps(2))
      show ?thesis
        apply (rule allI)
        apply clarify
        apply (simp add: possible_steps_def ffilter_def)
        by (simp add: set_filter abs_fset)
    qed
    show ?thesis
      unfolding step_def
      apply (rule allI)
      apply (simp add: possible_steps)
      apply (simp add: select_def)
      apply clarify
      apply (rule ext)
      apply simp
      by (simp add: hd_input2state)
  qed
  have coin_subsumes_coin50_2: "subsumes select_posterior Simple_Drinks_Machine.coin coin50"
  proof-
    have aux1: "(\<forall>r i. cval (medial select_posterior (Guard coin50) r) i = Some True \<longrightarrow>
           cval (medial select_posterior (Guard Simple_Drinks_Machine.coin) r) i = Some True)"
      apply (simp add: coin50_def coin_def)
      apply safe
      apply (case_tac "cval (\<lbrakk>\<rbrakk> r) i")
       apply simp
      by simp
    have aux2: "(\<forall>i r. apply_guards (Guard coin50) (join_ir i r) \<longrightarrow>
           apply_outputs (Outputs coin50) (join_ir i r) = apply_outputs (Outputs Simple_Drinks_Machine.coin) (join_ir i r))"
      by (simp add: coin50_def coin_def)
    have aux3: "(\<forall>r i. cval (posterior (medial select_posterior (Guard coin50)) Simple_Drinks_Machine.coin r) i = Some True \<longrightarrow>
           cval (posterior select_posterior coin50 r) i = Some True \<or> posterior select_posterior coin50 r = Undef)"
    proof-
      have medial_coin50: "medial select_posterior (Guard coin50) = \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> Eq (Num 0), V (I 1) \<mapsto> Eq (Num 50)\<rbrakk>"
        apply (rule ext)
        by (simp add: coin50_def)
      have consistent_medial_coin50: "consistent \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> Eq (Num 0), V (I 1) \<mapsto> Eq (Num 50)\<rbrakk>"
        apply (simp add: consistent_def)
        apply (rule_tac x="<R 1 := Num 0, R 2 := Num 0, I 1 := Num 50>" in exI)
        apply (rule allI)
        by (simp add: consistent_empty_4)
      have posterior_coin50: "posterior select_posterior coin50 = \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> Eq (Num 50)\<rbrakk>"
        unfolding posterior_def Let_def
        apply (simp only: medial_coin50)
        apply (simp add: consistent_medial_coin50)
        apply (simp add: remove_input_constraints_def)
        apply (rule ext)
        apply (simp add: coin50_def valid_def satisfiable_def)
        by auto
      have medial_coin: "\<forall>c. medial c (Guard coin) = c"
        by (simp add: coin_def)
      have consistent_medial_coin: "consistent \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> Eq (Num 0), V (I 1) \<mapsto> Eq (Num 50)\<rbrakk>"
        unfolding consistent_def
        apply (rule_tac x="<R 1 := Num 0, R 2 := Num 0, I 1 := Num 50>" in exI)
        apply (rule allI)
        by (simp add: consistent_empty_4)
      have posterior_coin: "posterior \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> Eq (Num 0), V (I 1) \<mapsto> Eq (Num 50)\<rbrakk> Simple_Drinks_Machine.coin = \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> Eq (Num 50)\<rbrakk>"
        unfolding posterior_def Let_def
        apply (simp add: medial_coin consistent_medial_coin remove_input_constraints_def)
        apply (rule ext)
        apply (simp add: coin_def valid_def satisfiable_def)
        by auto
      show ?thesis
        apply clarify
        by (simp add: posterior_coin50 medial_coin50 posterior_coin)
    qed
    have aux4: "(consistent (posterior select_posterior coin50) \<longrightarrow> consistent (posterior select_posterior Simple_Drinks_Machine.coin))"
      apply (simp only: posterior_coin)
      using consistent_r1_r2_true by auto
    show ?thesis
      unfolding subsumes_def
      using aux1 aux2 aux3 aux4
      by simp
  qed
  have test: "\<forall>list aa ba. aa = ''select'' \<and> length ba = 1 \<longrightarrow> \<not>gets_us_to 0 Simple_Drinks_Machine.drinks2 0 Map.empty ((''select'', ba) # list)"
  proof-
    show ?thesis
      apply clarify
      apply (rule gets_us_to.cases)
         apply simp
        apply simp
       apply clarify
       apply simp
       apply (simp add: step_select no_route_from_1_to_0)
      apply clarify
      by (simp add: step_select)
  qed
  have test2: "\<forall>aa ba. \<not> (aa = ''select'' \<and> length ba = 1) \<longrightarrow> step Simple_Drinks_Machine.drinks2 0 Map.empty aa ba = None"
  proof-
    have possible_steps_invalid: "\<forall>aa ba. \<not> (aa = ''select'' \<and> length ba = 1) \<longrightarrow> possible_steps Simple_Drinks_Machine.drinks2 0 Map.empty aa ba = {||}"
    proof-
      have set_filter: "\<forall>aa ba. \<not> (aa = ''select'' \<and> length ba = 1) \<longrightarrow> (Set.filter
          (\<lambda>((origin, dest), t).
              origin = 0 \<and> Label t = aa \<and> length ba = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state ba 1 (I n)) Map.empty))
          (fset Simple_Drinks_Machine.drinks2)) = {}"
        apply (simp add: drinks2_def Set.filter_def)
        apply safe
        by (simp_all add: select_def)
      show ?thesis
        apply (clarify)
        apply (simp add: possible_steps_def ffilter_def)
        apply (simp add: set_filter)
        by (simp add: bot_fset_def)
    qed
    show ?thesis
      apply clarify
      apply (simp only: step_def)
      by (simp add: possible_steps_invalid)
  qed
  show ?thesis
    unfolding directly_subsumes_def anterior_context_def
    apply (rule allI)
    apply (case_tac p)
     apply (simp add: coin_subsumes_coin50)
    apply simp
    apply (case_tac a)
    apply clarify
    apply (case_tac "aa = ''select'' \<and> length ba = 1")
     apply (simp add: step_select select_posterior)
     apply (simp add: test)
     apply simp
    by (simp add: test2 coin_subsumes_coin50)
qed

\<comment> \<open> coin subsumes coin50 no matter how many times it is looped round \<close>
lemma "subsumes \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> Eq (Num n)\<rbrakk> coin coin50"
proof-
  have aux1: "(\<forall>r i. cval (medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> (Guard coin50) r) i = Some True \<longrightarrow>
           cval (medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> (Guard Simple_Drinks_Machine.coin) r) i = Some True)"
    apply (simp add: coin50_def coin_def)
    apply clarify
    apply (case_tac "cval (\<lbrakk>\<rbrakk> r) i")
     apply simp
    by simp
  have aux2: "(\<forall>i r. apply_guards (Guard coin50) (join_ir i r) \<longrightarrow>
           apply_outputs (Outputs coin50) (join_ir i r) = apply_outputs (Outputs Simple_Drinks_Machine.coin) (join_ir i r))"
    by (simp add: coin50_def coin_def)
  have medial_coin50: "medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> (Guard coin50) = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n), V (I 1) \<mapsto> Eq (Num 50)\<rbrakk>"
    apply (rule ext)
    by (simp add: coin50_def)
  have consistent_medial_coin50: "consistent \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n), V (I 1) \<mapsto> cexp.Eq (Num 50)\<rbrakk>"
    apply (simp add: consistent_def)
    apply (rule_tac x="<R 1 := Num 0, R 2 := Num n, I 1 := Num 50>" in exI)
    apply (rule allI)
    by (simp add: consistent_empty_4)
  have posterior_coin50: "posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> coin50 = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num (n+50))\<rbrakk>"
    unfolding posterior_def Let_def
    apply (simp add: medial_coin50 consistent_medial_coin50 remove_input_constraints_def)
    apply (rule ext)
    apply (simp add: coin50_def valid_def satisfiable_def)
    by auto
  have consistent_medial_coin: "consistent \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n), V (I 1) \<mapsto> cexp.Eq (Num 50)\<rbrakk>"
    apply (simp add: consistent_def)
    apply (rule_tac x="<R 1 := Num 0, R 2 := Num n, I 1 := Num 50>" in exI)
    apply (rule allI)
    by (simp add: consistent_empty_4)
  have posterior_coin: "posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n), V (I 1) \<mapsto> cexp.Eq (Num 50)\<rbrakk> Simple_Drinks_Machine.coin = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num (n+50))\<rbrakk>"
    unfolding posterior_def Let_def
    apply (simp add: medial_coin consistent_medial_coin remove_input_constraints_def)
    apply (rule ext)
    apply (simp add: coin_def valid_def satisfiable_def)
    by auto
  have aux3: "(\<forall>r i. cval (posterior (medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> (Guard coin50)) Simple_Drinks_Machine.coin r) i =
           Some True \<longrightarrow>
           cval (posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> coin50 r) i = Some True \<or>
           posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> coin50 r = Undef)"
    apply (simp only: medial_coin50 posterior_coin50 posterior_coin)
    by simp
  have aux4: "(consistent (posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> coin50) \<longrightarrow>
     consistent (posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> Simple_Drinks_Machine.coin))"
  proof-
  have consistent_medial_coin: "consistent \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk>"
      apply (simp add: consistent_def)
      apply (rule_tac x="<R 1 := Num 0, R 2 := Num n, I 1 := Num 50>" in exI)
      apply (rule allI)
      by (simp add: consistent_empty_4)
  have posterior_coin: "posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> Simple_Drinks_Machine.coin = r1_r2_true"
    unfolding posterior_def Let_def
    apply (simp add: medial_coin consistent_medial_coin remove_input_constraints_def)
    apply (rule ext)
    by (simp add: coin_def valid_def satisfiable_def)
  show ?thesis
    by (simp add: posterior_coin consistent_r1_r2_true)
qed
  show ?thesis
    unfolding subsumes_def
    using aux1 aux2 aux3 aux4
    by simp
qed
end
