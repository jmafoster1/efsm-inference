theory Simple_Drinks_Machine
imports "../Contexts" "../examples/Drinks_Machine_2" "../inference/Inference"
begin

declare One_nat_def [simp del]
declare gval.simps [simp]
declare ValueEq_def [simp]
declare ValueGt_def [simp]

definition t1 :: "transition" where
"t1 \<equiv> \<lparr>
        Label = (STR ''select''),
        Arity = 1,
        Guard = [],
        Outputs = [],
        Updates = [(R 1, (V (I 1))), (R 2, (L (Num 0)))]
      \<rparr>"

definition coin50 :: "transition" where
"coin50 \<equiv> \<lparr>
        Label = (STR ''coin''),
        Arity = 1,
        Guard = [(gexp.Eq (V (I 1)) (L (Num 50)))],
        Outputs = [(Plus (V (R 2)) (V (I 1)))],
        Updates = [(R 1, (V (R 1))),  (R 2, Plus (V (R 2)) (L (Num 50)))]
      \<rparr>"

lemma updates_coin50: "Updates coin50 = [(R 1, (V (R 1))),  (R 2, Plus (V (R 2)) (L (Num 50)))]"
  by (simp add: coin50_def)

definition coin :: "transition" where
"coin \<equiv> \<lparr>
        Label = (STR ''coin''),
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
        Label = (STR ''vend''),
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

lemma medial_coin50: "medial \<lbrakk>V (R 1) \<mapsto> {|Bc True|}, V (R 2) \<mapsto> {|Eq (Num n)|}\<rbrakk> (Guard coin50) =
                      \<lbrakk>V (R 1) \<mapsto> {|Bc True|}, V (R 2) \<mapsto> {|Eq (Num n)|}, V (I 1) \<mapsto> {|Eq (Num 50), Bc True|}\<rbrakk>"
  apply (rule ext)
  by (simp add: medial_def coin50_def List.maps_def pairs2context_def)

lemma consistent_medial_coin50: "consistent (medial \<lbrakk>V (R 1) \<mapsto> {|Bc True|}, V (R 2) \<mapsto> {|Eq (Num n)|}\<rbrakk> (Guard coin50))"
  apply (simp add: medial_coin50 consistent_def)
  apply (rule_tac x="<R 2 := Num n, I 1 := Num 50>" in exI)
  apply clarify
  apply (simp add: cval_def)
  apply (case_tac r)
     apply simp
    apply (case_tac x2)
  by auto

lemma coin50_posterior: "posterior \<lbrakk>V (R 1) \<mapsto> {|Bc True|}, V (R 2) \<mapsto> {|Eq (Num n)|}\<rbrakk> coin50 = \<lbrakk>V (R 1) \<mapsto> {|Bc True|}, V (R 2) \<mapsto> {|Eq (Num (n+50))|}\<rbrakk>"
  unfolding posterior_def posterior_separate_def Let_def
   apply (rule ext)
  apply (simp add: consistent_medial_coin50)
  apply (simp add: medial_coin50 remove_obsolete_constraints_def)
  by (simp add: coin50_def fprod_singletons)

lemma consistent_medial_coin: "consistent (medial \<lbrakk>V (R 1) \<mapsto> {|Bc True|}, V (R 2) \<mapsto> {|Eq (Num n)|}\<rbrakk> (Guard coin))"
  apply (simp add: coin_def medial_empty consistent_def)
  apply (rule_tac x="<R 2 := Num n>" in exI)
  apply (simp add: cval_def)
  apply clarify
  apply (case_tac r)
     apply simp
    apply (case_tac x2)
  by auto

lemma posterior_coin: "(posterior \<lbrakk>V (R 1) \<mapsto> {|Bc True|}, V (R 2) \<mapsto> {|Eq (Num n)|}\<rbrakk> coin) = \<lbrakk>V (R 1) \<mapsto> {|Bc True|}, V (R 2) \<mapsto> {|Bc True|}\<rbrakk>"
  unfolding posterior_def posterior_separate_def Let_def
  apply (simp add: consistent_medial_coin remove_obsolete_constraints_def)
  apply (rule ext)
  by (simp add: coin_def medial_empty fprod_singletons)

lemma medial_coin: "medial c (Guard Simple_Drinks_Machine.coin) = c"
  by (simp add: coin_def medial_empty)

lemma possible_steps_coin_50: "possible_steps Simple_Drinks_Machine.drinks2 1 r (STR ''coin'') [Num 50] = {|(2, coin50)|}"
  apply (simp add: possible_steps_alt Abs_ffilter Set.filter_def drinks2_def)
  apply safe
  by (simp_all add: select_def vend_nothing_def coin50_def)

lemma possible_steps_1_vend: "possible_steps Simple_Drinks_Machine.drinks2 1 r (STR ''vend'') [] = {|(1, vend_nothing)|}"
  apply (simp add: possible_steps_alt Abs_ffilter Set.filter_def drinks2_def)
  apply safe
  by (simp_all add: select_def coin50_def vend_nothing_def)

lemma invalid_step: "\<not> (aa = (STR ''coin'') \<and> b = [Num 50]) \<Longrightarrow>
                     \<not> (aa = (STR ''vend'') \<and> b = []) \<Longrightarrow>
                     possible_steps Simple_Drinks_Machine.drinks2 1 r aa b = {||}"
proof-
  assume premise1: "\<not> (aa = (STR ''coin'') \<and> b = [Num 50])"
  assume premise2: "\<not> (aa = (STR ''vend'') \<and> b = [])"
  have input2state: "length b = 1 \<Longrightarrow> input2state b 1 = (\<lambda>x. if x = I 1 then Some (hd b) else None)"
  proof(induct b)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a b)
    then show ?case
      apply simp
      apply (rule ext)
      by simp
  qed
  show ?thesis
    apply (simp add: possible_steps_def Abs_ffilter Set.filter_def drinks2_def)
    apply clarify
    apply (case_tac "ba = 1")
    using premise2
     apply (simp add: vend_nothing_def)
    using premise1
    apply (simp add: coin50_def)
    apply clarify
    apply (simp add: input2state)
    using premise1
    by (metis One_nat_def hd_Cons_tl length_0_conv length_Suc_conv list.sel(3) trilean.distinct(1))
qed

lemma next_step_1: "step Simple_Drinks_Machine.drinks2 1 r aa b = Some (uw, s', ux, r') \<Longrightarrow> s' = 1 \<or> s' = 2"
  apply (case_tac "aa = (STR ''coin'') \<and> b = [Num 50]")
   apply (simp add: step_def possible_steps_coin_50)
  apply (case_tac "aa = (STR ''vend'') \<and> b = []")
   apply (simp add: step_def possible_steps_1_vend)
  apply (simp only: step_def)
  using invalid_step
  by simp

lemma possible_steps_vend_fail: "ra (R 2) = Some (Num x1) \<and> x1 < 100 \<Longrightarrow> possible_steps Simple_Drinks_Machine.drinks2 2 ra (STR ''vend'') [] = {|(2, vend_fail)|}"
  apply (simp add: possible_steps_alt Abs_ffilter Set.filter_def drinks2_def)
  apply safe
  by (simp_all add: transitions)

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
    by (simp add: possible_steps_def ffilter_def set_filter)
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
  have possible_steps_coin: "length b = 1 \<Longrightarrow> possible_steps Simple_Drinks_Machine.drinks2 2 ra (STR ''coin'') b = {|(2, coin)|}"
    apply (simp add: possible_steps_alt Abs_ffilter Set.filter_def drinks2_def)
    apply safe
    by (simp_all add: transitions)
  have ra_not_num: "\<And>ra. \<forall>n. ra (R 2) \<noteq> Some (Num n) \<Longrightarrow> \<not> apply_guards (Guard vend_fail) (case_vname Map.empty (\<lambda>n. ra (R n)))"
    apply (simp add: vend_fail_def)
    apply (case_tac "ra (R 2)")
     apply simp
    apply (case_tac a)
    by auto
  have ra_not_num_2: "\<And>ra. \<forall>n. ra (R 2) \<noteq> Some (Num n) \<Longrightarrow> \<not> apply_guards (Guard Drinks_Machine.vend) (case_vname Map.empty (\<lambda>n. ra (R n)))"
    apply (simp add: Drinks_Machine.vend_def)
    apply (case_tac "ra (R 2)")
     apply simp
    apply (case_tac a)
    by auto
  have possible_steps_vend_r2_none: "\<nexists> n. ra (R 2) = Some (Num n) \<Longrightarrow> possible_steps Simple_Drinks_Machine.drinks2 2 ra (STR ''vend'') [] = {||}"
    apply (simp add: possible_steps_def Abs_ffilter Set.filter_def drinks2_def)
    apply clarify
    apply (case_tac "b = 2")
     apply simp
     apply (case_tac "ba = coin")
      apply (simp add: coin_def)
     apply (simp add: ra_not_num)
    apply (case_tac "b=3")
     apply (simp add: ra_not_num_2)
    by simp
  have set_filter_invalid: "\<not> (aa = (STR ''coin'') \<and> length b = 1) \<Longrightarrow> \<not> (aa = (STR ''vend'') \<and> b = []) \<Longrightarrow> (Set.filter
       (\<lambda>((origin, dest), t).
           origin = 2 \<and> Label t = aa \<and> length b = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) (\<lambda>n. ra (R n))))
       (fset Simple_Drinks_Machine.drinks2)) = {}"
    apply (simp add: drinks2_def Set.filter_def)
    apply safe
    by (simp_all add: transitions)
  have possible_steps_invalid: "\<not> (aa = (STR ''coin'') \<and> length b = 1) \<Longrightarrow> \<not> (aa = (STR ''vend'') \<and> b = []) \<Longrightarrow>
                      possible_steps Simple_Drinks_Machine.drinks2 2 ra aa b = {||}"
    by (simp add: possible_steps_def ffilter_def set_filter_invalid)
  have set_filter_vend_fail: "\<forall>ra x1. ra (R 2) = Some (Num x1) \<and> x1 < 100 \<longrightarrow>  (Set.filter
       (\<lambda>((origin, dest), t).
           origin = 2 \<and> Label t = (STR ''vend'') \<and> Arity t = 0 \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state [] 1 (I n)) (\<lambda>n. ra (R n))))
       (fset Simple_Drinks_Machine.drinks2)) =
    {((2, 2), vend_fail)}"
    apply (simp add: drinks2_def Set.filter_def)
    apply safe
    by (simp_all add: transitions)
  have possible_steps_vend_fail: "\<forall>ra x1. ra (R 2) = Some (Num x1) \<and> x1 < 100 \<longrightarrow> possible_steps Simple_Drinks_Machine.drinks2 2 ra (STR ''vend'') [] = {|(2, vend_fail)|}"
  apply (simp add: possible_steps_def ffilter_def)
  using set_filter_vend_fail
  by auto
  have set_filter_vend: "\<forall>ra x1. ra (R 2) = Some (Num x1) \<and> x1 \<ge> 100 \<longrightarrow> (Set.filter
            (\<lambda>((origin, dest), t).
                origin = 2 \<and> Label t = (STR ''vend'') \<and> Arity t = 0 \<and> apply_guards (Guard t) (case_vname Map.empty (\<lambda>n. ra (R n))))
            (fset Simple_Drinks_Machine.drinks2)) =
         {((2,3), Drinks_Machine.vend)}"
    apply (simp add: drinks2_def Set.filter_def)
    apply safe
    by (simp_all add: transitions)
  have possible_steps_vend: "\<forall>ra x1. ra (R 2) = Some (Num x1) \<and> x1 \<ge> 100 \<longrightarrow> possible_steps Simple_Drinks_Machine.drinks2 2 ra (STR ''vend'') [] = {|(3, Drinks_Machine.vend)|}"
    apply (simp add: possible_steps_def ffilter_def)
    using set_filter_vend
    by simp
  show ?thesis
    using premise
    apply (simp add: step_def)
    apply (case_tac "aa = (STR ''coin'') \<and> length b = 1")
     apply clarify
     apply (simp add: possible_steps_coin)
    apply (case_tac "aa = (STR ''vend'') \<and> b = []")
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
    using possible_steps_vend
    by simp
qed

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

\<comment> \<open> coin subsumes coin50 no matter how many times it is looped round \<close>
lemma "subsumes coin \<lbrakk>V (R 1) \<mapsto> {|Bc True|}, V (R 2) \<mapsto> {|Eq (Num n)|}\<rbrakk> coin50"
  unfolding subsumes_def
  apply standard
   apply (simp add: transitions)
  apply standard
   apply (simp add: transitions)
  apply standard
   apply (simp add: transitions)
  apply standard
   apply (simp add: medial_coin50 medial_coin)
  apply standard
   apply (simp add: transitions)
  apply standard
   apply (rule_tac x="[Num 50]" in exI)
   apply (rule_tac x="<R 2 := Num 50>" in exI)
   apply (simp add: transitions)
  apply standard
   apply (simp add: coin_def)
   apply (simp add: posterior_def posterior_separate_def Let_def)
   apply (simp add: consistent_medial_coin50)
   apply (simp add: medial_coin50)
   apply (simp add: updates_coin50 remove_obsolete_constraints_def medial_coin50 fprod_def)
  apply clarify
  apply (simp add: posterior_coin consistent_def)
  apply (rule_tac x="<>" in exI)
  apply clarify
  apply (simp add: cval_def)
  apply (case_tac r)
     apply simp
    apply (case_tac x2)
  by auto
end
