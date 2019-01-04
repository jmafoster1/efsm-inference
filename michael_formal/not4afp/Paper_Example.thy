theory Paper_Example
imports Inference SelectionStrategies FSet_Utils
begin

definition select :: transition where
  "select = \<lparr>
              Label = ''select'',
              Arity = 1,
              Guard = [],
              Outputs = [],
              Updates = [(R 1, V (I 1))]
            \<rparr>"

definition coin50 :: transition where
  "coin50 = \<lparr>
              Label = ''coin'',
              Arity = 1,
              Guard = [gexp.Eq (V (I 1)) (L (Num 50))],
              Outputs = [L (Num 50)],
              Updates = [(R 2, L (Num 50))]
            \<rparr>"

definition coin :: transition where
  "coin = \<lparr>
              Label = ''coin'',
              Arity = 1,
              Guard = [],
              Outputs = [Plus (V (R 2)) (V (I 1))],
              Updates = [(R 2, Plus (V (R 2)) (V (I 1)))]
            \<rparr>"

lemma guard_coin: "Guard coin = []"
  by (simp add: coin_def)

definition vend_fail :: transition where
  "vend_fail = \<lparr>
              Label = ''vend'',
              Arity = 0,
              Guard = [GExp.Lt (V (R 2)) (L (Num 100))],
              Outputs = [],
              Updates = []
            \<rparr>"

definition vend_success :: transition where
  "vend_success = \<lparr>
              Label = ''vend'',
              Arity = 0,
              Guard = [GExp.Ge (V (R 2)) (L (Num 100))],
              Outputs = [(V (R 1))],
              Updates = []
            \<rparr>"

definition select_update :: transition where
  "select_update = \<lparr>
              Label = ''select'',
              Arity = 1,
              Guard = [],
              Outputs = [],
              Updates = [(R 1, V (I 1)), (R 2, L (Num 0))]
            \<rparr>"

lemmas transitions = select_def coin_def coin50_def vend_fail_def vend_success_def select_update_def

declare One_nat_def [simp del]

lemma select_update_posterior: "posterior \<lbrakk>\<rbrakk> select_update = \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> Eq (Num 0)\<rbrakk>"
proof-
  show ?thesis
    unfolding posterior_def Let_def
    apply (rule ext)
    by (simp add: transitions remove_input_constraints_def)
qed

lemma select_posterior: "posterior \<lbrakk>\<rbrakk> select = \<lbrakk>V (R 1) \<mapsto> Bc True\<rbrakk>"
  unfolding posterior_def Let_def
  apply (rule ext)
  by (simp add: transitions remove_input_constraints_def)

lemma coin50_posterior: "posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True\<rbrakk> coin50 = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> Eq (Num 50)\<rbrakk>"
  unfolding posterior_def Let_def
  apply (rule ext)
  apply (simp add: transitions remove_input_constraints_def)
  apply (simp add: consistent_def)
  apply (rule_tac x="<I 1 := Num 50>" in exI)
  apply clarify
  by (simp add: consistent_empty_4)

definition drinks_before :: transition_matrix where
  "drinks_before = {|((0, 1), select), ((1, 2), coin50), ((2, 2), coin), ((2, 2), vend_fail), ((2, 3), vend_success)|}"

definition drinks_after :: transition_matrix where
  "drinks_after = {|((0, 1), select_update), ((1, 1), coin), ((1, 1), vend_fail), ((1, 3), vend_success)|}"

definition merge_1_2 :: transition_matrix where
  "merge_1_2 = {|((0, 1), select), ((1, 1), coin50), ((1, 1), coin), ((1, 1), vend_fail), ((1, 3), vend_success)|}"

lemma merge_1_2: "merge_states 1 2 drinks_before = merge_1_2"
  by (simp add: merge_states_def drinks_before_def merge_1_2_def merge_states_aux_def)

definition merge_1_2_update :: transition_matrix where
  "merge_1_2_update = {|((0, 1), select_update), ((1, 1), coin50), ((1, 1), coin), ((1, 1), vend_fail), ((1, 3), vend_success)|}"

definition update_mapping :: "nat \<Rightarrow> nat" where
  "update_mapping x = x"

lemma possible_steps_drinks_before_select: "length b = 1 \<Longrightarrow> possible_steps drinks_before 0 r ''select'' b = {|(1, select)|}"
proof-
  assume premise: "length b = 1"
  have set_filter: "(Set.filter
       (\<lambda>((origin, dest), t).
           origin = 0 \<and>
           Label t = ''select'' \<and> length b = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) (\<lambda>n. r (R n))))
       (fset drinks_before)) = {((0, 1), select)}"
    apply (simp add: Set.filter_def drinks_before_def)
    apply safe
    by (simp_all add: transitions premise)
  show ?thesis
    by (simp add: possible_steps_def ffilter_def set_filter)
qed

lemma possible_steps_merge_1_2_select: "length b = 1 \<Longrightarrow> possible_steps merge_1_2 0 r ''select'' b = {|(1, select)|}"
proof-
  assume premise: "length b = 1"
  have set_filter: "(Set.filter
       (\<lambda>((origin, dest), t).
           origin = 0 \<and>
           Label t = ''select'' \<and> length b = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) (\<lambda>n. r (R n))))
       (fset merge_1_2)) =
    {((0, 1), select)}"
    apply (simp add: merge_1_2_def Set.filter_def)
    apply safe
    by (simp_all add: transitions premise)
  show ?thesis
    by (simp add: possible_steps_def ffilter_def set_filter)
qed

lemma possible_steps_merge_1_2_update_select: "length b = 1 \<Longrightarrow> possible_steps merge_1_2_update 0 r ''select'' b = {|(1, select_update)|}"
proof-
  assume premise: "length b = 1"
  have set_filter: "(Set.filter
       (\<lambda>((origin, dest), t).
           origin = 0 \<and>
           Label t = ''select'' \<and> length b = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) (\<lambda>n. r (R n))))
       (fset merge_1_2_update)) =
    {((0, 1), select_update)}"
    apply (simp add: Set.filter_def merge_1_2_update_def)
    apply safe
    by (simp_all add: transitions premise)
  show ?thesis
    by (simp add: possible_steps_def ffilter_def set_filter)
qed

lemma drinks_before_step_0_invalid: "\<not> (aa = ''select'' \<and> length b = 1) \<Longrightarrow>
        nondeterministic_step drinks_before 0 Map.empty aa b = None"
proof-
  assume premise: "\<not> (aa = ''select'' \<and> length b = 1)"
  have set_filter: "(Set.filter
           (\<lambda>((origin, dest), t).
               origin = 0 \<and> Label t = aa \<and> length b = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) Map.empty))
           (fset drinks_before)) = {}"
    apply (simp add: Set.filter_def drinks_before_def)
    apply safe
    using premise
    by (simp_all add: transitions)
  show ?thesis
    by (simp add: nondeterministic_step_def possible_steps_def ffilter_def set_filter)
qed

lemma possible_steps_drinks_before_coin_50: "possible_steps drinks_before 1 r ''coin'' [Num 50] = {|(2, coin50)|}"
proof-
  have set_filter: "(Set.filter
       (\<lambda>((origin, dest), t).
           origin = 1 \<and>
           Label t = ''coin'' \<and> Suc 0 = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state [Num 50] 1 (I n)) (\<lambda>n. r (R n))))
       (fset drinks_before)) =
    {((1, 2), coin50)}"
    apply (simp add: drinks_before_def Set.filter_def)
    apply safe
    by (simp_all add: transitions)
  have abs_fset: "Abs_fset {((1, 1), coin50), ((1, 1), coin)} = {|((1, 1), coin50), ((1, 1), coin)|}"
    by (metis finsert.rep_eq fset_inverse fset_simps(1))
   show ?thesis
     by (simp add: possible_steps_def ffilter_def set_filter abs_fset)
 qed

lemma drinks_before_1_invalid: "\<not> (aa = ''coin'' \<and> b = [Num 50]) \<Longrightarrow> nondeterministic_step drinks_before 1 r aa b = None"
proof-
  assume premise: "\<not>(aa = ''coin'' \<and> b = [Num 50])"
  have set_filter: "(Set.filter
           (\<lambda>((origin, dest), t).
               origin = 1 \<and>
               Label t = aa \<and> length b = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) (\<lambda>n. r (R n))))
           (fset drinks_before)) = {}"
    using premise
    apply (simp add: drinks_before_def Set.filter_def coin50_def)
    by (metis One_nat_def input2state.simps(2) length_0_conv length_Suc_conv option.inject)
  show ?thesis
    by (simp add: nondeterministic_step_def possible_steps_def ffilter_def set_filter)
qed

lemma merge_1_2_invalid_coin_input: "aa = ''coin'' \<Longrightarrow> length b \<noteq> 1 \<Longrightarrow> nondeterministic_step merge_1_2 1 <R 1 := d> ''coin'' b = None"
proof-
  assume premise1: "aa = ''coin''"
  assume premise2: "length b \<noteq> 1"
  have set_filter: "(Set.filter
           (\<lambda>((origin, dest), t).
               origin = 1 \<and>
               Label t = ''coin'' \<and>
               length b = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) (\<lambda>n. if n = 1 then Some d else None)))
           (fset merge_1_2)) = {}"
    using premise1 premise2
    apply (simp add: merge_1_2_def Set.filter_def)
    apply safe
    by (simp_all add: transitions)
  show ?thesis
    by (simp add: nondeterministic_step_def possible_steps_def ffilter_def set_filter)
qed

lemma merge_1_2_possible_steps_coin_not_50: "aa = ''coin'' \<Longrightarrow>
    length b = 1 \<Longrightarrow>
    b \<noteq> [Num 50] \<Longrightarrow>
    possible_steps merge_1_2 1 <R 1 := d> ''coin'' b = {|(1, coin)|}"
proof-
  assume premise1: "aa = ''coin''"
  assume premise2: "length b = 1"
  assume premise3: "b \<noteq> [Num 50]"
  have set_filter: "(Set.filter
       (\<lambda>((origin, dest), t).
           origin = 1 \<and>
           Label t = ''coin'' \<and> length b = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) (\<lambda>n. <R 1 := d> (R n))))
       (fset merge_1_2)) = {((1, 1), coin)}"
    using premise1 premise2 premise3
    apply (simp add: merge_1_2_def Set.filter_def)
    apply safe
           apply (simp_all add: transitions)
    by (metis One_nat_def input2state.simps(2) length_0_conv length_Suc_conv option.inject)
  show ?thesis
    by (simp add: possible_steps_def ffilter_def set_filter)
qed

lemma merge_1_2_update_possible_steps_coin_50: "possible_steps merge_1_2_update 1 <R 1 := d, R 2 := Num n> ''coin'' [Num 50] = {|(1, coin50), (1, coin)|}"
proof-
  have set_filter: "(Set.filter
       (\<lambda>((origin, dest), t).
           origin = 1 \<and>
           Label t = ''coin'' \<and>
           Suc 0 = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state [Num 50] 1 (I n)) (\<lambda>na. <R 1 := d, R 2 := Num n> (R na))))
       (fset merge_1_2_update)) = {((1, 1), coin), ((1, 1), coin50)}"
    apply (simp add: Set.filter_def merge_1_2_update_def)
    apply safe
    by (simp_all add: transitions)
  have abs_fset: "Abs_fset {((1, 1), coin), ((1, 1), coin50)} = {|((1, 1), coin), ((1, 1), coin50)|}"
    by (metis finsert.rep_eq fset_inverse fset_simps(1))
  show ?thesis
    apply (simp add: possible_steps_def ffilter_def set_filter abs_fset)
    by auto
qed

lemma possible_steps_drinks_before_coin: "length b = 1 \<Longrightarrow> possible_steps drinks_before 2 r1 ''coin'' b = {|(2, coin)|}"
proof-
  assume premise: "length b = 1"
  have set_filter: "(Set.filter
       (\<lambda>((origin, dest), t).
           origin = 2 \<and>
           Label t = ''coin'' \<and> length b = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) (\<lambda>n. r1 (R n))))
       (fset drinks_before)) = {((2, 2), coin)}"
    apply (simp add: drinks_before_def Set.filter_def)
    apply safe
    by (simp_all add: transitions premise)
  show ?thesis
    by (simp add: possible_steps_def ffilter_def set_filter)
qed

lemma possible_steps_merge_1_2_update_coin: "length b = 1 \<Longrightarrow> (1, coin) |\<in>| possible_steps merge_1_2_update 1 r2 ''coin'' b"
proof-
  assume premise: "length b = 1"
  have set_filter: "((1, 1), coin) \<in> (Set.filter
       (\<lambda>((origin, dest), t).
           origin = 1 \<and>
           Label t = ''coin'' \<and> length b = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) (\<lambda>n. r2 (R n))))
       (fset merge_1_2_update))"
    apply (simp add: merge_1_2_update_def Set.filter_def)
    apply safe
    by (simp_all add: transitions premise)
  show ?thesis
    apply (simp add: possible_steps_def ffilter_def)
    using set_filter
    by (metis (no_types, lifting) case_prod_conv ffilter.rep_eq fimage_eqI fset_inverse notin_fset)
qed

lemma nondeterministic_step_drinks_before_invalid_step_2: " \<not> (aa = ''coin'' \<and> length b = 1) \<Longrightarrow>
       \<not> (aa = ''vend'' \<and> b = []) \<Longrightarrow> nondeterministic_step drinks_before 2 r1 aa b = None"
proof-
  assume premise1:  "\<not> (aa = ''coin'' \<and> length b = 1)"
  assume premise2: "\<not> (aa = ''vend'' \<and> b = [])"
  have set_filter: "(Set.filter
           (\<lambda>((origin, dest), t).
               origin = 2 \<and>
               Label t = aa \<and> length b = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) (\<lambda>n. r1 (R n))))
           (fset drinks_before)) = {}"
    using premise1 premise2
    apply (simp add: Set.filter_def drinks_before_def)
    apply safe
    by (simp_all add: transitions)
  show ?thesis
    by (simp add: nondeterministic_step_def possible_steps_def ffilter_def set_filter)
qed

lemma impossible_steps_drinks_before_vend: "\<nexists>n. r (R 2) = Some (Num n) \<Longrightarrow> nondeterministic_step drinks_before 2 r ''vend'' i = None"
proof-
  assume premise: "\<nexists>n. r (R 2) = Some (Num n)"
  have set_filter: "(Set.filter
       (\<lambda>((origin, dest), t).
           origin = 2 \<and>
           Label t = ''vend'' \<and> length i = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))))
       (fset drinks_before)) = {}"
    using premise
    apply (simp add: Set.filter_def drinks_before_def)
    apply safe
      apply (simp add: transitions)
     apply (simp add: transitions)
     apply (metis MaybeBoolInt.elims option.simps(3))
     apply (simp add: transitions)
    apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some (Num 100)) (r (R 2))")
     apply simp
    apply simp
    by (metis MaybeBoolInt.elims option.simps(3))
  show ?thesis
    by (simp add: nondeterministic_step_def possible_steps_def ffilter_def set_filter)
qed

lemma drinks_before_vend_fail: "r (R 2) = Some (Num x1) \<Longrightarrow> x1 < 100 \<Longrightarrow> possible_steps drinks_before 2 r ''vend'' [] = {|(2, vend_fail)|}"
proof-
  assume premise1: "r (R 2) = Some (Num x1)"
  assume premise2: "x1 < 100"
  have set_filter: "(Set.filter
       (\<lambda>((origin, dest), t).
           origin = 2 \<and> Label t = ''vend'' \<and> Arity t = 0 \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state [] 1 (I n)) (\<lambda>n. r (R n))))
       (fset drinks_before)) = {((2, 2), vend_fail)}"
    using premise1 premise2
    apply (simp add: Set.filter_def drinks_before_def)
    apply safe
    by (simp_all add: transitions)
  show ?thesis
    by (simp add: possible_steps_def ffilter_def set_filter)
qed

lemma drinks_before_vend_success: "r (R 2) = Some (Num x1) \<Longrightarrow> x1 \<ge> 100 \<Longrightarrow> possible_steps drinks_before 2 r ''vend'' [] = {|(3, vend_success)|}"
proof-
  assume premise1: "r (R 2) = Some (Num x1)"
  assume premise2: "x1 \<ge> 100"
  have set_filter: "(Set.filter
       (\<lambda>((origin, dest), t).
           origin = 2 \<and> Label t = ''vend'' \<and> Arity t = 0 \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state [] 1 (I n)) (\<lambda>n. r (R n))))
       (fset drinks_before)) = {((2, 3), vend_success)}"
    using premise1 premise2
    apply (simp add: Set.filter_def drinks_before_def)
    apply safe
    by (simp_all add: transitions)
  show ?thesis
    by (simp add: possible_steps_def ffilter_def set_filter)
qed

lemma merge_1_2_update_vend_fail: "r (R 2) = Some (Num x1) \<Longrightarrow> x1 < 100 \<Longrightarrow> possible_steps merge_1_2_update 1 r ''vend'' [] = {|(1, vend_fail)|}"
  proof-
  assume premise1: "r (R 2) = Some (Num x1)"
  assume premise2: "x1 < 100"
  have set_filter: "(Set.filter
       (\<lambda>((origin, dest), t).
           origin = 1 \<and> Label t = ''vend'' \<and> Arity t = 0 \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state [] 1 (I n)) (\<lambda>n. r (R n))))
       (fset merge_1_2_update)) = {((1, 1), vend_fail)}"
    using premise1 premise2
    apply (simp add: Set.filter_def merge_1_2_update_def)
    apply safe
    by (simp_all add: transitions)
  show ?thesis
    by (simp add: possible_steps_def ffilter_def set_filter)
qed

lemma merge_1_2_update_vend_success: "r (R 2) = Some (Num x1) \<Longrightarrow> x1 \<ge> 100 \<Longrightarrow> possible_steps merge_1_2_update 1 r ''vend'' [] = {|(3, vend_success)|}"
  proof-
  assume premise1: "r (R 2) = Some (Num x1)"
  assume premise2: "x1 \<ge> 100"
  have set_filter: "(Set.filter
       (\<lambda>((origin, dest), t).
           origin = 1 \<and> Label t = ''vend'' \<and> Arity t = 0 \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state [] 1 (I n)) (\<lambda>n. r (R n))))
       (fset merge_1_2_update)) = {((1, 3), vend_success)}"
    using premise1 premise2
    apply (simp add: merge_1_2_update_def Set.filter_def)
    apply safe
    by (simp_all add: transitions)
  show ?thesis
    by (simp add: possible_steps_def ffilter_def set_filter)
qed

lemma drinks_before_ends_at_3: "nondeterministic_step drinks_before 3 r aa b = None"
proof-
  have set_filter: "(Set.filter
           (\<lambda>((origin, dest), t).
               origin = 3 \<and>
               Label t = aa \<and> length b = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) (\<lambda>n. r (R n))))
           (fset drinks_before)) = {}"
    by (simp add: drinks_before_def Set.filter_def)
  show ?thesis
    by (simp add: nondeterministic_step_def possible_steps_def ffilter_def set_filter)
qed

definition update_before :: "nat \<Rightarrow> nat" where
  "update_before x = (if x = 2 then 1 else x)"

lemma simulation_2_1: "\<forall>r. nondeterministic_simulates_trace merge_1_2_update drinks_before 1 2 r r lst update_before"
proof (induct lst)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  case (Cons a lst)
  then show ?case
    apply (case_tac a)
    apply simp
     apply (rule allI)
    apply (case_tac "aa = ''coin'' \<and> length b = 1")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: update_before_def)
        apply (simp add: nondeterministic_step_def possible_steps_drinks_before_coin)
    using possible_steps_merge_1_2_update_coin
       apply blast
      apply simp
     apply simp
    apply (case_tac "aa = ''vend'' \<and> b = []")
     defer
     apply (rule nondeterministic_simulates_trace.step_none)
    using nondeterministic_step_drinks_before_invalid_step_2
     apply blast
    apply simp
    apply (case_tac "r (R 2)")
     apply (rule nondeterministic_simulates_trace.step_none)
     apply (simp add: impossible_steps_drinks_before_vend)
    apply (case_tac aaa)
     defer
     apply (rule nondeterministic_simulates_trace.step_none)
     apply (simp add: impossible_steps_drinks_before_vend)
    apply clarify
    apply simp
    apply (case_tac "x1 < 100")
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: update_before_def)
        apply (simp add: nondeterministic_step_def drinks_before_vend_fail)
       apply (simp add: merge_1_2_update_vend_fail)
      apply simp
     apply (simp add: vend_fail_def)
    apply (rule nondeterministic_simulates_trace.step_some)
        apply (simp add: update_before_def)
       apply (simp add: nondeterministic_step_def drinks_before_vend_success)
      apply (simp add: merge_1_2_update_vend_success)
     apply simp
    apply (simp add: vend_success_def)
    apply (case_tac lst)
     apply (simp add: nondeterministic_simulates_trace.base)
    apply simp
    apply clarify
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: drinks_before_ends_at_3)
  qed

lemma simulation_1_1: "nondeterministic_simulates_trace merge_1_2_update drinks_before 1 1 <R 1 := d, R 2 := Num 0> <R 1 := d> ((aa, b) # list) update_before"
proof-
  have choice_coin50_coin: "(\<exists>a b. a = 1 \<and> b = coin50 \<or> a = 1 \<and> b = coin)"
    by auto
  have coin50_updates: "(EFSM.apply_updates (Updates coin50)
       (case_vname (\<lambda>n. if n = 1 then Some (Num 50) else input2state [] (1 + 1) (I n)) (\<lambda>n. if n = 1 then Some d else None)) <R 1 := d>) = 
        <R 1 := d, R 2 := Num 50>"
    apply (rule ext)
    by (simp add: coin50_def)
  have coin50_updates_2: "(EFSM.apply_updates (Updates coin50) (\<lambda>x. case x of I n \<Rightarrow> input2state [Num 50] 1 (I n) | R n \<Rightarrow> <R 1 := d, R 2 := Num 0> (R n))
       <R 1 := d, R 2 := Num 0>) = <R 1 := d, R 2 := Num 50>"
    apply (rule ext)
    by (simp add: coin50_def)
  have set_filter: "\<forall>b d. (Set.filter
            (\<lambda>((origin, dest), t).
                origin = 1 \<and>
                Label t = ''vend'' \<and>
                length b = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) (\<lambda>n. if n = 1 then Some d else None)))
            (fset merge_1_2)) = {}"
    apply (simp add: merge_1_2_def Set.filter_def)
    apply safe
    by (simp_all add: transitions)
  show ?thesis
    apply (case_tac "aa = ''coin'' \<and> b = [Num 50]")
     prefer 2
     apply (rule nondeterministic_simulates_trace.step_none)
    using drinks_before_1_invalid
    apply auto[1]
    apply (rule nondeterministic_simulates_trace.step_some)
        apply (simp add: update_before_def)
       apply (simp add: nondeterministic_step_def possible_steps_drinks_before_coin_50)
      apply (simp add: nondeterministic_step_def merge_1_2_update_possible_steps_coin_50 choice_coin50_coin)
      apply auto[1]
     apply simp
    apply (simp add: coin50_updates coin50_updates_2)
    by (simp add: simulation_2_1)
qed

lemma simulation_0_0: "nondeterministic_simulates_trace merge_1_2_update drinks_before 0 0 Map.empty Map.empty ((aa, b) # t) update_before"
proof-
  have select_updates: "length b = 1 \<Longrightarrow> (EFSM.apply_updates (Updates select) (case_vname (\<lambda>n. input2state b 1 (I n)) Map.empty) Map.empty) = <R 1 := hd b>"
    apply (rule ext)
    by (simp add: hd_input2state select_def)
  have select_update_updates: "length b = 1 \<Longrightarrow> (\<lambda>x. if x = R 1 then aval (snd (R 1, V (I 1))) (case_vname (\<lambda>n. input2state b 1 (I n)) Map.empty)
          else EFSM.apply_updates [(R 2, L (Num 0))] (case_vname (\<lambda>n. input2state b 1 (I n)) Map.empty) Map.empty x) = <R 1 := hd b, R 2 := Num 0>"
    apply (rule ext)
    by (simp add: hd_input2state)
  show ?thesis
  apply (case_tac "aa = ''select'' \<and> length b = 1")
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: update_before_def)
        apply (simp add: nondeterministic_step_def possible_steps_drinks_before_select)
       apply (simp add: nondeterministic_step_def possible_steps_merge_1_2_update_select transitions)
      apply simp
     defer
     apply (rule nondeterministic_simulates_trace.step_none)
     apply (simp add: drinks_before_step_0_invalid)
    apply (simp add: select_updates select_update_updates)
    apply (case_tac t)
     apply (simp add: nondeterministic_simulates_trace.base)
    apply (case_tac a)
    by (simp add: simulation_1_1)
qed

lemma simulation_aux: "nondeterministic_simulates_trace merge_1_2_update drinks_before 0 0 Map.empty Map.empty t update_before"
proof (induct t)
case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  case (Cons a t)
  then show ?case
    apply (case_tac a)
    apply simp
    by (simp add: simulation_0_0)
qed

lemma simulation: "nondeterministic_simulates merge_1_2_update drinks_before update_before"
  apply (simp add:nondeterministic_simulates_def)
  apply (rule allI)
  by (simp add: simulation_aux)

lemma score: "(score drinks_before naive_score) = {|(0, 2, 3), (0, 1, 3), (1, 1, 2), (0, 0, 3), (0, 0, 2), (0, 0, 1)|}"
proof-
  have set_filter: "(Set.filter (\<lambda>(x, y). x < y) (fset (all_pairs (S drinks_before)))) = {(2, 3), (1, 3), (1, 2), (0, 3), (0, 2), (0, 1)}"
    apply (simp add: S_def drinks_before_def all_pairs_def Set.filter_def)
    by auto
  have ffilter: "ffilter (\<lambda>(x, y). x < y) (all_pairs (S drinks_before)) = {|(2, 3), (1, 3), (1, 2), (0, 3), (0, 2), (0, 1)|}"
    apply (simp add: ffilter_def set_filter)
    by (metis finsert.rep_eq fset_inverse fset_simps(1))
  have outgoing_transitions_2: "Set.filter (\<lambda>((origin, dest), t). origin = 2) (fset drinks_before) = {((2, 2), coin), ((2, 2), vend_fail), ((2, 3), vend_success)}"
    apply (simp add: drinks_before_def Set.filter_def)
    apply safe
    by (simp_all add: transitions)
  have abs_fset_2: "Abs_fset {((2, 2), coin), ((2, 2), vend_fail), ((2, 3), vend_success)} = {|((2, 2), coin), ((2, 2), vend_fail), ((2, 3), vend_success)|}"
    by (metis finsert.rep_eq fset_inverse fset_simps(1))
  have outgoing_transitions_3: "Set.filter (\<lambda>((origin, dest), t). origin = 3) (fset drinks_before) = {}"
    apply (simp add: drinks_before_def Set.filter_def)
    apply safe
    by (simp_all add: transitions)
  have outgoing_transitions_1: "Set.filter (\<lambda>((origin, dest), t). origin = 1) (fset drinks_before) = {((1, 2), coin50)}"
    apply (simp add: drinks_before_def Set.filter_def)
    apply safe
    by (simp_all add: transitions)
  have outgoing_transitions_0: "Set.filter (\<lambda>((origin, dest), t). origin = 0) (fset drinks_before) = {((0, 1), select)}"
    apply (simp add: drinks_before_def Set.filter_def)
    apply safe
    by (simp_all add: transitions)
  have naive_score_1_2: "naive_score {|coin50|} {|coin, vend_fail, vend_success|} = 1"
    proof-
      have abs_fset: "(Abs_fset {(coin50, coin), (coin50, vend_fail), (coin50, vend_success)}) = {|(coin50, coin), (coin50, vend_fail), (coin50, vend_success)|}"
        by (metis finsert.rep_eq fset_inverse fset_simps(1))
      have filter: "{(x, y). Label x = Label y \<and> Arity x = Arity y} \<inter> {(coin50, coin), (coin50, vend_fail), (coin50, vend_success)} = {(coin50, coin)}"
        by (simp add: transitions)
      show ?thesis
        by (simp add: naive_score_def fprod_def abs_fset filter)
    qed
    have naive_score_0_2: "naive_score {|select|} {|coin, vend_fail, vend_success|} = 0"
    proof-
      have abs_fset: "Abs_fset {(select, coin), (select, vend_fail), (select, vend_success)} = {|(select, coin), (select, vend_fail), (select, vend_success)|}"
        by (metis finsert.rep_eq fset_inverse fset_simps(1))
      show ?thesis
        apply (simp add: naive_score_def fprod_def abs_fset)
        by (simp add: transitions)
    qed
    have naive_score_0_1: "naive_score {|select|} {|coin50|} = 0"
      by (simp add: naive_score_def fprod_def transitions)
  show ?thesis
    apply (simp add: score_def ffilter)
    apply (simp add: outgoing_transitions_def ffilter_def)
    apply (simp add: outgoing_transitions_2 abs_fset_2)
    apply (simp add: outgoing_transitions_3)
    apply (simp add: outgoing_transitions_1)
    apply (simp add: outgoing_transitions_0)
    by (simp add: naive_score_empty naive_score_1_2 naive_score_0_1 naive_score_0_2)
qed

lemma no_choice_vend_fail_vend_success: "\<not>choice vend_fail vend_success"
  by (simp add: choice_def transitions)

lemma no_choice_coin_vend_success: "\<not>choice coin vend_success"
  by (simp add: choice_def transitions)

lemma no_choice_coin50_vend_success: "\<not>choice coin50 vend_success"
  by (simp add: choice_def transitions)

lemma no_choice_vend_fail_coin: "\<not>choice vend_fail coin"
  by (simp add: choice_def transitions)

lemma no_choice_vend_fail_coin50: "\<not>choice vend_fail coin50"
  by (simp add: choice_def transitions)

lemma no_choice_coin_vend_fail: "\<not>choice coin vend_fail"
  by (simp add: choice_def transitions)

lemma no_choice_coin50_vend_fail: "\<not>choice coin50 vend_fail"
  by (simp add: choice_def transitions)

lemma choice_coin50_coin: "choice coin50 coin"
  apply (simp add: choice_def transitions)
  by auto

lemma coin50_gt_coin: "coin50 > coin"
  by (simp add: transitions less_transition_ext_def)

lemmas choices = choice_symmetry choice_coin50_coin no_choice_coin50_vend_fail no_choice_coin_vend_fail no_choice_vend_fail_vend_success no_choice_coin_vend_success no_choice_coin50_vend_success no_choice_vend_fail_coin no_choice_vend_fail_coin50

lemma nondeterministic_pairs: "nondeterministic_pairs merge_1_2 = {|(1, (1, 1), coin, coin50)|}"
proof-
    have card1: "card {(1, coin50), (1, coin), (1, vend_fail), (3, vend_success)} = 4"
      by (simp add: transitions)
    have minus_1: "{|(1, coin), (1, vend_fail), (3, vend_success)|} |-| {|(1, coin50)|} = {|(1, coin), (1, vend_fail), (3, vend_success)|}"
      by (simp add: transitions)
    have minus_2: "{|(1, coin50), (1, coin), (1, vend_fail), (3, vend_success)|} |-| {|(1, coin)|} = {|(1, coin50), (1, vend_fail), (3, vend_success)|}"
      apply (simp add: transitions)
      by auto
    have minus_3: "{|(1, coin50), (1, coin), (1, vend_fail), (3, vend_success)|} |-| {|(1, vend_fail)|} = {|(1, coin50), (1, coin), (3, vend_success)|}"
      apply (simp add: transitions)
      by auto
    have minus_4: "{|(1, coin50), (1, coin), (1, vend_fail), (3, vend_success)|} |-| {|(3, vend_success)|} = {|(1, coin50), (1, coin), (1, vend_fail)|}"
      apply (simp add: transitions)
      by auto
  have state_nondeterminism:  "state_nondeterminism 1 {|(1, coin50), (1, coin), (1, vend_fail), (3, vend_success)|} = {|
   (1, (1, 3), vend_fail, vend_success),
   (1, (1, 3), coin,    vend_success),
   (1, (1, 3), coin50,    vend_success),
   (1, (1, 1), vend_fail,    coin),
   (1, (1, 1), vend_fail,    coin50),
   (1, (1, 1), coin,    vend_fail),
   (1, (1, 1), coin,    coin50),
   (1, (1, 1), coin50,    vend_fail),
   (1, (1, 1), coin50,    coin)|}"
    apply (simp add: state_nondeterminism_def card1)
    apply (simp only: minus_1 minus_2 minus_3 minus_4)
    apply (simp add: fimage_def fset_both_sides Abs_fset_inverse)
    by auto
  show ?thesis
    apply (simp add: nondeterministic_pairs_def)
    apply (simp add: S_def merge_1_2_def)
    apply (simp add: outgoing_transitions_def Set.filter_def fimage_def)
    apply (simp add: ffilter_def state_nondeterminism)
    apply (simp add: fset_both_sides Abs_fset_inverse Set.filter_def)
    apply safe
                        apply (simp_all add: choices)
    using coin50_gt_coin choice_coin50_coin choice_symmetry by auto
qed

lemma coin_doesnt_exit_1_drinks_before: "\<not>exits_state drinks_before coin 1"
proof-
  have set_filter: "Set.filter (\<lambda>((from', to), t'). from' = 1 \<and> t' = coin) (fset drinks_before) = {}"
    apply (simp add: drinks_before_def Set.filter_def)
    apply safe
    by (simp_all add: transitions)
  show ?thesis
    by (simp add: exits_state_def ffilter_def set_filter)
qed

lemma coin50_exits_1_drinks_before: "exits_state drinks_before coin50 1"
proof-
  have set_filter: "Set.filter (\<lambda>((from', to), t'). from' = 1 \<and> t' = coin50) (fset drinks_before) = {((1, 2), coin50)}"
    apply (simp add: drinks_before_def Set.filter_def)
    apply safe
    by (simp_all add: transitions)
  show ?thesis
    by (simp add: exits_state_def ffilter_def set_filter)
qed

lemma select_first: "\<not> (aa = ''select'' \<and> length b = 1) \<Longrightarrow> \<not>gets_us_to 1 merge_1_2_update 0 Map.empty ((aa, b) # p)"
      proof-
        assume premise: "\<not> (aa = ''select'' \<and> length b = 1)"
        have set_filter: "(Set.filter
                (\<lambda>((origin, dest), t).
                    origin = 0 \<and>
                    Label t = aa \<and> length b = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) Map.empty))
                (fset merge_1_2_update)) = {}"
          using premise
          apply (simp add: Set.filter_def merge_1_2_update_def)
          apply safe
          by (simp_all add: transitions)
      show ?thesis
        apply safe
        apply (rule gets_us_to.cases)
           apply simp
          apply simp
         apply clarify
         apply (simp add: step_def possible_steps_def ffilter_def set_filter)
        apply clarify
        by (simp add: step_def possible_steps_def ffilter_def set_filter)
    qed

lemma no_subsumption_empty: "\<not> subsumes \<lbrakk>\<rbrakk> coin coin50"
proof-
  have violation: "(\<exists>i r. satisfies_context r \<lbrakk>\<rbrakk> \<and>
           apply_guards (Guard coin50) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))) \<and>
           apply_outputs (Outputs coin50) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))) \<noteq>
           apply_outputs (Outputs coin) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))))"
    apply (rule_tac x="[Num 50]" in exI)
    apply (rule_tac x="<>" in exI)
    apply (simp add: transitions)
    apply (simp add: satisfies_context_def datastate2context_def consistent_def)
    apply (rule_tac x="<>" in exI)
    apply safe
    apply (case_tac r)
       apply simp
      apply simp
      apply (case_tac x2)
       apply simp
      apply simp
     apply simp
    by simp
  show ?thesis
    by (simp add: subsumes_def violation)
qed

lemma satisfies_must_have_r2_0: "satisfies_context d \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> \<Longrightarrow> d (R 2) = Some (Num 0)"
proof-
  have contrapositive: "\<not> d (R 2) = Some (Num 0) \<Longrightarrow> \<not>satisfies_context d \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk>"
    apply (simp add: satisfies_context_def datastate2context_def consistent_def)
    apply (rule allI)
    apply (rule_tac x="V (R 2)" in exI)
    apply simp
    apply (case_tac "d (R 2)")
     apply simp
    by simp
  show "satisfies_context d \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> \<Longrightarrow> d (R 2) = Some (Num 0)"
    using contrapositive
    by auto
qed 

lemma consistent_medial_coin: "consistent \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk>"
    apply (simp add: consistent_def)
    apply (rule_tac x="<R 1 := Str ''coke'', R 2 := Num 0, I 1 := Num 50>" in exI)
    apply (rule allI)
    by (simp add: consistent_empty_4)

lemma coin_posterior: "posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> coin = 
                       \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Bc True\<rbrakk>"
  apply (simp add: posterior_def Let_def transitions satisfiable_def remove_input_constraints_def)
  apply standard
  apply clarify
   apply (rule ext)
   apply simp
  by (simp add: consistent_medial_coin)

lemma coin_subsumes_coin50: "subsumes \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> coin coin50"
proof-
  have medial_coin50: "medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> (Guard coin50) =
        \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0), V (I 1) \<mapsto> Eq (Num 50)\<rbrakk>"
    apply (rule ext)
    by (simp add: transitions)
  have consistent_medial_coin50: "consistent \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0), V (I 1) \<mapsto> cexp.Eq (Num 50)\<rbrakk>"
    apply (simp add: consistent_def)
    apply (rule_tac x="<R 1 := Str ''coke'', R 2 := Num 0, I 1 := Num 50>" in exI)
    apply (rule allI)
    by (simp add: consistent_empty_4)
  have apply_coin50_updates: "(remove_input_constraints
              (Contexts.apply_updates \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0), V (I 1) \<mapsto> cexp.Eq (Num 50)\<rbrakk>
                \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> (Updates coin50))) = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 50)\<rbrakk>"
    apply (rule ext)
    by (simp add: coin50_def remove_input_constraints_def)
  have apply_coin_updates: "remove_input_constraints
                  (Contexts.apply_updates \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0), V (I 1) \<mapsto> cexp.Eq (Num 50)\<rbrakk>
                    \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0), V (I 1) \<mapsto> cexp.Eq (Num 50)\<rbrakk> (Updates coin)) = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 50)\<rbrakk>"
    apply (rule ext)
    apply (simp add: coin_def remove_input_constraints_def valid_def satisfiable_def)
    by auto
  show ?thesis
    unfolding subsumes_def
    apply standard
     apply (simp add: transitions)
    apply standard
     apply (simp add: transitions)
    apply standard
     apply (simp add: transitions)
    apply standard
     apply (simp add: transitions)
     apply clarify
     apply (case_tac "cval (\<lbrakk>\<rbrakk> r) i")
      apply simp
     apply simp
    apply standard
     apply (simp add: transitions)
     apply clarify
     apply (case_tac "value_plus (r (R 2)) (Some (Num 50))")
      apply simp
    using satisfies_must_have_r2_0
      apply fastforce
     apply simp
    using satisfies_must_have_r2_0
     apply fastforce
    apply standard
     apply (simp add: medial_coin50)
     apply clarify
     apply (simp add: posterior_def Let_def guard_coin medial_coin50)
     apply (simp add: consistent_medial_coin50)
     apply (simp add: apply_coin50_updates apply_coin_updates)
    apply (simp add: consistent_def)
    apply safe
    apply (rule_tac x=s in exI)
    apply (simp add: posterior_def Let_def)
    apply (simp add: medial_coin50 consistent_medial_coin50)
    apply (simp add: apply_coin50_updates)
    apply (simp add: guard_coin consistent_medial_coin)
    apply (simp add: coin_def remove_input_constraints_def satisfiable_def)
    by (simp add: consistent_empty_4)
qed

lemma step_vend_fail: "step merge_1_2_update 1 <R 1 := hd b, R 2 := Num 0> ''vend'' [] = Some (vend_fail, 1, [], <R 1 := hd b, R 2 := Num 0>)"
proof-
  have set_filter: "(Set.filter
          (\<lambda>((origin, dest), t).
              origin = 1 \<and>
              Label t = ''vend'' \<and>
              Arity t = 0 \<and> apply_guards (Guard t) (case_vname Map.empty (\<lambda>n. if n = 2 then Some (Num 0) else <R 1 := hd b> (R n))))
          (fset merge_1_2_update)) = {((1, 1), vend_fail)}"
    apply (simp add: merge_1_2_update_def Set.filter_def)
    apply safe
    by (simp_all add: transitions)
  show ?thesis
    apply (simp add: step_def possible_steps_def ffilter_def set_filter)
    apply (simp add: step_def possible_steps_def ffilter_def set_filter)
    by (simp add: vend_fail_def)
qed

lemma posterior_vend_fail: "posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> vend_fail =
       \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk>"
proof-
  have medial: "medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> (Guard vend_fail) =
        \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> And (cexp.Eq (Num 0)) (cexp.Lt (Num 100))\<rbrakk>"
    apply (rule ext)
    by (simp add: vend_fail_def)
  have consistent: "consistent \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> And (cexp.Eq (Num 0)) (cexp.Lt (Num 100))\<rbrakk>"
    apply (simp add: consistent_def)
    apply (rule_tac x="<R 1 := Num 5, R 2 := Num 0>" in exI)
    apply clarify
    by (simp add: consistent_empty_4)
  show ?thesis
    unfolding posterior_def Let_def
    apply (simp add: medial consistent remove_input_constraints_def)
    apply (rule ext)
    by (simp add: vend_fail_def)
qed

lemma merge_1_2_step_0_invalid: "\<not> (aa = ''select'' \<and> length b = 1) \<Longrightarrow> nondeterministic_step merge_1_2 0 Map.empty aa b = None"
proof-
  assume premise: "\<not> (aa = ''select'' \<and> length b = 1)"
  have set_filter: "Set.filter
           (\<lambda>((origin, dest), t).
               origin = 0 \<and> Label t = aa \<and> length b = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) Map.empty))
           (fset merge_1_2) = {}"
    using premise
    apply (simp add: merge_1_2_def Set.filter_def)
    apply safe
    by (simp_all add: transitions)
  show ?thesis
    by (simp add: nondeterministic_step_def possible_steps_def ffilter_def set_filter)
qed

lemma nondeterministic_step_merge_1_2_1_invalid: "aa \<noteq> ''coin'' \<Longrightarrow> nondeterministic_step merge_1_2 1 <R 1 := d> aa b = None"
proof-
  assume premise: "aa \<noteq> ''coin''"
  have set_filter: "Set.filter
           (\<lambda>((origin, dest), t).
               origin = 1 \<and>
               Label t = aa \<and>
               length b = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) (\<lambda>n. if n = 1 then Some d else None)))
           (fset merge_1_2) = {}"
    using premise
    apply (simp add: Set.filter_def merge_1_2_def)
    apply safe
    by (simp_all add: transitions)
  show ?thesis
    by (simp add: nondeterministic_step_def possible_steps_def ffilter_def set_filter)
qed

lemma nondeterministic_step_merge_1_2_1_invalid_coin: "aa = ''coin'' \<Longrightarrow> length b \<noteq> 1 \<Longrightarrow> nondeterministic_step merge_1_2 1 <R 1 := d> aa b = None"
proof-
  assume premise1: "aa = ''coin''"
  assume premise2: "length b \<noteq> 1"
  have set_filter: "Set.filter
           (\<lambda>((origin, dest), t).
               origin = 1 \<and>
               Label t = aa \<and>
               length b = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) (\<lambda>n. if n = 1 then Some d else None)))
           (fset merge_1_2) = {}"
    using premise1 premise2
    apply (simp add: merge_1_2_def Set.filter_def)
    apply safe
    by (simp_all add: transitions)
  show ?thesis
    by (simp add: nondeterministic_step_def possible_steps_def ffilter_def set_filter)
qed

lemma nondeterministic_step_merge_1_2_1_silly_coin: "length b = 1 \<Longrightarrow> b \<noteq> [Num 50] \<Longrightarrow> nondeterministic_step merge_1_2 1 <R 1 := d> ''coin'' b = Some (coin, 1, [None], <R 1 := d>)"
proof-
  assume premise1: "length b = 1"
  assume premise2: "b \<noteq> [Num 50]"
  have set_filter: "Set.filter
            (\<lambda>((origin, dest), t).
                origin = 1 \<and>
                Label t = ''coin'' \<and>
                length b = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) (\<lambda>n. if n = 1 then Some d else None)))
            (fset merge_1_2) = {((1, 1), coin)}"
    using premise1 premise2
    apply (simp add: Set.filter_def merge_1_2_def)
    apply safe
           apply (simp_all add: transitions hd_input2state)
    by (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))
  show ?thesis
    apply (simp add: nondeterministic_step_def possible_steps_def ffilter_def set_filter)
    apply (simp add: set_filter)
    apply (simp add: transitions)
    apply (rule ext)
    by simp
qed

lemma easy_merge_some: "easy_merge drinks_before merge_1_2_update 2 1 1 1 1 coin coin50 (\<lambda>a b c d. Map.empty) = Some drinks_after"
  apply (simp add: easy_merge_def)
  oops

lemma score_2: "sorted_list_of_fset (score drinks_after naive_score) = [(0, 0, 1), (0, 0, 3), (0, 1, 3)]"
proof-
  have set_filter: "Set.filter (\<lambda>(x, y). x < y) (fset (all_pairs (S drinks_after))) = {(1, 3), (0, 3), (0, 1)}"
    apply (simp add: Set.filter_def all_pairs_def S_def drinks_after_def)
    by auto
  have abs_fset: "Abs_fset {(1, 3), (0, 3), (0, 1)} = {|(1, 3), (0, 3), (0, 1)|}"
    by (metis finsert.rep_eq fset_inverse fset_simps(1))
  have outgoing_transitions_1: "Set.filter (\<lambda>((origin, dest), t). origin = 1) (fset drinks_after) = {((1, 1), coin), ((1, 1), vend_fail), ((1, 3), vend_success)}"
    apply (simp add: drinks_after_def Set.filter_def)
    apply safe
    by (simp_all add: transitions)
  have abs_fset_1: "Abs_fset {((1, 1), coin), ((1, 1), vend_fail), ((1, 3), vend_success)} =
                            {|((1, 1), coin), ((1, 1), vend_fail), ((1, 3), vend_success)|}"
    by (metis finsert.rep_eq fset_inverse fset_simps(1))
  have outgoing_transitions_3: "Set.filter (\<lambda>((origin, dest), t). origin = 3) (fset drinks_after) = {}"
    apply (simp add: drinks_after_def Set.filter_def)
    apply safe
    by (simp_all add: transitions)
  have outgoing_transitions_0: "Set.filter (\<lambda>((origin, dest), t). origin = 0) (fset drinks_after) = {((0, 1), select_update)}"
    apply (simp add: drinks_after_def Set.filter_def)
    apply safe
    by (simp_all add: transitions)
  have score_0_1: "naive_score {|select_update|} {|coin, vend_fail, vend_success|} = 0"
  proof-
    have abs_fset: "Abs_fset {(select_update, coin), (select_update, vend_fail), (select_update, vend_success)} = 
                  {|(select_update, coin), (select_update, vend_fail), (select_update, vend_success)|}"
      by (metis finsert.rep_eq fset_inverse fset_simps(1))
    show ?thesis
      apply (simp add: naive_score_def fprod_def abs_fset)
      by (simp add: transitions)
  qed
  show ?thesis
    apply (simp add: score_def ffilter_def set_filter abs_fset)
    apply (simp add: outgoing_transitions_def ffilter_def)
    apply (simp add: outgoing_transitions_1 abs_fset_1)
    apply (simp add: outgoing_transitions_3)
    apply (simp add: outgoing_transitions_0)
    apply (simp add: naive_score_empty score_0_1)
    by (simp add: sorted_list_of_fset_def)
qed

lemma step_drinks_before_select: "length ba = 1 \<Longrightarrow> step drinks_before 0 Map.empty ''select'' ba = Some (select, 1, [], <R 1 := hd ba>)"
proof-
  assume premise: "length ba = 1"
  show ?thesis
     apply (simp add: premise step_def possible_steps_drinks_before_select)
    apply (simp add: select_def)
    apply (rule ext)
    by (simp add: hd_input2state premise)
qed

lemma no_direct_subsumption_coin_coin50: "\<not> directly_subsumes drinks_before merge_1_2 1 coin coin50"
proof-
  have subsumption_violation: "(\<exists>i r. satisfies_context r \<lbrakk>V (R 1) \<mapsto> cexp.Bc True\<rbrakk> \<and>
           apply_guards (Guard coin50) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))) \<and>
           apply_outputs (Outputs coin50) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))) \<noteq>
           apply_outputs (Outputs coin) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))))"
    apply (rule_tac x="[Num 50]" in exI)
    apply (rule_tac x="<R 1 := Str ''coke''>" in exI)
    apply standard
     defer
    apply (simp add: coin50_def coin_def)
     apply (simp add: satisfies_context_def consistent_def datastate2context_def)
     apply (rule_tac x="<R 1 := Str ''coke''>" in exI)
     apply clarify
     apply simp
     apply (case_tac r)
        apply simp
       apply simp
       apply (case_tac x2)
    by auto
  show ?thesis
    apply (simp add: directly_subsumes_def)
    apply (rule_tac x="[(''select'', [Str ''coke''])]" in exI)
    apply standard
     apply (simp add: accepts_trace_def)
     apply (rule accepts.step)
      apply (simp add: step_drinks_before_select)
     apply (rule accepts.base)
    apply standard
     apply (rule gets_us_to.step_some)
      apply (simp add: step_def possible_steps_drinks_before_select)
     apply (simp add: gets_us_to.base)
    apply (simp add: anterior_context_def step_def possible_steps_merge_1_2_select select_posterior)
    by (simp add: subsumes_def subsumption_violation)
qed

lemma possible_steps_merge_1_2_coin50: "possible_steps merge_1_2 1 r ''coin'' [Num 50] = {|(1, coin), (1, coin50)|}"
proof-
  have set_filter: "Set.filter
       (\<lambda>((origin, dest), t).
           origin = 1 \<and>
           Label t = ''coin'' \<and> Suc 0 = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state [Num 50] 1 (I n)) (\<lambda>n. r (R n))))
       (fset merge_1_2) = {((1, 1), coin), ((1, 1), coin50)}"
    apply (simp add: Set.filter_def merge_1_2_def)
    apply safe
    by (simp_all add: transitions)
  have abs_fset: "Abs_fset {((1, 1), coin), ((1, 1), coin50)} = {|((1, 1), coin), ((1, 1), coin50)|}"
    by (metis finsert.rep_eq fset_inverse fset_simps(1))
  show ?thesis
    by (simp add: possible_steps_def ffilter_def set_filter abs_fset)
qed

lemma step_drinks_before_coin_50: "step drinks_before 1 <R 1 := d> ''coin'' [Num 50] = Some (coin50, 2, [Some (Num 50)], <R 1 := d, R 2 := Num 50>)"
proof-
  have set_filter: "Set.filter
          (\<lambda>((origin, dest), t).
              origin = 1 \<and>
              Label t = ''coin'' \<and>
              Suc 0 = Arity t \<and>
              apply_guards (Guard t)
               (case_vname (\<lambda>n. if n = 1 then Some (Num 50) else input2state [] (1 + 1) (I n)) (\<lambda>n. if n = 1 then Some d else None)))
          (fset drinks_before) = {((1, 2), coin50)}"
    apply (simp add: Set.filter_def drinks_before_def)
    apply safe
    by (simp_all add: transitions)
  show ?thesis
    apply (simp add: step_def possible_steps_def ffilter_def set_filter)
    apply (simp add: set_filter)
    apply (simp add: transitions)
    apply (rule ext)
    by simp
qed

lemma no_direct_subsumption_coin50_coin: "\<not> directly_subsumes drinks_before merge_1_2 2 coin50 coin"
proof-
  have subsumption_violation: "(\<exists>i r. satisfies_context r \<lbrakk>V (R 1) \<mapsto> cexp.Bc True\<rbrakk> \<and>
           apply_guards (Guard coin) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))) \<and>
           apply_outputs (Outputs coin) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))) \<noteq>
           apply_outputs (Outputs coin50) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))))"
apply (rule_tac x="[Num 50]" in exI)
    apply (rule_tac x="<R 1 := Str ''coke''>" in exI)
    apply standard
     defer
    apply (simp add: coin50_def coin_def)
     apply (simp add: satisfies_context_def consistent_def datastate2context_def)
     apply (rule_tac x="<R 1 := Str ''coke''>" in exI)
     apply clarify
     apply simp
     apply (case_tac r)
        apply simp
       apply simp
       apply (case_tac x2)
    by auto
  show ?thesis
    apply (simp add: directly_subsumes_def)
    apply (rule_tac x="[(''select'', [Str ''coke'']), (''coin'', [Num 50])]" in exI)
    apply standard
     apply (simp add: accepts_trace_def)
     apply (rule accepts.step)
      apply (simp add: step_drinks_before_select)
     apply (rule accepts.step)
      apply (simp add: step_drinks_before_coin_50)
    apply (rule accepts.base)
    apply standard
     apply (rule gets_us_to.step_some)
      apply (simp add: step_def possible_steps_drinks_before_select)
     apply (rule gets_us_to.step_some)
      apply (simp add: step_def possible_steps_drinks_before_coin_50)
     apply (simp add: gets_us_to.base)
    apply (simp add: anterior_context_def step_def possible_steps_merge_1_2_select select_posterior)
    apply (simp add: possible_steps_merge_1_2_coin50 fis_singleton_def is_singleton_def)
    apply standard
     apply (simp add: transitions)
    by (simp add: subsumes_def subsumption_violation)
qed

lemma easy_merge_none:  "easy_merge drinks_before merge_1_2 2 1 1 1 1 coin coin50 (\<lambda>a b c d. Map.empty) = None"
  by (simp add: easy_merge_def no_direct_subsumption_coin_coin50 no_direct_subsumption_coin50_coin)

lemma regsimp1: "(\<lambda>a. if a = R 1 then Some d else None) = <R 1 := d>"
  by auto

lemma contextsimp1: "(\<lambda>a. if a = V (R 2) then cexp.Eq (Num 0) else if a = V (R 1) then cexp.Bc True else \<lbrakk>\<rbrakk> a) = 
                     \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk>"
  by auto

lemma regsimp2: "(\<lambda>a. if a = R 2 then Some (Num n) else if a = R 1 then Some d else None) = <R 1 := d, R 2 := Num n>"
  by auto

lemma invalid_r2_vend: "\<nexists>n. ra (R 2) = Some (Num n) \<Longrightarrow> step drinks_before 2 ra ''vend'' [] = None"
proof-
  assume premise: "\<nexists>n. ra (R 2) = Some (Num n)"
  have set_filter: "(Set.filter
         (\<lambda>((origin, dest), t). origin = 2 \<and> Label t = ''vend'' \<and> Arity t = 0 \<and> apply_guards (Guard t) (case_vname Map.empty (\<lambda>n. ra (R n))))
         (fset drinks_before)) = {}"
    using premise
    apply (simp add: Set.filter_def drinks_before_def)
    apply safe
      apply (simp add: transitions)
    apply (simp add: transitions)
     apply (metis MaybeBoolInt.elims option.simps(3))
    apply (simp add: transitions)
    apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some (Num 100)) (ra (R 2))")
     apply simp
    apply simp
    by (metis MaybeBoolInt.elims option.simps(3))
  show ?thesis
    by (simp add: step_def possible_steps_def ffilter_def set_filter)
qed

lemma step_drinks_before_vend_fail: "ra (R 2) = Some (Num x1) \<Longrightarrow> x1 < 100 \<Longrightarrow> step drinks_before 2 ra ''vend'' [] = Some (vend_fail, 2, [], ra)"
proof-
  assume premise1: "ra (R 2) = Some (Num x1)"
  assume premise2: "x1 < 100"
  have set_filter: "Set.filter
          (\<lambda>((origin, dest), t).
              origin = 2 \<and> Label t = ''vend'' \<and> Arity t = 0 \<and> apply_guards (Guard t) (case_vname Map.empty (\<lambda>n. ra (R n))))
          (fset drinks_before) = {((2, 2), vend_fail)}"
    using premise1 premise2
    apply (simp add: Set.filter_def drinks_before_def)
    apply safe
    by (simp_all add: transitions)
  show ?thesis
    apply (simp add: step_def possible_steps_def ffilter_def set_filter)
    apply (simp add: set_filter)
    by (simp add: transitions)
qed

lemma step_drinks_before_3_none: "step drinks_before 3 r' a b = None"
proof-
  have set_filter: "Set.filter
         (\<lambda>((origin, dest), t).
             origin = 3 \<and> Label t = a \<and> length b = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) (\<lambda>n. r' (R n))))
         (fset drinks_before) = {}"
    by (simp add: Set.filter_def drinks_before_def)
  show ?thesis
    by (simp add: step_def possible_steps_def ffilter_def set_filter)
qed

lemma no_route_from_3_to_anywhere: "s \<noteq> 3 \<Longrightarrow> \<not>gets_us_to s drinks_before 3 r' p"
  apply safe
  apply (rule gets_us_to.cases)
     apply simp
    apply simp
   apply (simp add: step_drinks_before_3_none)
  by simp

lemma no_route_from_2_to_1: "\<forall>r. \<not>gets_us_to 1 drinks_before 2 r p"
proof(induct p)
  case Nil
  then show ?case
    by (simp add: no_further_steps)
next
  case (Cons a p)
  then show ?case
    apply clarify
    apply (rule gets_us_to.cases)
       apply simp
      apply simp
     defer
     apply simp
    apply clarify
    apply simp
    apply (case_tac "aa = ''coin'' \<and> length b = 1")
     apply (simp add: step_def possible_steps_drinks_before_coin)
    apply (case_tac "aa = ''vend'' \<and> b = []")
    defer
    apply (simp add: nondeterministic_step_drinks_before_invalid_step_2 nondeterministic_step_none)
     apply clarify
     apply simp
     apply (case_tac "ra (R 2)")
      apply (simp add: invalid_r2_vend)
     apply (case_tac aa)
      defer
     apply (simp add: invalid_r2_vend)
    apply clarify
    apply simp
    apply (case_tac "x1 < 100")
     apply (simp add: step_drinks_before_vend_fail)
    apply (simp add: step_def drinks_before_vend_success)
    apply (simp add: vend_success_def)
    apply clarify
    by (simp add: no_route_from_3_to_anywhere)
qed

lemma drinks_before_1_step_invalid: "(aa, ba) \<noteq> (''coin'', [Num 50]) \<Longrightarrow> step drinks_before 1 r aa ba = None"
proof-
  assume premise: "(aa, ba) \<noteq> (''coin'', [Num 50])"
  have set_filter: "Set.filter
         (\<lambda>((origin, dest), t).
             origin = 1 \<and>
             Label t = aa \<and> length ba = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state ba 1 (I n)) (\<lambda>n. r (R n))))
         (fset drinks_before) = {}"
    using premise
    apply (simp add: Set.filter_def drinks_before_def)
    apply safe
     apply (simp_all add: transitions)
    by (metis One_nat_def hd_input2state le_numeral_extra(4) length_0_conv length_Suc_conv list.sel(1) option.inject)
  show ?thesis
    by (simp add: step_def possible_steps_def ffilter_def set_filter)
qed

lemma stop_at_1: "step drinks_before 1 <R 1 := d> aa ba = Some (uw, s', ux, r') \<Longrightarrow> \<not>gets_us_to 1 drinks_before 1 <R 1 := d> ((aa, ba) # p)"
  apply safe
  apply (rule gets_us_to.cases)
     apply simp
    apply simp
  apply (case_tac "(aa, ba) = (''coin'', [Num 50])")
   apply (simp add: step_drinks_before_coin_50)
    apply clarify
    apply simp
    apply clarify
    apply simp
   apply (simp add: step_drinks_before_coin_50)
    apply clarify
    apply (simp add: no_route_from_2_to_1)
   apply (simp add: drinks_before_1_step_invalid)
   apply clarify
  by simp

lemma drinks_before_1_must_be_coin_50: "fis_singleton (possible_steps drinks_before 1 <R 1 := d> aa ba) \<Longrightarrow> (aa = ''coin'' \<and> ba = [Num 50])"
proof-
  assume premise: "fis_singleton (possible_steps drinks_before 1 <R 1 := d> aa ba)"
  have set_filter: "\<not> (aa = ''coin'' \<and> ba = [Num 50]) \<Longrightarrow> Set.filter
         (\<lambda>((origin, dest), t).
             origin = 1 \<and>
             Label t = aa \<and>
             length ba = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state ba 1 (I n)) (\<lambda>n. if n = 1 then Some d else None)))
         (fset drinks_before) = {}"
    apply (simp add: Set.filter_def drinks_before_def)
    apply (simp add: transitions)
    by (metis One_nat_def hd_input2state le_numeral_extra(4) length_0_conv length_Suc_conv list.sel(1) option.inject)
  show ?thesis
    using premise
    apply (case_tac "aa = ''coin'' \<and> ba = [Num 50]")
     apply simp
    by (simp add: possible_steps_def ffilter_def set_filter)
qed

lemma gets_us_to_aux: "gets_us_to 1 drinks_before 1 <R 1 := d> p \<Longrightarrow> accepts drinks_before 1 <R 1 := d> p \<Longrightarrow>
          posterior_sequence \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> merge_1_2_update 1 <R 1 := d, R 2 := Num 0> p =
          \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk>"
proof (induct p)
  case Nil
  then show ?case
  by simp
next
  case (Cons a p)
  then show ?case
    apply (case_tac a)
    apply clarify
    apply (simp del: posterior_sequence.simps)
    apply (simp only: regsimp1 regsimp2 contextsimp1) \<comment> \<open>This makes it print nicely again\<close>
    apply (rule gets_us_to.cases)
       apply simp
      apply simp
     apply simp
    apply clarify
     apply (simp del: posterior_sequence.simps)
     apply (simp add: stop_at_1)
    apply clarify
    apply simp
    apply (case_tac "step merge_1_2_update 1 <R 1 := d, R 2 := Num 0> aa ba")
     apply simp
    apply simp
    apply clarify
    by (simp add: no_step_none)
qed

lemma accepts_trace_anterior: "accepts_trace drinks_before p \<Longrightarrow> gets_us_to 1 drinks_before 0 Map.empty p \<Longrightarrow> anterior_context merge_1_2_update p = \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> Eq (Num 0)\<rbrakk>"
proof(induct p)
  case Nil
  then show ?case
    apply simp
    apply (rule gets_us_to.cases)
    by auto
next
  have select_update_updates: "\<forall>ba. length ba = 1 \<longrightarrow> (EFSM.apply_updates (Updates select_update) (case_vname (\<lambda>n. input2state ba 1 (I n)) Map.empty) Map.empty) =
        <R 1 := hd ba, R 2 := Num 0>"
    apply clarify
    apply (rule ext)
    by (simp add: transitions hd_input2state)
  case (Cons a p)
  then show ?case
    apply (case_tac a)
    apply (case_tac "aa = ''select'' \<and> length b = 1")
    defer
     apply clarify
     apply (rule gets_us_to.cases)
        apply simp
       apply simp
    using drinks_before_step_0_invalid nondeterministic_step_none
      apply auto[1]
     apply simp

    apply (rule gets_us_to.cases)
       apply simp
      apply simp
     defer
     apply clarify
     apply (simp add: step_def possible_steps_drinks_before_select)

    apply clarify
    apply (simp add: step_drinks_before_select)
    apply clarify
    apply (simp add: anterior_context_def step_def possible_steps_merge_1_2_update_select)
    apply (simp add: accepts_trace_def)
    apply (rule accepts.cases)
      apply simp
     apply simp
    apply simp
    apply clarify
    apply (simp add: step_drinks_before_select)
    apply clarify
    apply (simp add: select_update_posterior select_update_updates)
    by (simp add: gets_us_to_aux)
qed

lemma coin_directly_subsumes_coin50: "directly_subsumes drinks_before merge_1_2_update 1 coin coin50"
  apply (simp add: directly_subsumes_def)
  apply clarify
  by (simp add: accepts_trace_anterior coin_subsumes_coin50)

lemma step_merge_1_2_update_select: "step merge_1_2_update 0 Map.empty ''select'' [d] = Some (select_update, 1, [], <R 1 := d, R 2 := Num 0>)"
  apply (simp add: step_def possible_steps_merge_1_2_update_select)
  apply (simp add: transitions)
  apply (rule ext)
  by simp

lemma step_merge_1_2_update_coin_50: "step merge_1_2_update 1 <R 1 := Str ''coke'', R 2 := Num 0> ''coin'' [Num 50] = None"
  apply (simp add: step_def merge_1_2_update_possible_steps_coin_50 fis_singleton_def is_singleton_def)
  by (simp add: transitions)

lemma coin50_doesnt_subsume_coin: "\<not> subsumes \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> coin50 coin"
proof-
  have subsumption_violation: "(\<exists>r i. cval (medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> (Guard coin) r) i = Some True \<and>
           cval (medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> (Guard coin50) r) i \<noteq> Some True)"
    apply (simp add: transitions)
    by auto
  show ?thesis
    by (simp add: subsumes_def subsumption_violation)
qed

lemma coin50_doesnt_directly_subsume_coin: "\<not> directly_subsumes drinks_before merge_1_2_update 2 coin50 coin"
proof-
  show ?thesis
    apply (simp add: directly_subsumes_def)
    apply (rule_tac x="[(''select'', [Str ''coke'']), (''coin'', [Num 50])]" in exI)
    apply standard
     apply (simp add: accepts_trace_def)
     apply (rule accepts.step)
      apply (simp add: step_drinks_before_select)
     apply (rule accepts.step)
      apply (simp add: step_drinks_before_coin_50)
     apply (rule accepts.base)
    apply standard
    apply (rule gets_us_to.step_some)
      apply (simp add: step_drinks_before_select)
    apply (rule gets_us_to.step_some)
      apply (simp add: step_drinks_before_coin_50)
     apply (simp add: gets_us_to.base)
    apply (simp add: anterior_context_def)
    apply (simp add: step_merge_1_2_update_select step_merge_1_2_update_coin_50)
    by (simp add: select_update_posterior coin50_doesnt_subsume_coin)
qed

lemma easy_merge_some: "easy_merge drinks_before merge_1_2_update 2 1 (update_mapping 1) (update_mapping 1) (update_mapping 1) coin coin50 (\<lambda>a b c d. Map.empty) =
    Some drinks_after"
proof-
  have set_filter: "Set.filter (\<lambda>x. x \<noteq> ((1, 1), coin50)) (fset merge_1_2_update) = {((0, 1), select_update), ((1, 1), coin), ((1, 1), vend_fail), ((1, 3), vend_success)}"
    apply (simp add: merge_1_2_update_def Set.filter_def)
    apply safe
    by (simp_all add: transitions)
  have abs_fset: "Abs_fset {((0, 1), select_update), ((1, 1), coin), ((1, 1), vend_fail), ((1, 3), vend_success)} =
                          {|((0, 1), select_update), ((1, 1), coin), ((1, 1), vend_fail), ((1, 3), vend_success)|}"
    by (metis finsert.rep_eq fset_inverse fset_simps(1))
  show ?thesis
  apply (simp add: easy_merge_def coin_directly_subsumes_coin50 coin50_doesnt_directly_subsume_coin)
    apply (simp add: replace_transition_def update_mapping_def ffilter_def set_filter abs_fset)
    using drinks_after_def
    by auto
qed

lemma merge_transitions: "merge_transitions drinks_before merge_1_2 2 1 1 1 1 coin coin50 (\<lambda>a b c d. Map.empty)
                (\<lambda>a b c d e. Some (merge_1_2_update, update_mapping, update_before)) True = Some drinks_after"
  apply (simp add: merge_transitions_def easy_merge_none)
  by (simp add: simulation easy_merge_some)

lemma "infer drinks_before naive_score (\<lambda>a b c d e. None) (\<lambda>a b c d e. Some (merge_1_2_update, update_mapping, update_before)) = drinks_after"
proof-
  have nondeterminism_merge_1_2: "nondeterminism merge_1_2"
    by (simp add: nondeterminism_def nondeterministic_pairs)
  show ?thesis
    apply (simp add: score sorted_list_of_fset_def Let_def)
    apply (simp add: merge_1_2 nondeterministic_pairs)
    apply (simp add: coin_doesnt_exit_1_drinks_before coin50_exits_1_drinks_before)
    apply (simp add: nondeterminism_merge_1_2)
    apply (simp add: merge_transitions)
    by (simp add: score_2)
qed
end