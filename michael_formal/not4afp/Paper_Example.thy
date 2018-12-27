theory Paper_Example
imports Inference
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

declare One_nat_def [simp del]

definition drinks_before :: transition_matrix where
  "drinks_before = {|((0, 1), select), ((1, 2), coin50), ((2, 2), coin), ((2, 2), vend_fail), ((2, 3), vend_success)|}"

definition drinks_after :: transition_matrix where
  "drinks_after = {|((0, 1), select_update), ((1, 1), coin), ((1, 1), vend_fail), ((1, 2), vend_success)|}"

definition merge_1_2 :: transition_matrix where
  "merge_1_2 = {|((0, 1), select), ((1, 1), coin50), ((1, 1), coin), ((1, 1), vend_fail), ((1, 3), vend_success)|}"

lemma merge_1_2: "merge_states 1 2 drinks_before = merge_1_2"
  by (simp add: merge_states_def drinks_before_def merge_1_2_def merge_states_aux_def)

definition merge_1_2_update :: transition_matrix where
  "merge_1_2_update = {|((0, 1), select_update), ((1, 1), coin50), ((1, 1), coin), ((1, 1), vend_fail), ((1, 3), vend_success)|}"

lemmas transitions = select_def coin_def coin50_def vend_fail_def vend_success_def select_update_def

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
    apply (simp add: nondeterministic_step_def possible_steps_def ffilter_def set_filter)
    using bot_fset.abs_eq by auto
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
    apply (simp add: nondeterministic_step_def possible_steps_def ffilter_def set_filter)
    using bot_fset.abs_eq by auto
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
    apply (simp add: nondeterministic_step_def possible_steps_def ffilter_def set_filter)
    using bot_fset_def by force
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
    apply (simp add: nondeterministic_step_def possible_steps_def ffilter_def set_filter)
    using bot_fset_def by force
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
    apply (simp add: nondeterministic_step_def possible_steps_def ffilter_def set_filter)
    using bot_fset_def by force
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
    apply (simp add: nondeterministic_step_def possible_steps_def ffilter_def set_filter)
    using bot_fset_def by force
qed

lemma simulation_2_1: "\<forall>r. nondeterministic_simulates_trace drinks_before merge_1_2_update 2 1 r r lst"
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
        apply (simp add: nondeterministic_step_def drinks_before_vend_fail)
       apply (simp add: merge_1_2_update_vend_fail)
      apply simp
     apply (simp add: vend_fail_def)
     apply (rule nondeterministic_simulates_trace.step_some)
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

lemma simulation_1_1: "nondeterministic_simulates_trace drinks_before merge_1_2_update 1 1 <R 1 := d> <R 1 := d, R 2 := Num 0> ((aa, b) # list)"
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
     apply (simp add: nondeterministic_step_def possible_steps_drinks_before_coin_50)
      apply (simp add: nondeterministic_step_def merge_1_2_update_possible_steps_coin_50 choice_coin50_coin)
      apply auto[1]
     apply simp
    apply (simp add: coin50_updates coin50_updates_2)
    by (simp add: simulation_2_1)
qed

lemma simulation_0_0: "nondeterministic_simulates_trace drinks_before merge_1_2_update 0 0 Map.empty Map.empty ((aa, b) # t)"
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

lemma simulation_aux: "nondeterministic_simulates_trace drinks_before merge_1_2_update 0 0 Map.empty Map.empty t"
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

lemma simulation: "nondeterministic_simulates drinks_before merge_1_2_update"
  apply (simp add:nondeterministic_simulates_def)
  apply (rule allI)
  by (simp add: simulation_aux)


end