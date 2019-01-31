theory Paper_Example
imports Inference SelectionStrategies EFSM_Dot
begin

definition select :: transition where
  "select = \<lparr>
              Label = (STR ''select''),
              Arity = 1,
              Guard = [],
              Outputs = [],
              Updates = [(R 1, V (I 1))]
            \<rparr>"

definition coin50 :: transition where
  "coin50 = \<lparr>
              Label = (STR ''coin''),
              Arity = 1,
              Guard = [gexp.Eq (V (I 1)) (L (Num 50))],
              Outputs = [L (Num 50)],
              Updates = [(R 2, L (Num 50))]
            \<rparr>"

definition coin :: transition where
  "coin = \<lparr>
              Label = (STR ''coin''),
              Arity = 1,
              Guard = [],
              Outputs = [Plus (V (R 2)) (V (I 1))],
              Updates = [(R 2, Plus (V (R 2)) (V (I 1)))]
            \<rparr>"

lemma guard_coin: "Guard coin = []"
  by (simp add: coin_def)

definition vend_fail :: transition where
  "vend_fail = \<lparr>
              Label = (STR ''vend''),
              Arity = 0,
              Guard = [GExp.Lt (V (R 2)) (L (Num 100))],
              Outputs = [],
              Updates = []
            \<rparr>"

definition vend_success :: transition where
  "vend_success = \<lparr>
              Label = (STR ''vend''),
              Arity = 0,
              Guard = [GExp.Ge (V (R 2)) (L (Num 100))],
              Outputs = [(V (R 1))],
              Updates = []
            \<rparr>"

definition select_update :: transition where
  "select_update = \<lparr>
              Label = (STR ''select''),
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

definition drinks_before :: iEFSM where
  "drinks_before = {|(0, (0, 1), select), (1, (1, 2), coin50), (2, (2, 2), coin), (3, (2, 2), vend_fail), (4, (2, 3), vend_success)|}"

definition drinks_after :: iEFSM where
  "drinks_after = {|(1, (1, 1), coin), (0, (0, 1), select_update), (3, (1, 1), vend_fail), (4, (1, 3), vend_success)|}"

definition merge_1_2_update :: iEFSM where
  "merge_1_2_update = {|(0, (0, 1), select_update), (1, (1, 1), coin50), (2, (1, 1), coin), (3, (1, 1), vend_fail), (4, (1, 3), vend_success)|}"

definition update_mapping :: "nat \<Rightarrow> nat" where
  "update_mapping x = x"

definition update_before :: "nat \<Rightarrow> nat" where
  "update_before x = (if x = 2 then 1 else x)"

definition modifier :: update_modifier where
  "modifier a b c d e =  Some (merge_1_2_update, update_mapping, update_before)"

lemma scoring_1: "sorted_list_of_fset (score drinks_before naive_score) = [(1, 1, 2)]"
proof-
  have S_drinks_before: "S drinks_before = {|0, 1, 2, 3|}"
    apply (simp add: S_def drinks_before_def)
    by auto
  have ffilter: "ffilter (\<lambda>(x, y). x < y) ({|0::nat, 1, 2, 3|} |\<times>| {|0::nat, 1, 2, 3|}) = {|
    (0, 1), (0, 2), (0, 3),
            (1, 2), (1, 3),
                    (2, 3)
  |}"
    apply (simp add: fprod_def ffilter_def fset_both_sides Abs_fset_inverse)
    apply (simp add: Set.filter_def)
    by auto
  have score_0_1: "naive_score {|select|} {|coin50|} = 0"
    by (simp add: naive_score_def transitions fprod_def)
  have score_0_2: "naive_score {|select|} {|coin, vend_fail, vend_success|} = 0"
    by (simp add: naive_score_def transitions fprod_def)
  have score_1_2: "naive_score {|coin50|} {|coin, vend_fail, vend_success|} = 1"
    by (simp add: naive_score_def transitions fprod_def)
  have score: "score drinks_before naive_score = {|(1, 1, 2)|}"
    apply (simp add: score_def S_drinks_before ffilter)
    apply (simp add: fimage_def outgoing_transitions_def drinks_before_def naive_score_empty)
    apply (simp add: score_0_1 score_0_2 score_1_2)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    by auto
  show ?thesis
    by (simp add: score sorted_list_of_fset_def)
qed

definition merged_1_2 :: iEFSM where
  "merged_1_2 = {|(0, (0, 1), select),
                  (1, (1, 1), coin50),
                  (2, (1, 1), coin),
                  (3, (1, 1), vend_fail),
                  (4, (1, 3), vend_success)
                |}"

lemma merge_states_1_2: "merge_states 1 2 drinks_before = merged_1_2"
  by (simp add: merge_states_def merge_states_aux_def drinks_before_def merged_1_2_def)

lemma choice_coin_coin50: "choice coin coin50"
  apply (simp add: transitions choice_def)
  by auto

lemma no_choice_coin50_vend_fail: "\<not>choice coin50 vend_fail"
  by (simp add: transitions choice_def)

lemma no_choice_coin50_vend_success: "\<not>choice coin50 vend_success"
  by (simp add: transitions choice_def)

lemma no_choice_vend_fail_vend_success: "\<not>choice vend_fail vend_success"
  by (simp add: transitions choice_def)

lemma no_choice_coin_vend_fail: "\<not>choice coin vend_fail"
  by (simp add: transitions choice_def)

lemma no_choice_coin_vend_success: "\<not>choice coin vend_success"
  by (simp add: transitions choice_def)

lemmas choices = no_choice_coin_vend_success no_choice_coin_vend_fail no_choice_vend_fail_vend_success no_choice_coin50_vend_success no_choice_coin50_vend_fail choice_coin_coin50 choice_symmetry

lemma coin_lt_coin50: "coin < coin50"
  by (simp add: transitions less_transition_ext_def)

lemmas orders = coin_lt_coin50

lemma nondeterministic_pairs_merged_1_2: "nondeterministic_pairs merged_1_2 = {|(1, (1, 1), (coin, 2), coin50, 1), (1, (1, 1), (coin50, 1), coin, 2)|}"
proof-
  have minus_1: "{(1, coin50, 1), (1, coin, 2), (1, vend_fail, 3), (3, vend_success, 4)} - {(1, coin, 2)} = {(1, coin50, 1), (1, vend_fail, 3), (3, vend_success, 4)}"
    apply (simp add: transitions)
    by auto
  have minus_2: "{(1, coin50, 1), (1, coin, 2), (1, vend_fail, 3), (3, vend_success, 4)} - {(1, vend_fail, 3)} = {(1, coin50, 1), (1, coin, 2), (3, vend_success, 4)}"
    apply (simp add: transitions)
    by auto
  have minus_3: "{(1, coin50, 1), (1, coin, 2), (1, vend_fail, 3), (3, vend_success, 4)} - {(3, vend_success, 4)} = {(1, coin50, 1), (1, coin, 2), (1, vend_fail, 3)}"
    apply (simp add: transitions)
    by auto
  have state_nondeterminism_1: "state_nondeterminism 1 {|(1, coin50, 1), (1, coin, 2), (1, vend_fail, 3), (3, vend_success, 4)|} = {|
     (1, (3, 1), (vend_success, 4), vend_fail, 3),
     (1, (3, 1), (vend_success, 4), coin, 2),
     (1, (3, 1), (vend_success, 4), coin50, 1),
     (1, (1, 3), (vend_fail, 3), vend_success, 4),
     (1, (1, 1), (vend_fail, 3), coin, 2),
     (1, (1, 1), (vend_fail, 3), coin50, 1),
     (1, (1, 3), (coin, 2), vend_success, 4),  
     (1, (1, 1), (coin, 2), vend_fail, 3),
     (1, (1, 1), (coin, 2), coin50, 1),
     (1, (1, 3), (coin50, 1), vend_success, 4),
     (1, (1, 1), (coin50, 1), vend_fail, 3),
     (1, (1, 1), (coin50, 1), coin, 2)
  |}"
    by eval
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_1_2_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_1)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply safe
    using choices orders by auto
qed

lemma step_drinks_before_select: "length ba = 1 \<Longrightarrow> step (tm drinks_before) 0 Map.empty (STR ''select'') ba = Some (select, 1, [], <R 1 := hd ba>)"
proof-
  assume premise: "length ba = 1"
  have possible_steps: "possible_steps (tm drinks_before) 0 Map.empty (STR ''select'') ba = {|(1, select)|}"
    apply (simp add: possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse)
    apply (simp add: tm_def drinks_before_def Set.filter_def)
    apply safe
    using premise
            apply (simp_all add: transitions)
    by force
  show ?thesis
    apply (simp add: step_def possible_steps)
    apply (simp add: select_def)
    apply (rule ext)
    by (simp add: hd_input2state premise)
qed

lemma possible_steps_merge_1_2_select: "length b = 1 \<Longrightarrow> possible_steps (tm merged_1_2) 0 r (STR ''select'') b = {|(1, select)|}"
  apply (simp add: possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse)
  apply (simp add: tm_def merged_1_2_def Set.filter_def)
  apply safe
       apply (simp_all add: transitions)
  by force

lemma no_direct_subsumption_coin_coin50: "\<not> directly_subsumes (tm drinks_before) (tm merged_1_2) 1 coin coin50"
proof-
  have subsumption_violation: "(\<exists>i r. satisfies_context r \<lbrakk>V (R 1) \<mapsto> cexp.Bc True\<rbrakk> \<and>
           apply_guards (Guard coin50) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))) \<and>
           apply_outputs (Outputs coin50) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))) \<noteq>
           apply_outputs (Outputs coin) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))))"
    apply (rule_tac x="[Num 50]" in exI)
    apply (rule_tac x="<R 1 := (Str ''coke'')>" in exI)
    apply standard
     defer
    apply (simp add: coin50_def coin_def)
     apply (simp add: satisfies_context_def consistent_def datastate2context_def)
     apply (rule_tac x="<R 1 := (Str ''coke'')>" in exI)
     apply clarify
     apply simp
     apply (case_tac r)
        apply simp
       apply simp
       apply (case_tac x2)
    by auto
  show ?thesis
    apply (simp add: directly_subsumes_def)
    apply standard
    apply (rule_tac x="[((STR ''select''), [(Str ''coke'')])]" in exI)
    apply standard
     apply (simp add: accepts_trace_def)
     apply (rule accepts.step)
      apply (simp add: step_drinks_before_select)
     apply (rule accepts.base)
    apply standard
     apply (rule gets_us_to.step_some)
      apply (simp add: step_drinks_before_select)
     apply (simp add: gets_us_to.base)
    apply (simp add: anterior_context_def step_def possible_steps_merge_1_2_select select_posterior)
    by (simp add: subsumes_def subsumption_violation)
qed

lemma step_drinks_before_coin_50: "step (tm drinks_before) 1 <R 1 := d> (STR ''coin'') [Num 50] = Some (coin50, 2, [Some (Num 50)], <R 1 := d, R 2 := Num 50>)"
proof-
  have possible_steps: "possible_steps (tm drinks_before) 1 <R 1 := d> (STR ''coin'') [Num 50] = {|(2, coin50)|}"
    apply (simp add: possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse)
    apply (simp add: Set.filter_def tm_def drinks_before_def)
    apply safe
          apply (simp_all add: transitions)
    by force
  show ?thesis
    apply (simp add: step_def possible_steps)
    apply (simp add: coin50_def)
    apply (rule ext)
    by simp
qed

lemma possible_steps_merge_1_2_coin50: "possible_steps (tm merged_1_2) 1 r (STR ''coin'') [Num 50] = {|(1, coin), (1, coin50)|}"
  apply (simp add: possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse)
  apply (simp add: Set.filter_def tm_def merged_1_2_def)
  apply safe
         apply (simp_all add: transitions)
   apply force
  by force

lemma no_direct_subsumption_coin50_coin: "\<not> directly_subsumes (tm drinks_before) (tm merged_1_2) 2 coin50 coin"
proof-
  have subsumption_violation: "(\<exists>i r. satisfies_context r \<lbrakk>V (R 1) \<mapsto> cexp.Bc True\<rbrakk> \<and>
           apply_guards (Guard coin) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))) \<and>
           apply_outputs (Outputs coin) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))) \<noteq>
           apply_outputs (Outputs coin50) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))))"
    apply (rule_tac x="[Num 50]" in exI)
    apply (rule_tac x="<R 1 := (Str ''coke'')>" in exI)
    apply standard
     defer
    apply (simp add: coin50_def coin_def)
     apply (simp add: satisfies_context_def consistent_def datastate2context_def)
     apply (rule_tac x="<R 1 := (Str ''coke'')>" in exI)
     apply clarify
     apply simp
     apply (case_tac r)
        apply simp
       apply simp
       apply (case_tac x2)
    by auto
  show ?thesis
    apply (simp add: directly_subsumes_def)
    apply standard
    apply (rule_tac x="[((STR ''select''), [(Str ''coke'')]), ((STR ''coin''), [Num 50])]" in exI)
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
    apply (simp add: anterior_context_def step_def possible_steps_merge_1_2_select select_posterior)
    apply (simp add: possible_steps_merge_1_2_coin50 fis_singleton_def is_singleton_def)
    apply standard
     apply (simp add: transitions)
    by (simp add: subsumes_def subsumption_violation)
qed

lemma possible_steps_merge_1_2_update_select: "length b = 1 \<Longrightarrow> possible_steps (tm merge_1_2_update) 0 r (STR ''select'') b = {|(1, select_update)|}"
proof-
  assume premise: "length b = 1"
  show ?thesis
    apply (simp add: possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse)
    apply (simp add: Set.filter_def merge_1_2_update_def tm_def)
    apply safe
    using premise
         apply (simp_all add: transitions)
    by force
qed

lemma drinks_before_step_0_invalid: "\<not> (aa = (STR ''select'') \<and> length b = 1) \<Longrightarrow>
        nondeterministic_step (tm drinks_before) 0 Map.empty aa b = None"
proof-
  assume premise: "\<not> (aa = (STR ''select'') \<and> length b = 1)"
  have possible_steps: "possible_steps (tm drinks_before) 0 Map.empty aa b = {||}"
    apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse)
    apply (simp add: tm_def drinks_before_def Set.filter_def)
    apply safe
    using premise
    by (simp_all add: transitions premise)
  show ?thesis
    by (simp add: nondeterministic_step_def possible_steps)
qed

lemma drinks_before_1_invalid: "\<not> (aa = (STR ''coin'') \<and> b = [Num 50]) \<Longrightarrow> nondeterministic_step (tm drinks_before) 1 r aa b = None"
proof-
  assume premise: "\<not>(aa = (STR ''coin'') \<and> b = [Num 50])"
  have possible_steps: "possible_steps (tm drinks_before) 1 r aa b = {||}"
    apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse)
    apply (simp add: drinks_before_def tm_def Set.filter_def)
    apply safe
    using premise
    apply (simp_all add: transitions hd_input2state)
    by (metis One_nat_def hd_Cons_tl length_0_conv length_Suc_conv list.sel(3))
  show ?thesis
    by (simp add: nondeterministic_step_def possible_steps)
qed

lemma possible_steps_drinks_before_coin: "length b = 1 \<Longrightarrow> possible_steps (tm drinks_before) 2 r (STR ''coin'') b = {|(2, coin)|}"
proof-
  assume premise: "length b = 1"
  show ?thesis
    apply (simp add: possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse)
    apply (simp add: tm_def drinks_before_def Set.filter_def)
    apply safe
          apply (simp_all add: transitions)
    using premise
    by force
qed

lemma possible_steps_merge_1_2_update_coin: "length b = 1 \<Longrightarrow> (1, coin) |\<in>| possible_steps (tm merge_1_2_update) 1 r2 (STR ''coin'') b"
proof-
  assume premise: "length b = 1"
  show ?thesis
    apply (simp add: possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse fmember_def)
    apply (simp add: tm_def merge_1_2_update_def Set.filter_def transitions)
    using premise
    by force
qed

lemma nondeterministic_step_drinks_before_invalid_step_2: " \<not> (aa = (STR ''coin'') \<and> length b = 1) \<Longrightarrow>
       \<not> (aa = (STR ''vend'') \<and> b = []) \<Longrightarrow> nondeterministic_step (tm drinks_before) 2 r1 aa b = None"
proof-
  assume premise1:  "\<not> (aa = (STR ''coin'') \<and> length b = 1)"
  assume premise2: "\<not> (aa = (STR ''vend'') \<and> b = [])"
  have possible_steps: "possible_steps (tm drinks_before) 2 r1 aa b = {||}"
    apply (simp add: possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse)
    apply (simp add: tm_def drinks_before_def Set.filter_def)
    apply safe
    using premise1 premise2
    by (simp_all add: transitions)
  show ?thesis
    by (simp add: nondeterministic_step_def possible_steps)
qed

lemma impossible_steps_drinks_before_vend: "\<nexists>n. r (R 2) = Some (Num n) \<Longrightarrow> nondeterministic_step (tm drinks_before) 2 r (STR ''vend'') i = None"
proof-
  assume premise: "\<nexists>n. r (R 2) = Some (Num n)"
  have possible_steps: "possible_steps (tm drinks_before) 2 r (STR ''vend'') i = {||}"
    apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse)
    apply (simp add: Set.filter_def tm_def drinks_before_def)
    apply safe
    using premise
      apply (simp_all add: transitions)
    using MaybeBoolInt.elims apply force
    by (metis (no_types, lifting) MaybeBoolInt.elims option.case_eq_if option.simps(3))
  show ?thesis
    by (simp add: nondeterministic_step_def possible_steps)
qed

lemma drinks_before_vend_fail: "r (R 2) = Some (Num x1) \<Longrightarrow> x1 < 100 \<Longrightarrow> possible_steps (tm drinks_before) 2 r (STR ''vend'') [] = {|(2, vend_fail)|}"
    apply (simp add: possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse)
    apply (simp add: tm_def drinks_before_def Set.filter_def)
    apply safe
          apply (simp_all add: transitions)
    by force

lemma merge_1_2_update_vend_fail: "r (R 2) = Some (Num x1) \<Longrightarrow> x1 < 100 \<Longrightarrow> possible_steps (tm merge_1_2_update) 1 r (STR ''vend'') [] = {|(1, vend_fail)|}"
  apply (simp add: possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse)
  apply (simp add: tm_def merge_1_2_update_def Set.filter_def)
    apply safe
          apply (simp_all add: transitions)
  by force

lemma drinks_before_vend_success: "r (R 2) = Some (Num x1) \<Longrightarrow> x1 \<ge> 100 \<Longrightarrow> possible_steps (tm drinks_before) 2 r (STR ''vend'') [] = {|(3, vend_success)|}"
    apply (simp add: possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse)
    apply (simp add: tm_def drinks_before_def Set.filter_def)
    apply safe
          apply (simp_all add: transitions)
  by force

lemma merge_1_2_update_vend_success: "r (R 2) = Some (Num x1) \<Longrightarrow> x1 \<ge> 100 \<Longrightarrow> possible_steps (tm merge_1_2_update) 1 r (STR ''vend'') [] = {|(3, vend_success)|}"
  apply (simp add: possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse)
  apply (simp add: tm_def merge_1_2_update_def Set.filter_def)
    apply safe
          apply (simp_all add: transitions)
  by force

lemma drinks_before_ends_at_3: "nondeterministic_step (tm drinks_before) 3 r aa b = None"
proof-
  have possible_steps: "possible_steps (tm drinks_before) 3 r aa b = {||}"
    apply (simp add: possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse)
    by (simp add: tm_def drinks_before_def Set.filter_def)
  show ?thesis
    by (simp add: nondeterministic_step_def possible_steps)
qed

lemma simulation_2_1: "\<forall>r. nondeterministic_simulates_trace (tm merge_1_2_update) (tm drinks_before) 1 2 r r lst update_before"
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
    apply (case_tac "aa = (STR ''coin'') \<and> length b = 1")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: update_before_def)
        apply (simp add: nondeterministic_step_def possible_steps_drinks_before_coin)
    using possible_steps_merge_1_2_update_coin  apply blast
      apply simp
      apply simp
    using nondeterministic_step_drinks_before_invalid_step_2
     apply blast
    apply (case_tac "aa = (STR ''vend'') \<and> b = []")
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
    apply (simp add: transitions(4))
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

lemma simulation_1_1: "nondeterministic_simulates_trace (tm merge_1_2_update) (tm drinks_before) 1 1 <R 1 := d, R 2 := Num 0> <R 1 := d> ((aa, b) # list) update_before"
proof-
  have coin50_updates: "(EFSM.apply_updates (Updates coin50) (\<lambda>x. case x of I n \<Rightarrow> input2state [Num 50] 1 (I n) | R n \<Rightarrow> <R 1 := d, R 2 := Num 0> (R n))
       <R 1 := d, R 2 := Num 0>) = <R 1 := d, R 2 := Num 50>"
    apply (rule ext)
    by (simp add: coin50_def)
  have merge_1_2_update_possible_steps_coin_50: "possible_steps (tm merge_1_2_update) 1 <R 1 := d, R 2 := Num 0> (STR ''coin'') [Num 50] = {|(1, coin50), (1, coin)|}"
    apply (simp add: possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse)
    apply (simp add: Set.filter_def tm_def merge_1_2_update_def)
    apply safe
           apply (simp_all add: transitions)
     apply force
    by force
  show ?thesis
    apply (case_tac "aa = (STR ''coin'') \<and> b = [Num 50]")
     prefer 2
     apply (rule nondeterministic_simulates_trace.step_none)
    using drinks_before_1_invalid
    apply auto[1]
    apply (rule nondeterministic_simulates_trace.step_some)
        apply (simp add: update_before_def)
       apply (simp add: step_drinks_before_coin_50 step_nondet_step_equiv)
       apply (simp add: merge_1_2_update_possible_steps_coin_50)
      apply auto[1]
      apply simp
     apply (simp add: transitions)
     apply (simp add: coin50_updates)
    by (simp add: simulation_2_1)
qed

lemma simulation_0_0: "nondeterministic_simulates_trace (tm merge_1_2_update) (tm drinks_before) 0 0 Map.empty Map.empty ((aa, b) # t) update_before"
proof-
  have select_updates: "length b = 1 \<Longrightarrow> EFSM.apply_updates (Updates select_update) (\<lambda>x. case x of I n \<Rightarrow> input2state b 1 (I n) | R x \<Rightarrow> Map.empty x) Map.empty = <R 1 := hd b, R 2 := Num 0>"
    apply (simp add: select_update_def)
    apply (rule ext)
    by (simp add: hd_input2state)
  show ?thesis
  apply (case_tac "aa = (STR ''select'') \<and> length b = 1")
     apply (rule nondeterministic_simulates_trace.step_some)
          apply (simp add: update_before_def)
         apply (simp add: step_nondet_step_equiv step_drinks_before_select)
        apply (simp add: possible_steps_merge_1_2_update_select)
       apply simp
      apply (simp add: select_update_def)
     defer
     apply (rule nondeterministic_simulates_trace.step_none)
     apply (simp add: drinks_before_step_0_invalid)
    apply (simp add: select_updates)
    apply (case_tac t)
     apply (simp add: nondeterministic_simulates_trace.base)
    apply (case_tac a)
    by (simp add: simulation_1_1)
qed

lemma simulation_aux: "nondeterministic_simulates_trace (tm merge_1_2_update) (tm drinks_before) 0 0 Map.empty Map.empty t update_before"
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

lemma simulation: "nondeterministic_simulates (tm merge_1_2_update) (tm drinks_before) update_before"
  apply (simp add:nondeterministic_simulates_def)
  apply (rule allI)
  by (simp add: simulation_aux)

lemma regsimp1: "(\<lambda>a. if a = R 1 then Some d else None) = <R 1 := d>"
  by auto

lemma contextsimp1: "(\<lambda>a. if a = V (R 2) then cexp.Eq (Num 0) else if a = V (R 1) then cexp.Bc True else \<lbrakk>\<rbrakk> a) = 
                     \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk>"
  by auto

lemma regsimp2: "(\<lambda>a. if a = R 2 then Some (Num n) else if a = R 1 then Some d else None) = <R 1 := d, R 2 := Num n>"
  by auto

lemma no_route_from_3_to_anywhere: "s \<noteq> 3 \<Longrightarrow> \<not>gets_us_to s (tm drinks_before) 3 r' p"
  apply safe
  apply (rule gets_us_to.cases)
     apply simp
    apply simp
   apply clarify
  apply (simp add: drinks_before_ends_at_3 nondeterministic_step_none)
  by simp

lemma no_route_from_2_to_1: "\<forall>r. \<not>gets_us_to 1 (tm drinks_before) 2 r p"
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
    apply (case_tac "aa = (STR ''coin'') \<and> length b = 1")
     apply (simp add: step_def possible_steps_drinks_before_coin)
    apply (case_tac "aa = (STR ''vend'') \<and> b = []")
    defer
    apply (simp add: nondeterministic_step_drinks_before_invalid_step_2 nondeterministic_step_none)
     apply clarify
     apply simp
    apply (case_tac "ra (R 2)")
      apply (simp add: impossible_steps_drinks_before_vend nondeterministic_step_none)
    apply (case_tac aa)
      defer
      apply (simp add: impossible_steps_drinks_before_vend nondeterministic_step_none)
    apply clarify
    apply simp
    apply (case_tac "x1 < 100")
     apply (simp add: step_def drinks_before_vend_fail)
    apply (simp add: step_def drinks_before_vend_success)
    apply (simp add: vend_success_def)
    apply clarify
    by (simp add: no_route_from_3_to_anywhere)
qed

lemma drinks_before_1_step_invalid: "(aa, ba) \<noteq> ((STR ''coin''), [Num 50]) \<Longrightarrow> step (tm drinks_before) 1 r aa ba = None"
proof-
  assume premise: "(aa, ba) \<noteq> ((STR ''coin''), [Num 50])"
  have possible_steps: "possible_steps (tm drinks_before) 1 r aa ba = {||}"
    apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse)
    apply (simp add: Set.filter_def tm_def drinks_before_def)
    apply (simp add: transitions hd_input2state)
    using premise
    by (metis One_nat_def hd_Cons_tl length_0_conv length_Suc_conv list.sel(3))
  show ?thesis
    by (simp add: step_def possible_steps)
qed

lemma stop_at_1: "step (tm drinks_before) 1 <R 1 := d> aa ba = Some (uw, s', ux, r') \<Longrightarrow> \<not>gets_us_to 1 (tm drinks_before) 1 <R 1 := d> ((aa, ba) # p)"
  apply safe
  apply (rule gets_us_to.cases)
     apply simp
    apply simp
  apply (case_tac "(aa, ba) = ((STR ''coin''), [Num 50])")
   apply (simp add: step_drinks_before_coin_50)
    apply clarify
    apply simp
    apply clarify
    apply simp
   apply (simp add: step_drinks_before_coin_50)
    apply clarify
    apply (simp add: no_route_from_2_to_1)
   apply clarify
   apply simp
  using drinks_before_1_step_invalid
  apply (metis option.simps(3) prod.sel(1) prod.sel(2))
   apply clarify
  by simp

lemma gets_us_to_aux: "gets_us_to 1 (tm drinks_before) 1 <R 1 := d> p \<Longrightarrow> accepts (tm drinks_before) 1 <R 1 := d> p \<Longrightarrow>
          posterior_sequence \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> (tm merge_1_2_update) 1 <R 1 := d, R 2 := Num 0> p =
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
    apply (case_tac "step (tm merge_1_2_update) 1 <R 1 := d, R 2 := Num 0> aa ba")
     apply simp
    apply simp
    apply clarify
    by (simp add: no_step_none)
qed

lemma accepts_trace_anterior: "accepts_trace (tm drinks_before) p \<Longrightarrow> gets_us_to 1 (tm drinks_before) 0 Map.empty p \<Longrightarrow> anterior_context (tm merge_1_2_update) p = \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> Eq (Num 0)\<rbrakk>"
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
    apply (case_tac "aa = (STR ''select'') \<and> length b = 1")
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
     apply (simp add: step_drinks_before_select)
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

lemma coin_subsumes_coin50: "subsumes \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> coin coin50"
proof-
  have consistent_medial_coin: "consistent \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk>"
    apply (simp add: consistent_def)
    apply (rule_tac x="<R 1 := (Str ''coke''), R 2 := Num 0, I 1 := Num 50>" in exI)
    apply (rule allI)
    by (simp add: consistent_empty_4)
  have medial_coin50: "medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> (Guard coin50) =
        \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0), V (I 1) \<mapsto> Eq (Num 50)\<rbrakk>"
    apply (rule ext)
    by (simp add: transitions)
  have consistent_medial_coin50: "consistent \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0), V (I 1) \<mapsto> cexp.Eq (Num 50)\<rbrakk>"
    apply (simp add: consistent_def)
    apply (rule_tac x="<R 1 := (Str ''coke''), R 2 := Num 0, I 1 := Num 50>" in exI)
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
     apply (simp add: transitions)
     apply (rule_tac x="[Num 50]" in exI)
     apply (rule_tac x="<R 2 := Num 0>" in exI)
     apply simp
    apply standard
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

lemma coin_directly_subsumes_coin50: "directly_subsumes (tm drinks_before) (tm merge_1_2_update) 1 coin coin50"
  apply (simp add: directly_subsumes_def)
  apply standard
  apply clarify
   apply (simp add: accepts_trace_anterior coin_subsumes_coin50)
  apply (rule_tac x="\<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk>" in exI)
  by (simp add: coin_subsumes_coin50)

lemma not_coin50_directly_subsumes_coin: "\<not> directly_subsumes (tm drinks_before) (tm merge_1_2_update) 2 coin50 coin"
proof-
  have possible_steps: "possible_steps (tm merge_1_2_update) 1
        (EFSM.apply_updates (Updates select_update)
          (case_vname (\<lambda>n. if n = 1 then Some ((Str ''coke'')) else input2state [] (1 + 1) (I n)) Map.empty) Map.empty)
        (STR ''coin'') [Num 50] = {|(1, coin50), (1, coin)|}"
    apply (simp add: possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse)
    apply (simp add: Set.filter_def tm_def merge_1_2_update_def)
    apply safe
           apply (simp_all add: transitions)
     apply force
    by force
  have coin_neq_coin50: "coin \<noteq> coin50"
    by (simp add: transitions)
  have select_update_posterior: "posterior \<lbrakk>\<rbrakk> select_update = \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> Eq (Num 0)\<rbrakk>"
    unfolding posterior_def Let_def
    apply (rule ext)
    by (simp add: transitions remove_input_constraints_def)
  have coin50_doesnt_subsume_coin: "\<not> subsumes \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> coin50 coin"
  proof-
    have subsumption_violation: "(\<exists>r i. cval (medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> (Guard coin) r) i = Some True \<and>
             cval (medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> (Guard coin50) r) i \<noteq> Some True)"
      apply (simp add: transitions)
      by auto
    show ?thesis
      by (simp add: subsumes_def subsumption_violation)
  qed
  show ?thesis
    apply (simp add: directly_subsumes_def)
    apply standard
  apply (rule_tac x="[((STR ''select''), [(Str ''coke'')]), ((STR ''coin''), [Num 50])]" in exI)
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
    apply (simp add: step_def possible_steps_merge_1_2_update_select possible_steps)
    apply (simp add: fis_singleton_def is_singleton_def coin_neq_coin50)
    by (simp add: select_update_posterior coin50_doesnt_subsume_coin)
qed

lemma merge_transitions: "merge_transitions drinks_before merged_1_2 (leaves 1 drinks_before) (leaves 2 drinks_before) (leaves 1 merged_1_2) 1 1 coin50 1
           coin 2 null_generator (\<lambda>a b c d e. Some (merge_1_2_update, update_mapping, update_before)) True = Some merge_1_2_update"
proof-
  have leaves_1_drinks_before: "leaves 1 drinks_before = 1"
  proof-
    have set_filter: "Set.filter (\<lambda>x. \<exists>a b ba. x = (1, (a, b), ba)) (fset drinks_before) = {(1, (1, 2), coin50)}"
      apply (simp add: Set.filter_def drinks_before_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter_def fthe_elem_def Abs_fset_inverse set_filter)
  qed
  have leaves_2_drinks_before: "leaves 2 drinks_before = 2"
  proof-
    have set_filter: "Set.filter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) (fset drinks_before) = {(2, (2, 2), coin)}"
      apply (simp add: Set.filter_def drinks_before_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter_def fthe_elem_def Abs_fset_inverse set_filter)
  qed
  have leaves_1_drinks_before: "leaves 1 drinks_before = 1"
  proof-
    have set_filter: "Set.filter (\<lambda>x. \<exists>a b ba. x = (1, (a, b), ba)) (fset drinks_before) = {(1, (1, 2), coin50)}"
      apply (simp add: Set.filter_def drinks_before_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter_def fthe_elem_def Abs_fset_inverse set_filter)
  qed
  have easy_merge: "easy_merge drinks_before merged_1_2 (leaves 1 drinks_before) (leaves 2 drinks_before) (leaves 1 merged_1_2) 1 1 coin50 1 coin 2
           null_generator = None"
    apply (simp add: easy_merge_def null_generator_def leaves_1_drinks_before leaves_2_drinks_before)
    by (simp add: no_direct_subsumption_coin_coin50 no_direct_subsumption_coin50_coin)
  have ffilter: "ffilter (\<lambda>x. snd x \<noteq> ((1, 1), coin50) \<and> snd x \<noteq> ((1, 1), coin)) merge_1_2_update = {|(0, (0, 1), select_update), (3, (1, 1), vend_fail), (4, (1, 3), vend_success)|}"
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse)
    apply (simp add: Set.filter_def merge_1_2_update_def)
    apply safe
    by (simp_all add: transitions)
  show ?thesis
    apply (simp add: merge_transitions_def easy_merge)
    by (simp add: simulation update_mapping_def leaves_2_drinks_before leaves_1_drinks_before)
qed

lemma nondeterministic_pairs_drinks_after: "nondeterministic_pairs drinks_after = {||}"
proof-
  have minus_1: "{(1, coin, 2), (1, vend_fail, 3), (3, vend_success, 4)} - {(1, vend_fail, 3)} = {(1, coin, 2), (3, vend_success, 4)}"
    apply (simp add: transitions)
    by auto
  have minus_2: "{(1, coin, 2), (1, vend_fail, 3), (3, vend_success, 4)} - {(3, vend_success, 4)} = {(1, coin, 2), (1, vend_fail, 3)}"
    apply (simp add: transitions)
    by auto
  have state_nondeterminism: "state_nondeterminism 1 {|(1, coin, 1), (1, vend_fail, 3), (3, vend_success, 4)|} = {|
(1, (3, 1), (vend_success, 4),
    vend_fail, 3),
   (1, (3, 1), (vend_success, 4),
   coin, 1),
   (1, (1, 3), (vend_fail, 3),
    vend_success, 4),
   (1, (1, 1), (vend_fail, 3),
   coin, 1),
   (1, (1, 3),
    (coin, 1),
    vend_success, 4),
   (1, (1, 1),
    (coin, 1),
    vend_fail, 3)|}"
    by eval
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def drinks_after_def outgoing_transitions_def fimage_def)
    apply (simp add: state_nondeterminism)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply safe
    by (simp_all add: choices)
qed

lemma merge_1_2_drinks_before: "merge drinks_before 1 2 null_generator (\<lambda>a b c d e. Some (merge_1_2_update, update_mapping, update_before)) = Some drinks_after"
proof-
  have arrives_2_merged_1_2: "arrives 2 merged_1_2 = 1 \<and> leaves 2 merged_1_2 = 1"
  proof-                                                
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_1_2 = {|(2, (1, 1), coin)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def merged_1_2_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def leaves_def ffilter)
  qed
  have arrives_1_merged_1_2: "arrives 1 merged_1_2 = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (1, (a, b), ba)) merged_1_2 = {|(1, (1, 1), coin50)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def merged_1_2_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have nondeterministic_pairs_merge_1_2_update: "nondeterministic_pairs merge_1_2_update = {|(1, (1, 1), (coin, 2), coin50, 1), (1, (1, 1), (coin50, 1), coin, 2)|}"
  proof-
    have minus_1: "{|(1, coin50, 1), (1, coin, 2), (1, vend_fail, 3), (3, vend_success, 4)|} |-| {|(1, coin, 2)|} = {|(1, coin50, 1), (1, vend_fail, 3), (3, vend_success, 4)|}"
      apply (simp add: transitions)
      by auto
    have minus_2: "{|(1, coin50, 1), (1, coin, 2), (1, vend_fail, 3), (3, vend_success, 4)|} |-| {|(1, vend_fail, 3)|} = {|(1, coin50, 1), (1, coin, 2), (3, vend_success, 4)|}"
      apply (simp add: transitions)
      by auto
    have minus_3: "{|(1, coin50, 1), (1, coin, 2), (1, vend_fail, 3), (3, vend_success, 4)|} |-| {|(3, vend_success, 4)|} = {|(1, coin50, 1), (1, coin, 2), (1, vend_fail, 3)|}"
      apply (simp add: transitions)
      by auto
    have state_nondeterminism_1: "state_nondeterminism 1 {|(1, coin50, 1), (1, coin, 2), (1, vend_fail, 3), (3, vend_success, 4)|} = {|
        (1, (3, 1), (vend_success, 4), vend_fail, 3),
        (1, (3, 1), (vend_success, 4), coin, 2),
        (1, (3, 1), (vend_success, 4), coin50, 1),
        (1, (1, 3), (vend_fail, 3), vend_success, 4),
        (1, (1, 1), (vend_fail, 3), coin, 2),
        (1, (1, 1), (vend_fail, 3), coin50, 1),
        (1, (1, 3), (coin, 2), vend_success, 4),
        (1, (1, 1), (coin, 2), vend_fail, 3),
        (1, (1, 1), (coin, 2), coin50, 1),
        (1, (1, 3), (coin50, 1), vend_success, 4),
        (1, (1, 1), (coin50, 1), vend_fail, 3),  
        (1, (1, 1), (coin50, 1), coin, 2)
      |}"
      by eval
    show ?thesis
      apply (simp add: nondeterministic_pairs_def S_def merge_1_2_update_def)
      apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_1)
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: choices)
  qed
  have arrives_2_merge_1_2_update: "arrives 2 merge_1_2_update = 1 \<and> leaves 2 merge_1_2_update = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merge_1_2_update = {|(2, (1, 1), coin)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def merge_1_2_update_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter leaves_def)
  qed
  have arrives_1_merge_1_2_update: "arrives 1 merge_1_2_update = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (1, (a, b), ba)) merge_1_2_update = {|(1, (1, 1), coin50)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def merge_1_2_update_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have leaves_2_drinks_before: "leaves 2 drinks_before = 2"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) drinks_before = {|(2, (2, 2), coin)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_before_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have leaves_1_drinks_before: "leaves 1 drinks_before = 1"
  proof-
      have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (1, (a, b), ba)) drinks_before = {|(1, (1, 2), coin50)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_before_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have easy_merge: "easy_merge drinks_before merge_1_2_update 1 2 1 1 1 coin50 1 coin 2 null_generator = Some drinks_after"
  proof-
    have ffilter: "ffilter (\<lambda>x. snd x \<noteq> ((1, 1), coin50) \<and> snd x \<noteq> ((1, 1), coin)) merge_1_2_update = {|(0, (0, 1), select_update), (3, (1, 1), vend_fail), (4, (1, 3), vend_success)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def merge_1_2_update_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      apply (simp add: easy_merge_def null_generator_def coin_directly_subsumes_coin50 not_coin50_directly_subsumes_coin)
      by (simp add: replace_transition_def ffilter drinks_after_def)
  qed
  have merge_coins: "merge_transitions drinks_before merge_1_2_update 1 2 1 1 1 coin50 1 coin 2 null_generator
                (\<lambda>a b c d e. Some (merge_1_2_update, update_mapping, update_before)) True = Some drinks_after"
    by (simp add: merge_transitions_def easy_merge)
  have arrives_1_merge_1_2_update: "arrives 1 merge_1_2_update = 1"
    by eval
  have leaves_1_merge_1_2_update:  "leaves 1 merge_1_2_update = 1"
    by eval
  show ?thesis
    apply (simp add: merge_def merge_states_1_2)
    apply (simp add: nondeterminism_def nondeterministic_pairs_merged_1_2 arrives_2_merged_1_2
           arrives_1_merged_1_2 merge_states_reflexive max_def coin_lt_coin50)
    apply (simp add: merge_transitions nondeterminism_def nondeterministic_pairs_drinks_after)
    apply (simp add: nondeterministic_pairs_merge_1_2_update arrives_2_merge_1_2_update merge_states_reflexive max_def coin_lt_coin50 arrives_1_merge_1_2_update)
    by (simp add: leaves_2_drinks_before leaves_1_merge_1_2_update leaves_1_drinks_before merge_coins nondeterministic_pairs_drinks_after nondeterminism_def)
qed

lemma scoring_2: "sorted_list_of_fset (score drinks_after naive_score) = []"
proof-
  have ffilter: "ffilter (\<lambda>(x, y). x < y) (Inference.S drinks_after |\<times>| Inference.S drinks_after) = {|(0, 1), (1, 3), (0, 3)|}"
    apply (simp add: S_def drinks_after_def fprod_def ffilter_def fset_both_sides Abs_fset_inverse)
    apply (simp add: Set.filter_def)
    by auto
  show ?thesis
    apply (simp add: score_def ffilter)
    apply (simp add: fimage_def outgoing_transitions_def drinks_after_def naive_score_empty)
    apply (simp add: transitions naive_score_def fprod_def)
    by (simp add: sorted_list_of_fset_def)
qed
    
lemma "infer drinks_before naive_score null_generator (\<lambda>a b c d e. Some (merge_1_2_update, update_mapping, update_before)) = drinks_after"
proof-
  show ?thesis
    by (simp add: scoring_1 merge_1_2_drinks_before scoring_2)
qed
end