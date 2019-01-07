theory Paper_Example
imports Inference SelectionStrategies
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

definition drinks_before :: iEFSM where
  "drinks_before = {|(0, (0, 1), select), (1, (1, 2), coin50), (2, (2, 2), coin), (3, (2, 2), vend_fail), (4, (2, 3), vend_success)|}"

definition drinks_after :: iEFSM where
  "drinks_after = {|(0, (0, 1), select_update), (1, (1, 1), coin), (2, (1, 1), vend_fail), (3, (1, 3), vend_success)|}"

definition merge_1_2_update :: iEFSM where
  "merge_1_2_update = {|(0, (0, 1), select_update), (1, (1, 1), coin50), (2, (1, 1), coin), (3, (1, 1), vend_fail), (4, (1, 3), vend_success)|}"

definition update_mapping :: "nat \<Rightarrow> nat" where
  "update_mapping x = x"

definition update_before :: "nat \<Rightarrow> nat" where
  "update_before x = (if x = 2 then 1 else x)"

definition modifier :: update_modifier where
  "modifier a b c d e =  Some (merge_1_2_update, update_mapping, update_before)"

lemma scoring_1: "sorted_list_of_fset (score drinks_before naive_score) = [(0, 0, 1), (0, 0, 2), (0, 0, 3), (0, 1, 3), (0, 2, 3), (1, 1, 2)]"
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
  have score: "score drinks_before naive_score = {|(0, 0, 1), (0, 0, 2), (0, 0, 3), (1, 1, 2), (0, 1, 3), (0, 2, 3)|}"
    apply (simp add: score_def S_drinks_before ffilter)
    apply (simp add: fimage_def outgoing_transitions_def drinks_before_def naive_score_empty)
    by (simp add: score_0_1 score_0_2 score_1_2)
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

lemma nondeterministic_pairs_merged_1_2: "nondeterministic_pairs merged_1_2 = {|(1, (1, 1), (coin, 2), coin50, 1)|}"
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
      (1, (1, 1), (coin50, 1), coin, 2),
      (1, (1, 1), (coin50, 1), vend_fail, 3),
      (1, (1, 3), (coin50, 1), vend_success, 4),
      (1, (1, 3), (vend_fail, 3), vend_success, 4),
      (1, (1, 1), (vend_fail, 3), coin50, 1),
      (1, (1, 1), (vend_fail, 3), coin, 2),
      (1, (1, 1), (coin, 2), coin50, 1),
      (1, (1, 1), (coin, 2), vend_fail, 3),
      (1, (1, 3), (coin, 2), vend_success, 4)
    |}"
    apply (simp add: state_nondeterminism_def fimage_def fset_both_sides Abs_fset_inverse)
    apply (simp add: minus_1 minus_2 minus_3)
    by auto
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_1_2_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_1)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply safe
    using choices orders by auto
qed

lemma step_drinks_before_select: "length ba = 1 \<Longrightarrow> step (tm drinks_before) 0 Map.empty ''select'' ba = Some (select, 1, [], <R 1 := hd ba>)"
proof-
  assume premise: "length ba = 1"
  have possible_steps: "possible_steps (tm drinks_before) 0 Map.empty ''select'' ba = {|(1, select)|}"
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

lemma possible_steps_merge_1_2_select: "length b = 1 \<Longrightarrow> possible_steps (tm merged_1_2) 0 r ''select'' b = {|(1, select)|}"
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
      apply (simp add: step_drinks_before_select)
     apply (simp add: gets_us_to.base)
    apply (simp add: anterior_context_def step_def possible_steps_merge_1_2_select select_posterior)
    by (simp add: subsumes_def subsumption_violation)
qed

lemma step_drinks_before_coin_50: "step (tm drinks_before) 1 <R 1 := d> ''coin'' [Num 50] = Some (coin50, 2, [Some (Num 50)], <R 1 := d, R 2 := Num 50>)"
proof-
  have possible_steps: "possible_steps (tm drinks_before) 1 <R 1 := d> ''coin'' [Num 50] = {|(2, coin50)|}"
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

lemma possible_steps_merge_1_2_coin50: "possible_steps (tm merged_1_2) 1 r ''coin'' [Num 50] = {|(1, coin), (1, coin50)|}"
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

lemma simulation_0_0: "nondeterministic_simulates_trace (tm merge_1_2_update) (tm drinks_before) 0 0 Map.empty Map.empty ((aa, b) # t) update_before"
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

lemma "merge_transitions drinks_before merged_1_2 (leaves 2 drinks_before) (leaves 1 drinks_before) 1 1 1 coin 2 coin50 1 null_generator
           (\<lambda>a b c d e. Some (merge_1_2_update, update_mapping, update_before)) True = Some a"
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
  have leaves_2_coin_before: "leaves 2 drinks_before = 2"
  proof-
    have set_filter: "Set.filter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) (fset drinks_before) = {(2, (2, 2), coin)}"
      apply (simp add: Set.filter_def drinks_before_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter_def fthe_elem_def Abs_fset_inverse set_filter)
  qed
  have easy_merge: "easy_merge drinks_before merged_1_2 (leaves 2 drinks_before) (leaves 1 drinks_before) 1 1 1 coin 2 coin50 1 null_generator = None"
    apply (simp add: easy_merge_def null_generator_def leaves_1_drinks_before leaves_2_coin_before)
    by (simp add: no_direct_subsumption_coin_coin50 no_direct_subsumption_coin50_coin)
  show ?thesis
    apply (simp add: merge_transitions_def easy_merge)

lemma "merge drinks_before 1 2 null_generator (\<lambda>a b c d e. Some (merge_1_2_update, update_mapping, update_before)) = Some merge_1_2_update"
  apply (simp add: merge_def merge_states_1_2)
  apply (simp add: nondeterminism_def nondeterministic_pairs_merged_1_2)


lemma "infer drinks_before naive_score null_generator (\<lambda>a b c d e. Some (merge_1_2_update, update_mapping, update_before)) = drinks_after"
proof-
  show ?thesis
    apply (simp add: scoring_1)
qed
end