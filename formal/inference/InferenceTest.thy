theory InferenceTest
imports Learn_EFSM Trace_Matches Increment_Reset Code_Generation
begin

declare One_nat_def [simp del]

definition "heuristics = try_heuristics [heuristic_1 traces, insert_increment]"

termination infer sorry
termination resolve_nondeterminism sorry

abbreviation "coin_general \<equiv> \<lparr>Label = STR ''coin'', Arity = 1, Guard = [], Outputs = [Plus (V (R 1)) (V (I 1))], Updates = [(R 1, Plus (V (R 1)) (V (I 1)))]\<rparr>"
abbreviation "vend_initialise \<equiv> \<lparr>Label = STR ''vend'', Arity = 0, Guard = [], Outputs = [L (value.Str STR ''pepsi'')], Updates = [(R 1, L (Num 0))]\<rparr>"
abbreviation "coin50_initialise \<equiv> \<lparr>Label = STR ''coin'', Arity = 1, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 100)], Updates = [(R 1, L (Num 0))]\<rparr>"

definition "heuristics_2_9 = {|(0, (0, 1), select coke),
     (1, (0, 7), select pepsi),
     (2, (1, 2), coin_general),
     (3, (1, 5), coin 100 100),
     (4, (2, 3), coin50_initialise),
     (5, (3, 4), vend coke),
     (6, (5, 6), vend coke),
     (7, (7, 1), coin_general),
     (8, (1, 2), coin_general),
     (9, (2, 10), vend_initialise)|}"

lemma choice_coin_specific_coin_general:"choice (coin m n) coin_general"
  apply (simp add: choice_def)
  by auto

lemma nondeterministic_pairs_heuristics_2_9: "nondeterministic_pairs heuristics_2_9 = {|
(1, (2, 5), (coin_general, 8), coin 100 100, 3),
(1, (2, 2), (coin_general, 8), coin_general, 2),
(1, (5, 2), (coin 100 100, 3), coin_general, 8),
(1, (5, 2), (coin 100 100, 3), coin_general, 2),
(1, (2, 2), (coin_general, 2), coin_general, 8),
(1, (2, 5), (coin_general, 2), coin 100 100, 3)
|}"
proof-
  have state_nondeterminism_1: "state_nondeterminism 1 {|(2, coin_general, 2), (5, coin 100 100, 3), (2, coin_general, 8)|} = {|(1, (2, 5), (coin_general, 8), coin 100 100, 3), (1, (2, 2), (coin_general, 8), coin_general, 2),
   (1, (5, 2), (coin 100 100, 3), coin_general, 8), (1, (5, 2), (coin 100 100, 3), coin_general, 2),
   (1, (2, 2), (coin_general, 2), coin_general, 8), (1, (2, 5), (coin_general, 2), coin 100 100, 3)|}"
    by eval
  have state_nondeterminism_2: "state_nondeterminism 2
                                                       {|(3, \<lparr>Label = STR ''coin'', Arity = 1, Guard = [gexp.Eq (V (I 1)) (L (Num 50))],
                                                                Outputs = [L (Num 100)], Updates = [(R 1, L (Num 0))]\<rparr>,
                                                          4),
                                                         (10,
                                                          \<lparr>Label = STR ''vend'', Arity = 0, Guard = [],
                                                             Outputs = [L (value.Str STR ''pepsi'')], Updates = [(R 1, L (Num 0))]\<rparr>,
                                                          9)|} =  {|(2, (10, 3), (vend_initialise, 9),
    coin50_initialise, 4),
   (2, (3, 10),
    (coin50_initialise, 4),
    vend_initialise, 9)|}"
    by eval
  have state_nondeterminism_0:  "state_nondeterminism 0 {|(1, select coke, 0), (7, select pepsi, 1)|} = {|(0, (7, 1),
    (select pepsi, 1),
    select coke, 0),
   (0, (1, 7), (select coke, 0),
    select pepsi, 1)|}"
  by eval
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def heuristics_2_9_def)
    apply (simp add: outgoing_transitions_def fimage_def)
    apply (simp add: state_nondeterminism_1 state_nondeterminism_2 state_nondeterminism_0)
    apply (simp add: Abs_ffilter Set.filter_def)
    apply standard
     apply clarify
     apply simp
     apply (case_tac "ab = coin_general")
      apply simp
      apply (case_tac "ac = coin 100 100")
       apply auto[1]
      apply auto[1]
     apply (case_tac "ab = vend_initialise")
      apply (simp add: choice_def)
     apply (case_tac "ab = coin50_initialise")
      apply (simp add: choice_def)
     apply (case_tac "ab = coin 100 100")
      apply (case_tac "ac = coin_general")
       apply (simp add: choice_def)
       apply auto[1]
      apply simp
     apply (case_tac "ab = vend_initialise")
      apply simp
     apply simp
     apply (meson choice_symmetry no_choice_select_coke_select_pepsi)
    apply clarify
    apply simp
    apply (case_tac "ab = coin_general")
     apply (case_tac "ac = coin_general")
      apply (simp add: choice_def)
     apply (case_tac "ac = coin 100 100")
      apply (simp add: choice_def)
      apply auto[1]
     apply simp
    apply simp
    using choice_coin_specific_coin_general by blast
qed

definition "merge_5_2 = {|
(0, (0, 1), select coke),
   (1, (0, 7), select pepsi),
   (2, (1, 2), coin_general), (3, (1, 2), coin 100 100), (4, (2, 3), coin50_initialise),
   (5, (3, 4), vend coke),
   (6, (2, 6), vend coke),
   (7, (7, 1), coin_general), (8, (1, 2), coin_general), (9, (2, 10), vend_initialise)|}"

lemma merge_5_2: "merge_states 5 2 heuristics_2_9 = merge_5_2 \<and> merge_states 2 5 heuristics_2_9 = merge_5_2"
  by eval

lemma step_pta_select_pepsi: "step (tm pta) 0 Map.empty (STR ''select'') [(Str ''pepsi'')] = Some ((select pepsi), 7, [], <>)"
  apply (rule one_possible_step)
    apply (rule possible_steps_singleton)
    apply (simp add: Abs_ffilter Set.filter_def pta_def tm_def)
  using implode_coke implode_pepsi
  by auto

lemma step_pta_select_coke: "step (tm pta) 0 Map.empty (STR ''select'') [(Str ''coke'')] = Some ((select coke), 1, [], <>)"
  apply (rule one_possible_step)
    apply (rule possible_steps_singleton)
    apply (simp add: Abs_ffilter Set.filter_def pta_def tm_def)
  using implode_coke implode_pepsi
  by auto

  lemma posterior_select_drink: "posterior \<lbrakk>\<rbrakk> (select d) = \<lbrakk>\<rbrakk>"
    apply (rule posterior_consistent_medial)
      apply (simp add: medial_def List.maps_def pairs2context_def)
     apply (simp add: consistent_def)
     apply (rule_tac x="<I 1 := Str d>" in exI)
     defer
     apply (rule ext)
     apply (simp add: remove_obsolete_constraints_def)
    apply safe
      apply (simp add: cval_def)
     apply (simp add: cval_true)
    apply (case_tac r)
       apply (simp add: cval_true)
      apply (case_tac x2)
    using cval_def
    by auto

lemma coin_100_100_not_directly_subsumes_coin_general: "\<not> directly_subsumes (tm pta) (tm merge_5_2) 8 (coin 100 100) coin_general \<and>
                                                        \<not> directly_subsumes (tm pta) (tm merge_5_2) 1 coin_general (coin 100 100)"
proof-
  have select_pepsi: "step (tm merge_5_2) 0 Map.empty STR ''select'' [EFSM.Str pepsi] = Some (select pepsi, 7, [], <>)"
    apply (rule one_possible_step)
      defer
      apply simp
     apply simp
    apply (simp add: possible_steps_alt Abs_ffilter tm_def merge_5_2_def Set.filter_def)
    using implode_coke implode_pepsi
    by auto
  have step_merge_5_2_coin_7: "step (tm merge_5_2) 7 Map.empty STR ''coin'' [Num 50] = Some (coin_general, 1, [None], <>)"
    apply (rule one_possible_step)
      defer
      apply simp
     apply (rule ext)
     apply simp
    apply (simp add: possible_steps_alt Abs_ffilter Set.filter_def tm_def merge_5_2_def)
    by auto
  have posterior_coin_general: "posterior \<lbrakk>\<rbrakk> coin_general = \<lbrakk>\<rbrakk>"
    apply (rule posterior_consistent_medial)
      apply (simp add: medial_empty)
     apply simp
    apply (simp add: remove_obsolete_constraints_def)
    apply (rule ext)
    by (simp add: fprod_singletons)
  have select_coke: "step (tm merge_5_2) 0 Map.empty STR ''select'' [EFSM.Str coke] = Some (select coke, 1, [], <>)"
    apply (rule one_possible_step)
      apply (simp add: possible_steps_alt Abs_ffilter Set.filter_def tm_def merge_5_2_def)
    using implode_coke implode_pepsi
    by auto
  show ?thesis
    apply standard
    apply (rule gets_us_to_and_not_subsumes)
    apply (rule_tac x="[(STR ''select'', [Str pepsi]), (STR ''coin'', [Num 50])]" in exI)
    apply standard
     apply (simp add: accepts_trace_def)
     apply (rule accepts.step)
      apply (simp add: step_pta_select_pepsi)
     apply (rule accepts.step)
      apply (simp add: step_pta_coin50_7)
     apply (simp add: accepts.base)
    apply standard
     apply (rule step_some)
      apply (simp add: step_pta_select_pepsi)
     apply (rule step_some)
      apply (simp add: step_pta_coin50_7)
     apply (simp add: gets_us_to.base)
    apply (simp add: anterior_context_def)
    apply (simp add: select_pepsi step_merge_5_2_coin_7)
    apply (simp add: posterior_select_drink posterior_coin_general)
    apply (simp add: subsumes_def)
    using satisfies_context_empty apply fastforce
    apply (rule gets_us_to_and_not_subsumes)
    apply (rule_tac x="[(STR ''select'', [Str coke])]" in exI)
    apply standard
     apply (simp add: accepts_trace_def)
     apply (rule accepts.step)
      apply (simp add: step_pta_select_coke)
     apply (simp add: accepts.base)
    apply standard
     apply (rule step_some)
      apply (simp add: step_pta_select_coke)
     apply (simp add: gets_us_to.base)
    apply (simp add: anterior_context_def)
    apply (simp add: select_coke posterior_select_drink)
    apply (rule output_subsumption_violation)
    apply simp
    apply (rule_tac x="[Num 100]" in exI)
    apply simp
    apply (rule_tac x="<>" in exI)
    by (simp add: satisfies_context_empty)
qed

lemma pta_1_anterior_context: "accepts_trace (tm pta) p \<and> gets_us_to 1 (tm pta) 0 Map.empty p \<Longrightarrow> anterior_context (tm merge_5_2) p = \<lbrakk>\<rbrakk>"
proof(induct p)
  case Nil
  then show ?case
    by (simp add: anterior_context_def)
next
  have select_coke: "step (tm merge_5_2) 0 Map.empty STR ''select'' [EFSM.Str coke] = Some (select coke, 1, [], <>)"
    apply (rule one_possible_step)
      apply (simp add: possible_steps_alt Abs_ffilter Set.filter_def tm_def merge_5_2_def)
    using implode_coke implode_pepsi
    by auto
  have posterior_coke: "posterior \<lbrakk>\<rbrakk> (select coke) = \<lbrakk>\<rbrakk>"
    apply (rule posterior_consistent_medial)
      apply (simp add: medial_def pairs2context_def List.maps_def)
     apply (simp add: consistent_def)
     apply (rule_tac x="<I 1 := Str coke>" in exI)
     defer
     apply simp
    apply safe
      apply (simp add: cval_def)
     apply (simp add: cval_true)
    apply (case_tac r)
       apply (simp add: cval_def)
      apply (case_tac x2)
    using cval_def by auto
  case (Cons a p)
  then show ?case
    apply (simp add: accepts_trace_def anterior_context_def)
    apply (case_tac "a = (STR ''select'', [Str coke])")
     apply (simp add: select_coke posterior_coke)
    sorry
qed

lemma not_directly_subsumes_100_pta: "\<not> directly_subsumes (tm pta) (tm merge_5_2) 1 (coin 100 100) coin_general"
proof-
  have select_coke: "step (tm merge_5_2) 0 Map.empty STR ''select'' [EFSM.Str coke] = Some (select coke, 1, [], <>)"
    apply (rule one_possible_step)
      apply (simp add: possible_steps_alt Abs_ffilter Set.filter_def tm_def merge_5_2_def)
    using implode_coke implode_pepsi by auto
  show ?thesis
    apply (rule gets_us_to_and_not_subsumes)
 apply (rule_tac x="[(STR ''select'', [Str coke])]" in exI)
    apply standard
     apply (simp add: accepts_trace_def)
     apply (rule accepts.step)
      apply (simp add: step_pta_select_coke)
     apply (simp add: accepts.base)
    apply standard
     apply (rule step_some)
      apply (simp add: step_pta_select_coke)
     apply (simp add: gets_us_to.base)
    apply (simp add: anterior_context_def)
    apply (simp add: select_coke posterior_select_drink)
    apply (rule output_subsumption_violation)
    apply simp
    apply (rule_tac x="[Num 100]" in exI)
    apply simp
    apply (rule_tac x="<>" in exI)
    by (simp add: satisfies_context_empty)
qed

lemma minus: "{|(0::nat, (0::nat, 1::nat), select coke), (1, (0, 7), select pepsi), (2, (1, 2), coin_general), (3, (1, 5), coin 100 100),
                   (4, (2, 3), coin50_initialise), (5, (3, 4), vend coke), (6, (5, 6), vend coke), (7, (7, 1), coin_general),
                   (8, (1, 2), coin_general), (9, (2, 10), vend_initialise)|} |-|
                 {|(2, (1, 2), coin_general)|} =
{|(0, (0, 1), select coke),
   (1, (0, 7), select pepsi),
   (3, (1, 5), coin 100 100), (4, (2, 3), coin50_initialise),
   (5, (3, 4), vend coke),
   (6, (5, 6), vend coke),
   (7, (7, 1), coin_general), (8, (1, 2), coin_general), (9, (2, 10), vend_initialise)|}"
    apply (simp add: minus_fset_def fset_both_sides Abs_fset_inverse)
    by auto

lemma nondeterministic_pairs_heuristics_2_9_minus: "nondeterministic_pairs (heuristics_2_9 |-| {|(2, (1, 2), coin_general)|}) = {|
(1, (2, 5), (coin_general, 8), coin 100 100, 3), (1, (5, 2), (coin 100 100, 3), coin_general, 8)
|}"
proof-
  have state_nondeterminism_1: "state_nondeterminism 1 {|(5, coin 100 100, 3), (2, coin_general, 8)|} = {|(1, (2, 5), (coin_general, 8), coin 100 100, 3), (1, (5, 2), (coin 100 100, 3), coin_general, 8)|}"
    by eval
  have state_nondeterminism_2: "state_nondeterminism 2 {|(3, coin50_initialise, 4), (10, vend_initialise, 9)|} = {|(2, (10, 3), (vend_initialise, 9), coin50_initialise, 4), (2, (3, 10), (coin50_initialise, 4), vend_initialise, 9)|}"
    by eval
  have state_nondeterminism_0:  "state_nondeterminism 0 {|(1, select coke, 0), (7, select pepsi, 1)|} = {|(0, (7, 1), (select pepsi, 1), select coke, 0), (0, (1, 7), (select coke, 0), select pepsi, 1)|}"
    by eval
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def heuristics_2_9_def)
    apply (simp add: outgoing_transitions_def fimage_def minus Abs_fset_inverse)
    apply (simp add: state_nondeterminism_0 state_nondeterminism_1 state_nondeterminism_2)
    apply (simp add: ffUnion_def Abs_fset_inverse)
    apply (simp add: Abs_ffilter Abs_fset_inverse Set.filter_def)
    apply standard
     apply clarify
     apply simp
     apply (case_tac "ab = coin_general")
      apply simp
     apply (case_tac "ab = vend_initialise")
      apply (simp add: choice_def)
    apply (case_tac "ab = coin50_initialise")
      apply (simp add: choice_def)
     apply simp
     apply (meson choice_symmetry no_choice_select_coke_select_pepsi)
    apply clarify
    apply simp
    using choice_coin_specific_coin_general choice_symmetry by blast
qed

definition "merge_states_5_2_a = 
{|(0, (0, 1), select coke),
   (1, (0, 7), select pepsi),
   (3, (1, 2), coin 100 100), (4, (2, 3), coin50_initialise),
   (5, (3, 4), vend coke),
   (6, (2, 6), vend coke),
   (7, (7, 1), coin_general), (8, (1, 2), coin_general), (9, (2, 10), vend_initialise)|}"

lemma merge_states_5_2_a: "merge_states 5 2 (heuristics_2_9 |-| {|(2, (1, 2), coin_general)|}) = merge_states_5_2_a"
  by eval

lemma "merge_transitions pta merge_states_5_2_a 1 8 1 2 2 (coin 100 100) 3 coin_general 8 heuristics = None"
  apply (simp add: merge_transitions_def)
  oops

lemma "merge pta 1 8 heuristics (satisfies (set traces)) = None"
proof-
  have arrives_8_merged_1_8:  "arrives 8 merged_1_8 = 9"
    by eval
  have arrives_2_merged_1_8: "(arrives 2 merged_1_8) = 2"
    by eval
  have leaves_8_merged_2_9:  "leaves 8 merged_2_9 = 1"
    by eval
  have heuristics_merged_2_9: "heuristics 8 2 1 merged_2_9 pta = Some heuristics_2_9"
    by eval
  have arrives_3_heuristics_2_9: "arrives 3 heuristics_2_9 = 5"
    by eval
  have arrives_8_heuristics_2_9: "arrives 8 heuristics_2_9 = 2"
    by eval
  have leaves_3_pta: "leaves 3 pta = 1"
    by eval
  have leaves_8_pta: "leaves 8 pta = 8"
    by eval
  have leaves_3_merge_5_2: "leaves 3 merge_5_2 = 1"
    by eval
  have arrives_3_merge_5_2: "arrives 3 merge_5_2 = 2"
    by eval
  have arrives_8_merge_5_2: "arrives 8 merge_5_2 = 2"
    by eval
  have merge_transitions_coin_100_100_general_none: "merge_transitions pta merge_5_2 1 8 1 2 2 (coin 100 100) 3 coin_general 8 heuristics = None"
    proof-
      show ?thesis
        apply (simp add: merge_transitions_def coin_100_100_not_directly_subsumes_coin_general)
        by eval
    qed
    have arrives_2_heuristics_2_9: "arrives 2 heuristics_2_9 = 2"
      by eval
    have leaves_2_pta: "leaves 2 pta = 1"
      by eval
    have arrives_2_merge_5_2: "arrives 2 merge_5_2 = 2"
      by eval
    have merge_transitions_2: "merge_transitions pta merge_5_2 1 1 1 2 2 (coin 100 100) 3 coin_general 2 heuristics = None"
      apply (simp add: merge_transitions_def)
      apply (simp add: coin_100_100_not_directly_subsumes_coin_general not_directly_subsumes_100_pta)
      by eval
    have leaves_8_merge_5_2: "leaves 8 merge_5_2 = 1"
      by eval
    have merge_transitions_3: "merge_transitions pta merge_5_2 8 1 1 2 2 coin_general 8 (coin 100 100) 3 heuristics = None"
      apply (simp add: merge_transitions_def)
      apply (simp add: coin_100_100_not_directly_subsumes_coin_general not_directly_subsumes_100_pta)
      by eval
    have leaves_2_merge_5_2: "leaves 2 merge_5_2 = 1"
      by eval
    have merge_transitions_4: "merge_transitions pta merge_5_2 1 1 1 2 2 coin_general 2 (coin 100 100) 3 heuristics = None"
      apply (simp add: merge_transitions_def)
      apply (simp add: coin_100_100_not_directly_subsumes_coin_general not_directly_subsumes_100_pta)
      by eval
    have leaves_8_heuristics_2_9: "leaves 8 heuristics_2_9 = 1"
      by eval
    have arrives_8_heuristics_2_9: "arrives 8 heuristics_2_9 = 2"
      by eval
    have arrives_2_heuristics_2_9: "arrives 2 heuristics_2_9 = 2"
      by eval
    have merge_transitions_general_general: "merge_transitions pta heuristics_2_9 8 1 1 2 2 coin_general 8 coin_general 2 heuristics = Some (heuristics_2_9 |-| {|(2, (1, 2), coin_general)|})"
      apply (simp add: merge_transitions_def)
      apply (simp add: directly_subsumes_def transition_subsumes_self)
      apply (simp add: replace_transition_def heuristics_2_9_def)
      by eval
    have arrives_3_minus:  "arrives 3 (heuristics_2_9 |-| {|(2, (1, 2), coin_general)|}) = 5"
      by eval
    have arrives_8_minus: "(arrives 8 (heuristics_2_9 |-| {|(2, (1, 2), coin_general)|})) = 2"
      by eval
    have leaves_3_merge_states_5_2_a: "leaves 3 merge_states_5_2_a = 1"
      by eval
    have arrives_3_merge_states_5_2_a: "arrives 3 merge_states_5_2_a = 2"
      by eval
    have arrives_8_merge_states_5_2_a: "arrives 8 merge_states_5_2_a = 2"
      by eval
  show ?thesis
    apply (simp add: merge_def merge_states_1_8 nondeterministic_pairs_merged_1_8 sorted_list_of_fset_def)
    apply (simp add: arrives_8_merged_1_8 arrives_2_merged_1_8 merge_states_2_9)
    apply (simp add: merge_transitions_def coin_50_100_cant_directly_subsume_coin_50_50 coin_50_50_cant_directly_subsume_coin_50_100)
    apply (simp add: leaves_8_merged_2_9 heuristics_merged_2_9)
    apply (simp add: nondeterministic_pairs_heuristics_2_9 sorted_list_of_fset_def)

    apply (simp add: arrives_3_heuristics_2_9 arrives_8_heuristics_2_9)
    apply (simp add: merge_5_2)
    apply (simp add: leaves_3_pta leaves_8_pta leaves_3_merge_5_2 arrives_3_merge_5_2 arrives_8_merge_5_2)
    apply (simp add: merge_transitions_coin_100_100_general_none)

    apply (simp add: arrives_3_heuristics_2_9 arrives_2_heuristics_2_9)
    apply (simp add: merge_5_2)
    apply (simp add: leaves_3_pta leaves_2_pta leaves_3_merge_5_2 arrives_3_merge_5_2 arrives_2_merge_5_2)
    apply (simp add: merge_transitions_2)

    apply (simp add: arrives_3_heuristics_2_9 arrives_8_heuristics_2_9)
    apply (simp add: merge_5_2)
    apply (simp add: leaves_3_pta leaves_8_pta leaves_8_merge_5_2 arrives_3_merge_5_2 arrives_8_merge_5_2)
    apply (simp add: merge_transitions_3)

    apply (simp add: arrives_3_heuristics_2_9 arrives_2_heuristics_2_9)
    apply (simp add: merge_5_2)
    apply (simp add: leaves_3_pta leaves_2_pta arrives_3_merge_5_2 arrives_2_merge_5_2 leaves_2_merge_5_2)
    apply (simp add: merge_transitions_4)

    apply (simp add: arrives_2_heuristics_2_9 arrives_8_heuristics_2_9)
    apply (simp add: merge_states_reflexive)
    apply (simp add: leaves_8_pta leaves_2_pta leaves_8_heuristics_2_9 arrives_8_heuristics_2_9 arrives_2_heuristics_2_9)
    apply (simp add:merge_transitions_general_general)

    apply (simp add: nondeterministic_pairs_heuristics_2_9_minus sorted_list_of_fset_def)
    apply (simp add: arrives_3_minus arrives_8_minus merge_states_5_2_a)
    apply (simp add: leaves_3_pta leaves_8_pta leaves_3_merge_states_5_2_a arrives_3_merge_states_5_2_a
                     arrives_8_merge_states_5_2_a)


lemma "learn traces naive_score heuristics = (tm final)"
  apply (simp add: learn_def build_pta scoring_1)


end