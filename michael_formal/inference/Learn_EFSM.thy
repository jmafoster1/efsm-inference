theory Learn_EFSM
  imports Inference SelectionStrategies "../examples/Drinks_Machine" Learn_EFSM_Transitions EFSM_Dot
begin

declare One_nat_def [simp del]

lemma merge_states_1_8: "merge_states 1 8 pta = merged_1_8"
  apply (simp add: merge_states_def merge_states_aux_def pta_def merged_1_8_def)
  by auto

lemma nondeterministic_pairs_merged_1_8: "nondeterministic_pairs merged_1_8 = {|(1, (2, 9), (coin50_50, 2), coin50_100, 8)|}"
proof-
  have minus_1: "{|(1, selectCoke, 0), (7, selectPepsi, 1)|} |-| {|(7, selectPepsi, 1)|} = {|(1, selectCoke, 0)
|}"
    apply (simp add: transitions)
    by auto
  have minus_2: "{|(2, coin50_50, 2), (5, coin100_100, 3), (9, coin50_100, 8)|} |-| {|(5, coin100_100, 3)|} = {|(2, coin50_50, 2), (9, coin50_100, 8)|}"
    apply (simp add: transitions)
    by auto
  have minus_3: "{|(2, coin50_50, 2), (5, coin100_100, 3), (9, coin50_100, 8)|} |-| {|(9, coin50_100, 8)|} = {|(2, coin50_50, 2), (5, coin100_100, 3)|}"
    apply (simp add: transitions)
    by auto
  have state_nondeterminsm_0: "state_nondeterminism 0 {|(1, selectCoke, 0), (7, selectPepsi, 1)|} = {|(0, (1, 7), (selectCoke, 0), selectPepsi, 1)|}"
    by (simp add: state_nondeterminism_def minus_1)
  have state_nondeterminism_1: "state_nondeterminism 1 {|(2, coin50_50, 2), (5, coin100_100, 3), (9, coin50_100, 8)|} = {|
      (1, (2, 5), (coin50_50, 2), coin100_100, 3),
      (1, (5, 9), (coin100_100, 3), coin50_100, 8),
      (1, (2, 9), (coin50_50, 2), coin50_100, 8)
    |}"
    apply (simp add: state_nondeterminism_def minus_2 minus_3)
    by auto
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_1_8_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminsm_0 state_nondeterminism_1)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply safe
    by (simp_all add: choices orders)
qed

definition generator :: generator_function where
  "generator oldEFSM t1FromOld t1 t2FromOld t2 = (if (oldEFSM, t1FromOld, t1, t2FromOld, t2) = (pta, 1, coin50_50, 8, coin50_100) then None
                                                  else None)"

definition modifier :: update_modifier where
  "modifier t1 t2 newFrom newEFSM oldEFSM = (if (t1, t2, newFrom, newEFSM, oldEFSM) = (coin50_50, coin50_100, 1, merged_1_8, pta) then None
                                             else None)"
         
lemma merge_1_8: "merge pta 1 8 generator modifier = None"
proof-
  have leaves_2_pta: "leaves 2 pta = 1"
  proof-
    have set_filter: "Set.filter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) (fset pta) = {(2, (1, 2), coin50_50)}"
      apply (simp add: Set.filter_def pta_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter_def fthe_elem_def Abs_fset_inverse set_filter)
  qed
  have leaves_1_8_pta: "leaves 8 pta = 8"
  proof-
    have set_filter: "Set.filter (\<lambda>x. \<exists>a b ba. x = (8, (a, b), ba)) (fset pta) = {(8, (8, 9), coin50_100)}"
      apply (simp add: Set.filter_def pta_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter_def fthe_elem_def Abs_fset_inverse set_filter)
  qed
  have no_direct_subsumption_coin_50_50_coin50_100: "\<not> directly_subsumes (tm pta) (tm merged_1_8) 8 coin50_50 coin50_100"
    apply (simp add: directly_subsumes_def)
    apply (rule_tac x="[(''select'', [Str ''pepsi'']), (''coin'', [Num 50])]" in exI)
    apply standard
     apply (simp add: accepts_trace_def)
     apply (rule accepts.step)
      apply (simp add: step_pta_selectPepsi)
     apply (rule accepts.step)
      apply (simp add: step_pta_coin50_7)
     apply (rule accepts.base)
    apply standard
     apply (rule gets_us_to.step_some)
      apply (simp add: step_pta_selectPepsi)
     apply (rule gets_us_to.step_some)
      apply (simp add: step_pta_coin50_7)
     apply (simp add: gets_us_to.base)
    apply (simp add: anterior_context_def)
    apply (simp add: step_merged_1_8_selectPepsi step_merged_1_8_coin50_7)
    by (simp add: posterior_selectPepsi posterior_coin50_50 no_subsumption_coin50_50_coin50_100)
  have no_direct_subsumption_coin50_100_coin_50_50: "\<not> directly_subsumes (tm pta) (tm merged_1_8) 1 coin50_100 coin50_50"
    apply (simp add: directly_subsumes_def)
    apply (rule_tac x="[(''select'', [Str ''coke''])]" in exI)
    apply standard
     apply (simp add: accepts_trace_def)
     apply (rule accepts.step)
      apply (simp add: step_pta_selectCoke)
     apply (rule accepts.base)
    apply standard
     apply (rule gets_us_to.step_some)
      apply (simp add: step_pta_selectCoke)
     apply (simp add: gets_us_to.base)
    apply (simp add: anterior_context_def)
    apply (simp add: step_merged_1_8_selectCoke)
    by (simp add: posterior_selectCoke no_subsumption_coin50_100_coin50_50)
  have merge_transitions: "merge_transitions pta merged_1_8 1 8 1 2 9 coin50_50 2 coin50_100 8 generator modifier True = None"
    apply (simp add: merge_transitions_def easy_merge_def)
    by (simp add: generator_def modifier_def no_direct_subsumption_coin_50_50_coin50_100
                     no_direct_subsumption_coin50_100_coin_50_50)
  show ?thesis
    apply (simp add: merge_def merge_states_1_8 nondeterminism_def nondeterministic_pairs_merged_1_8)
    apply (simp add: leaves_2_pta leaves_1_8_pta merge_transitions)
    by (simp add: nondeterminism_def nondeterministic_pairs_merged_1_8)
qed


lemma "learn traces naive_score generator modifier = drinks"
  apply (simp add: learn_def build_pta scoring_1 merge_1_8)
  sorry

end