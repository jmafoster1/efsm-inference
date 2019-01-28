theory Inference_Test
  imports Learn_EFSM Nano_JSON 
begin
import_JSON json_traces "../../inference-tool/sample-traces/vend1.json"

declare One_nat_def [simp del]

definition convert_args :: "json list \<Rightarrow> value list" where
  "convert_args l = map (\<lambda>x. case x of STRING s \<Rightarrow> Str s | NUMBER (INTEGER i) \<Rightarrow> Num i) l"

definition convert_event :: "json \<Rightarrow> (label \<times> value list \<times> value list)" where
  "convert_event e = (case e of 
    (OBJECT [(''label'', STRING l), (''inputs'', ARRAY i), (''outputs'', ARRAY p)]) \<Rightarrow> (l, convert_args i, convert_args p)
  )"

definition convert_aux :: "json \<Rightarrow> execution" where
  "convert_aux j = (case j of (ARRAY l) \<Rightarrow> map convert_event l)"

definition convert :: "json \<Rightarrow> log" where
  "convert j = (case j of (ARRAY l) \<Rightarrow> map convert_aux l)"

lemma "convert json_traces = traces"
  apply (simp add: json_traces_def traces_def)
  by (simp add: convert_def convert_aux_def convert_event_def convert_args_def)

lemma merge_1_8: "merge pta 1 8 null_generator null_modifier = None"
  sorry

lemma merge_1_7: "merge pta 1 7 null_generator null_modifier = None"
  sorry

lemma merge_1_2: "merge pta 1 2 null_generator null_modifier = None"
  sorry

lemma merge_7_8: "merge pta 7 8 null_generator null_modifier = None"
  sorry

lemma merge_5_9: "merge pta 5 9 null_generator null_modifier = None"
  sorry

lemma merge_3_9: "merge pta 3 9 null_generator null_modifier = None"
  sorry

definition "merged_3_5 = {|
   (0, (0, 1), selectCoke),
   (2, (1, 2), coin50_50),
   (4, (2, 3), coin50_100),
   (5, (3, 4), vend_coke),
   (3, (1, 3), coin100_100),
   (6, (3, 6), vend_coke),
   (1, (0, 7), selectPepsi),
   (7, (7, 8), coin50_50),
   (8, (8, 9), coin50_100),
   (9, (9, 10), vend_pepsi)|}"

lemma merged_3_5: "merge_states 3 5 pta = merged_3_5"
  by eval

lemma nondeterministic_pairs_merged_3_5: "nondeterministic_pairs merged_3_5 = {|(3, (4, 6), (vend_coke, 5), vend_coke, 6)|}"
proof-
  have state_nondeterminism_1: "state_nondeterminism 1 {|(2, coin50_50, 2), (3, coin100_100, 3)|} = {|
    (1, (2, 3), (coin50_50, 2), coin100_100, 3),
    (1, (2, 3), (coin50_50, 2),
    coin100_100, 3)|}"
    by eval
  have state_nondeterminism_3: "state_nondeterminism 3 {|(4, vend_coke, 5), (6, vend_coke, 6)|} = {|(3, (4, 6), (vend_coke, 5),    vend_coke, 6),
   (3, (4, 6), (vend_coke, 5),    vend_coke, 6)|}"
    by eval
have state_nondeterminism_0: "state_nondeterminism 0 {|(1, selectCoke, 0), (7, selectPepsi, 1)|} = {|
  (0, (1, 7), (selectCoke, 0),
    selectPepsi, 1),
   (0, (1, 7), (selectCoke, 0),
    selectPepsi, 1)|}"
  by eval
  show ?thesis
    apply (simp add: S_def merged_3_5_def nondeterministic_pairs_def)
    apply (simp add: outgoing_transitions_def fimage_def)
    apply (simp add: state_nondeterminism_1 state_nondeterminism_3 state_nondeterminism_0)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply (safe)
                   apply (simp_all add: choices)
    by (simp add: vend_coke_def choice_def)
qed

definition merged_4_6 :: iEFSM where
  "merged_4_6 = {|(0, (0, 1), selectCoke),
   (2, (1, 2), coin50_50),
   (4, (2, 3), coin50_100),
   (5, (3, 4), vend_coke),
   (3, (1, 3), coin100_100),
   (6, (3, 4), vend_coke),
   (1, (0, 7), selectPepsi),
   (7, (7, 8), coin50_50),
   (8, (8, 9), coin50_100),
   (9, (9, 10), vend_pepsi)|}"

definition "fallback = {|(9, (9, 10), vend_pepsi),
   (8, (8, 9), coin50_100),
   (7, (7, 8), coin50_50),
   (1, (0, 7), selectPepsi),
   (3, (1, 3), coin100_100),
   (4, (2, 3), coin50_100),
   (2, (1, 2), coin50_50),
   (0, (0, 1), selectCoke),
   (5, (3, 4), vend_coke)|}"

lemma nondeterministic_pairs_fallback: "nondeterministic_pairs fallback = {||}"
proof-
  have state_nondeterminism_1: "state_nondeterminism 1 {|(3, coin100_100, 3), (2, coin50_50, 2)|} = {|(1, (2, 3), (coin50_50, 2),
    coin100_100, 3),
   (1, (2, 3), (coin50_50, 2),
    coin100_100, 3)|}"
    by eval
  have state_nondeterminism_0: "state_nondeterminism 0 {|(7, selectPepsi, 1), (1, selectCoke, 0)|} = {|(0, (1, 7), (selectCoke, 0),
    selectPepsi, 1),
   (0, (1, 7), (selectCoke, 0),
    selectPepsi, 1)|}"
    by eval
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def fallback_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_1 state_nondeterminism_0)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def choice_def)
    by auto
qed

lemma merge_3_5: "merge pta 3 5 null_generator null_modifier = Some fallback"
proof-
  have arrives_5_merged_3_5:  "arrives 5 merged_3_5 = 4"
    by eval
  have arrives_6_merged_3_5:  "arrives 6 merged_3_5 = 6"
    by eval
  have merge_states_4_6: "merge_states 4 6 merged_3_5 = merged_4_6"
    by eval
  have leaves_5_pta: "leaves 5 pta = 3"
    by eval
  have leaves_6_pta: "leaves 6 pta = 5"
    by eval
  have leaves_5_merged_4_6: "leaves 5 Inference_Test.merged_4_6 = 3 \<and> arrives 5 Inference_Test.merged_4_6 = 4"
    by eval
  have arrives_6_merged_4_6:  "arrives 6 Inference_Test.merged_4_6 = 4"
    by eval
  have directly_subsumes_vend_coke:  "directly_subsumes (tm pta) (tm Inference_Test.merged_4_6) 5 vend_coke vend_coke"
    by (simp add: directly_subsumes_def subsumes_def vend_coke_def)
  have replace_transition: "replace_transition Inference_Test.merged_4_6 5 3 4 vend_coke vend_coke = fallback"
    by eval
  have merge_vend_coke:  "merge_transitions pta Inference_Test.merged_4_6 3 5 3 4 4 vend_coke 5 vend_coke 6 null_generator null_modifier True = Some fallback"
    by (simp add: merge_transitions_def easy_merge_def directly_subsumes_vend_coke replace_transition)
  show ?thesis
    apply (simp add: merge_def merged_3_5)
    apply (simp add: nondeterminism_def nondeterministic_pairs_merged_3_5)
    apply (simp add: arrives_5_merged_3_5 arrives_6_merged_3_5 merge_states_4_6)
    apply (simp add: leaves_5_pta leaves_6_pta leaves_5_merged_4_6 arrives_6_merged_4_6)
    by (simp add: merge_vend_coke nondeterminism_def nondeterministic_pairs_fallback)
qed

lemma scoring_2: "rev (sorted_list_of_fset (score fallback naive_score)) = [(2, 1, 8), (2, 1, 7), (2, 1, 2), (1, 7, 8), (1, 3, 9), (1, 2, 8), (1, 2, 7)]"
  by eval

lemma merge_1_8_fallback: "merge fallback 1 8 null_generator null_modifier = None"
  sorry

lemma merge_1_7_fallback: "merge fallback 1 7 null_generator null_modifier = None"
  sorry

lemma merge_1_2_fallback: "merge fallback 1 2 null_generator null_modifier = None"
  sorry

lemma merge_7_8_fallback: "merge fallback 7 8 null_generator null_modifier = None"
  sorry

lemma merge_3_9_fallback: "merge fallback 3 9 null_generator null_modifier = None"
  sorry

lemma merge_2_8_fallback: "merge fallback 2 8 null_generator null_modifier = None"
  sorry

definition "merge_states_2_7 = {|
   (9, (9, 10), vend_pepsi),
   (8, (8, 9), coin50_100),
   (7, (2, 8), coin50_50),
   (1, (0, 2), selectPepsi),
   (3, (1, 3), coin100_100),
   (4, (2, 3), coin50_100),
   (2, (1, 2), coin50_50),
   (0, (0, 1), selectCoke),
   (5, (3, 4), vend_coke)|}"

lemma merge_2_7_fallback: "merge fallback 2 7 null_generator null_modifier = None"
proof-
  have merge_states_2_7: "merge_states 2 7 fallback = merge_states_2_7"
    by eval
  have nondeterministic_pairs_merged_2_7: "nondeterministic_pairs merge_states_2_7 = {|(2, (3, 8), (coin50_100, 4), coin50_50, 7)|}"
  proof-
    have state_nondeterminism_2: "state_nondeterminism 2 {|(8, coin50_50, 7), (3, coin50_100, 4)|} = {|(2, (3, 8), (coin50_100, 4),
    coin50_50, 7),
   (2, (3, 8), (coin50_100, 4),
    coin50_50, 7)|}"
      by eval
    have state_nondeterminism_1: "state_nondeterminism 1 {|(3, coin100_100, 3), (2, coin50_50, 2)|} = {|(1, (2, 3), (coin50_50, 2),
    coin100_100, 3),
   (1, (2, 3), (coin50_50, 2),
    coin100_100, 3)|}"
      by eval
    have state_nondeterminism_0: "state_nondeterminism 0 {|(2, selectPepsi, 1), (1, selectCoke, 0)|} = {|(0, (1, 2), (selectCoke, 0),
    selectPepsi, 1),
   (0, (1, 2), (selectCoke, 0),
    selectPepsi, 1)|}"
      by eval
    show ?thesis
      apply (simp add: nondeterministic_pairs_def S_def merge_states_2_7_def)
      apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_2 state_nondeterminism_1 state_nondeterminism_0)
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse choice_def Set.filter_def transitions)
      by auto
  qed
  show ?thesis
    apply (simp add: merge_def)
    apply (simp add: merge_states_2_7)
    apply (simp add: nondeterminism_def)
    apply (simp add: nondeterministic_pairs_merged_2_7)
    sorry
qed

lemma "learn traces naive_score null_generator null_modifier = a"
  apply (simp add: learn_def build_pta scoring_1)
  apply (simp add: merge_1_8 merge_1_7 merge_1_2 merge_7_8 merge_5_9 merge_3_9 merge_3_5)
  apply (simp add: scoring_2)
  apply (simp add: merge_1_8_fallback merge_1_7_fallback merge_1_2_fallback merge_7_8_fallback merge_3_9_fallback merge_2_8_fallback)
  apply (simp add: merge_2_7_fallback)


end