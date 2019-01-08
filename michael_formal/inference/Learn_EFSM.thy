theory Learn_EFSM
  imports Inference SelectionStrategies "../examples/Drinks_Machine" Learn_EFSM_Transitions EFSM_Dot
begin

declare One_nat_def [simp del]

definition merged_1_8 :: iEFSM where
  "merged_1_8 = {|
(0, (0, 1), selectCoke),
(1, (0, 7), selectPepsi),
(2, (1, 2), coin50_50),
(3, (1, 5), coin100_100),
(4, (2, 3), coin50_100),
(5, (3, 4), vend_coke),
(6, (5, 6), vend_coke),
(7, (7, 1), coin50_50),
(8, (1, 9), coin50_100),
(9, (9, 10), vend_pepsi)
|}"

lemma merge_states_1_8: "merge_states 1 8 pta = merged_1_8"
  by (simp add: merge_states_def merge_states_aux_def pta_def merged_1_8_def)

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
         
value "efsm2dot (tm merged_1_8)"

lemma "merge pta 1 8 (\<lambda>a b c d e. Some t) (\<lambda>a b c d e. Some e') = Some b"
  apply (simp add: merge_def merge_states_1_8 nondeterminism_def nondeterministic_pairs_merged_1_8)


lemma "learn traces naive_score (\<lambda>a b c d e. Some t) (\<lambda>a b c d e. Some e') = drinks"
  apply (simp add: learn_def build_pta scoring_1)
  sorry

end