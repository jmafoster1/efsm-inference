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

lemma "merge pta 1 8 heuristics (satisfies (set traces)) = None"
proof-
  have arrives_8:  "arrives 8 merged_1_8 = 9"
    by eval
  have arrives_2: "(arrives 2 merged_1_8) = 2"
    by eval
  have leaves_8:  "leaves 8 merged_2_9 = 1"
    by eval
  have heuristics_merged_2_9: "heuristics 8 2 1 merged_2_9 pta = Some heuristics_2_9"
    by eval
  show ?thesis
    apply (simp add: merge_def merge_states_1_8 nondeterministic_pairs_merged_1_8 sorted_list_of_fset_def)
    apply (simp add: arrives_8 arrives_2 merge_states_2_9)
    apply (simp add: merge_transitions_def coin_50_100_cant_directly_subsume_coin_50_50 coin_50_50_cant_directly_subsume_coin_50_100)
    apply (simp add: leaves_8 heuristics_merged_2_9)
    apply (simp add: nondeterministic_pairs_heuristics_2_9 sorted_list_of_fset_def)



lemma "learn traces naive_score heuristics = (tm final)"
  apply (simp add: learn_def build_pta scoring_1)


end