theory InferenceTest
imports Inference Convert_JSON SelectionStrategies Trace_Matches Code_Generation
begin

declare One_nat_def [simp del]

import_JSON traces_json "../../inference-tool/sample-traces/vend4.json"

lemma implode_select: "String.implode ''select'' = STR ''select''"
  by eval

lemma implode_coin: "String.implode ''coin'' = STR ''coin''"
  by eval

lemma implode_vend: "String.implode ''vend'' = STR ''vend''"
  by eval

abbreviation "coke \<equiv> STR ''coke''"
abbreviation "pepsi \<equiv> STR ''pepsi''"
abbreviation "beer \<equiv> STR ''beer''"

definition "traces = [
                      [(STR ''select'', [Str ''coke''], []), (STR ''coin'', [Num 50], [Num 50]), (STR ''coin'', [Num 50], [Num 100]), (STR ''vend'', [], [Str ''coke''])],
                      [(STR ''select'', [Str ''pepsi''], []), (STR ''coin'', [Num 100], [Num 100]), (STR ''vend'', [], [Str ''pepsi''])],
                      [(STR ''select'', [Str ''beer''], []), (STR ''coin'', [Num 50], [Num 50]), (STR ''coin'', [Num 50], [Num 100]), (STR ''vend'', [], [Str ''beer''])]
                     ]"

lemma "convert traces_json = traces"
  apply (simp add: convert_def traces_json_def convert_aux_def convert_event_def convert_args_def)
  apply (simp add: implode_select implode_coin implode_vend)
  by (simp add: traces_def)

abbreviation "coin i out \<equiv> \<lparr>Label = STR ''coin'', Arity = 1, Guard = [gexp.Eq (V (I (1))) (L (Num i))], Outputs = [L (Num out)], Updates = []\<rparr>"
abbreviation "select i \<equiv> \<lparr>Label = STR ''select'', Arity = 1, Guard = [gexp.Eq (V (I 1)) (L (Value.Str i))], Outputs = [], Updates = []\<rparr>"
abbreviation "vend out \<equiv> \<lparr>Label = STR ''vend'', Arity = 0, Guard = [], Outputs = [L (Value.Str out)], Updates = []\<rparr>"

definition "pta = {|(0, (0, 1), select coke),
   (1, (0, 5), select pepsi),
   (2, (0, 8), select beer),
   (3, (1, 2), coin 50 50),
   (4, (2, 3), coin 50 100),
   (5, (3, 4), vend coke),
   (6, (5, 6), coin 100 100),
   (7, (6, 7), vend pepsi),
   (8, (8, 9), coin 50 50),
   (9, (9, 10), coin 50 100),
   (10, (10, 11), vend beer)|}"

lemma make_PTA: "toiEFSM (make_pta traces {||}) = pta"
  by eval

lemma score_1:  "rev (sorted_list_of_fset (score pta naive_score)) = [(1, 8, 9), (1, 6, 10), (1, 5, 9), (1, 5, 8), (1, 3, 10), (1, 3, 6), (1, 2, 9), (1, 2, 8), (1, 2, 5), (1, 1, 9), (1, 1, 8), (1, 1, 5),
  (1, 1, 2)]"
  by eval

definition "merge_states_8_9 = {|(0, (0, 1), select coke),
   (1, (0, 5), select pepsi),
   (2, (0, 8), select beer),
   (3, (1, 2), coin 50 50),
   (4, (2, 3), coin 50 100),
   (5, (3, 4), vend coke),
   (6, (5, 6), coin 100 100),
   (7, (6, 7), vend pepsi),
   (8, (8, 8), coin 50 50),
   (9, (8, 10), coin 50 100),
   (10, (10, 11), vend beer)|}"

lemma merge_states_8_9:  "merge_states 8 9 pta = merge_states_8_9"
  by eval

lemma implode_beer: "String.implode ''beer'' = STR ''beer''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_coke: "String.implode ''coke'' = STR ''coke''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_pepsi: "String.implode ''pepsi'' = STR ''pepsi''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma no_choice_coke_pepsi: "\<not>choice (select beer) (select pepsi)"
  by (simp add: choice_def)

lemma nondeterministic_pairs_merge_states_8_9: "nondeterministic_pairs merge_states_8_9 = {|
       (8, (10, 8), (coin 50 100, 9), coin 50 50, 8),
       (8, (8, 10), (coin 50 50, 8), coin 50 100, 9)
|}"
proof-
  have state_nondeterminism_8: "state_nondeterminism 8 {|(8, coin 50 50, 8), (10, coin 50 100, 9)|} = {|
      (8, (10, 8), (coin 50 100, 9), coin 50 50, 8),
      (8, (8, 10), (coin 50 50, 8), coin 50 100, 9)|}"
    by eval
  have state_nondeterminism_0: "state_nondeterminism 0 {|(1,select coke, 0), (5, select pepsi, 1), (8, select beer, 2)|} = {|
     (0, (8, 5), (select beer, 2), select pepsi, 1),
     (0, (8, 1), (select beer, 2), select coke, 0),
     (0, (5, 8), (select pepsi, 1), select beer, 2),
     (0, (5, 1), (select pepsi, 1), select coke, 0),
     (0, (1, 8), (select coke, 0), select beer, 2),
     (0, (1, 5), (select coke, 0), select pepsi, 1)
  |}"
  by eval
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merge_states_8_9_def)
    apply (simp add: outgoing_transitions_def fimage_def)
    apply (simp add: state_nondeterminism_8 state_nondeterminism_0)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply standard
     apply clarify
     apply simp
     apply (case_tac "a = 8")
      apply auto[1]
     apply simp
     apply (case_tac "a = 0")
      apply simp
      apply (case_tac "aa = 8")
       apply simp
       apply safe[1]
        apply (simp add: choice_def implode_beer implode_pepsi)
        apply auto[1]
       apply (simp add: choice_def implode_beer implode_coke)
       apply auto[1]
      apply simp
    using implode_beer implode_coke implode_pepsi choice_def
      apply auto[1]
     apply simp
    apply simp
    using implode_beer implode_coke implode_pepsi choice_def
    by auto
qed

definition "merge_a9_a8 = {|(0, (0, 1), select coke), (1, (0, 5), select pepsi), (2, (0, 8), select beer), (3, (1, 2), coin 50 50), (4, (2, 3), coin 50 100),
   (5, (3, 4), vend coke), (6, (5, 6), coin 100 100), (7, (6, 7), vend pepsi), (8, (8, 8), coin 50 50), (9, (8, 8), coin 50 100),
   (10, (8, 11), vend beer)|}"

lemma merge_a9_a8:  "merge_states (arrives 9 merge_states_8_9) (arrives 8 merge_states_8_9) merge_states_8_9 = merge_a9_a8"
  by eval

lemma no_coin_subsumption: "m \<noteq> n \<Longrightarrow> \<not>directly_subsumes e e' s (coin 50 m) (coin 50 n)"
proof-
  assume premise: "m \<noteq> n"
  have violation: "\<forall>c. \<not>subsumes c (coin 50 m) (coin 50 n)"
    apply (simp add: subsumes_def)
    using premise
    by simp
  show ?thesis
    by (simp add: directly_subsumes_def violation)
qed

lemma merge_fail_1: "merge_transitions pta merge_a9_a8 (leaves 9 pta) (leaves 8 pta) (leaves 9 merge_a9_a8) (arrives 9 merge_a9_a8)
           (arrives 8 merge_a9_a8) (coin 50 100) 9 (coin 50 50) 8 null_generator (heuristic_1 traces) = None"
proof-
  have modify_9_8:  "modify (find_intratrace_matches traces pta) 9 8 pta = None"
    by eval
  show ?thesis
  apply (simp add: merge_transitions_def)
  apply (simp add: easy_merge_def)
  apply (simp add: no_coin_subsumption null_generator_def)
    by (simp add: heuristic_1_def modify_9_8)
qed

definition "merge_a8_a9 = {|(0, (0, 1), select coke), (1, (0, 5), select pepsi), (2, (0, 8), select beer), (3, (1, 2), coin 50 50), (4, (2, 3), coin 50 100),
   (5, (3, 4), vend coke), (6, (5, 6), coin 100 100), (7, (6, 7), vend pepsi), (8, (8, 8), coin 50 50), (9, (8, 8), coin 50 100),
   (10, (8, 11), vend beer)|}"

lemma merge_a8_a9: "merge_states (arrives 8 merge_states_8_9) (arrives 9 merge_states_8_9) merge_states_8_9 = merge_a8_a9"
  by eval

lemma merge_fail_2: "merge_transitions pta merge_a8_a9 (leaves 8 pta) (leaves 9 pta) (leaves 8 merge_a8_a9) (arrives 8 merge_a8_a9)
           (arrives 9 merge_a8_a9) (coin 50 50) 8 (coin 50 100) 9 null_generator (heuristic_1 traces) = None"
proof-
  have heuristic_1: "heuristic_1 traces 8 9 (leaves 8 merge_a8_a9) merge_a8_a9 pta = None"
    by eval
  show ?thesis
    by (simp add: merge_transitions_def easy_merge_def no_coin_subsumption null_generator_def heuristic_1)
qed

lemma merge_8_9: "merge pta 8 9 null_generator (heuristic_1 traces) = None"
  apply (simp add: merge_def merge_states_8_9)
  apply (simp add: nondeterminism_def nondeterministic_pairs_merge_states_8_9)
  apply (simp add: sorted_list_of_fset_def)
  apply (simp add: merge_a9_a8 merge_fail_1)
  apply (simp add: merge_a8_a9 merge_fail_2)
  by (simp add: nondeterminism_def nondeterministic_pairs_merge_states_8_9)

definition "merged_6_10 = {|(0, (0, 1), select coke), (1, (0, 5), select pepsi), (2, (0, 8), select beer), (3, (1, 2), coin 50 50), (4, (2, 3), coin 50 100),
   (5, (3, 4), vend coke), (6, (5, 6), coin 100 100), (7, (6, 7), vend pepsi), (8, (8, 9), coin 50 50), (9, (9, 6), coin 50 100),
   (10, (6, 11), vend beer)|}"

lemma merged_6_10: "merge_states 6 10 pta = merged_6_10"
  by eval

lemma nondeterministic_pairs_merged_6_10: "nondeterministic_pairs merged_6_10 =  {|
       (6, (11, 7), (vend beer, 10), vend pepsi, 7),
       (6, (7, 11), (vend pepsi, 7), vend beer, 10)|}"
proof-
  have state_nondet_6:  "state_nondeterminism 6 {|(7, vend pepsi, 7), (11, vend beer, 10)|} = {|(6, (11, 7), (vend beer, 10), vend pepsi, 7), (6, (7, 11), (vend pepsi, 7), vend beer, 10)|}"
    by eval
  have state_nondet_0: "state_nondeterminism 0 {|(1, select coke, 0), (5, select pepsi, 1), (8, select beer, 2)|} = {|(0, (8, 5), (select beer, 2), select pepsi, 1), (0, (8, 1), (select beer, 2), select coke, 0),
   (0, (5, 8), (select pepsi, 1), select beer, 2), (0, (5, 1), (select pepsi, 1), select coke, 0),
   (0, (1, 8), (select coke, 0), select beer, 2), (0, (1, 5), (select coke, 0), select pepsi, 1)|}"
    by eval
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_6_10_def)
    apply (simp add: outgoing_transitions_def fimage_def)
    apply (simp add: state_nondet_6 state_nondet_0)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def choice_def)
    apply standard
     apply clarify
     apply simp
     apply (case_tac "a=0")
      apply simp
      apply auto[1]
     apply simp
     apply auto[1]
    by auto
qed

definition "merged_a10_a7 = {|(0, (0, 1), select coke), (1, (0, 5), select pepsi), (2, (0, 8), select beer), (3, (1, 2), coin 50 50), (4, (2, 3), coin 50 100),
   (5, (3, 4), vend coke), (6, (5, 6), coin 100 100), (7, (6, 7), vend pepsi), (8, (8, 9), coin 50 50), (9, (9, 6), coin 50 100),
   (10, (6, 7), vend beer)|}"

lemma  merged_a10_a7: "merge_states (arrives 10 merged_6_10) (arrives 7 merged_6_10) merged_6_10 = merged_a10_a7"
  by eval

lemma no_vend_subsumption: "m \<noteq> n \<Longrightarrow> \<not> directly_subsumes e e' s (vend m) (vend n)"
proof-
  assume premise: "m \<noteq> n"
  have violation: "\<forall>c. \<not>subsumes c (vend m) (vend n)"
    apply (simp add: subsumes_def)
    using premise by simp
  show ?thesis
    by (simp add: directly_subsumes_def violation)
qed

abbreviation "selectGeneral \<equiv> \<lparr>Label = STR ''select'', Arity = 1, Guard = [], Outputs = [], Updates = [(R 1, V (I 1))]\<rparr>"
abbreviation "vendGeneral \<equiv> \<lparr>Label = STR ''vend'', Arity = 0, Guard = [], Outputs = [V (R 1)], Updates = []\<rparr>"

definition "generalise_vends = {|(0, (0, 1), select coke), (1, (0, 5), selectGeneral),
     (2, (0, 8), selectGeneral), (3, (1, 2), coin 50 50),
     (4, (2, 3), coin 50 100), (5, (3, 4), vend coke), (6, (5, 6), coin 100 100),
     (7, (6, 7), vendGeneral), (8, (8, 9), coin 50 50),
     (9, (9, 10), coin 50 100), (10, (10, 11), vendGeneral)|}"

lemma generalise_vends: "heuristic_1 traces 10 7 (leaves 10 merged_a10_a7) merged_a10_a7 pta = Some generalise_vends"
  by eval

lemma simulation: "nondeterministic_simulates (tm generalise_vends) (tm pta)"
  sorry

lemma generalise_merge_vends: "merge_transitions pta merged_a10_a7 (leaves 10 pta) (leaves 7 pta) (leaves 10 merged_a10_a7) (arrives 10 merged_a10_a7)
           (arrives 7 merged_a10_a7) (vend beer) 10 (vend pepsi) 7 null_generator (heuristic_1 traces) = Some generalise_vends"
  apply (simp add: merge_transitions_def easy_merge_def no_vend_subsumption null_generator_def)
  by (simp add: generalise_vends simulation)

lemma nondeterministic_pairs_generalise_vends: "nondeterministic_pairs generalise_vends = {|
          (0, (8, 5), (selectGeneral, 2), selectGeneral, 1),
          (0, (8, 1), (selectGeneral, 2), select coke, 0),
          (0, (5, 8), (selectGeneral, 1), selectGeneral, 2),
          (0, (5, 1), (selectGeneral, 1), select coke, 0),
          (0, (1, 8), (select coke, 0), selectGeneral, 2),
          (0, (1, 5), (select coke, 0), selectGeneral, 1)
        |}"
proof-
  have state_nondet_0:  "state_nondeterminism 0 {|(1, select coke, 0), (5, selectGeneral, 1), (8, selectGeneral, 2)|} = {|
       (0, (8, 5), (selectGeneral, 2), selectGeneral, 1), (0, (8, 1), (selectGeneral, 2), select coke, 0),
       (0, (5, 8), (selectGeneral, 1), selectGeneral, 2), (0, (5, 1), (selectGeneral, 1), select coke, 0),
       (0, (1, 8), (select coke, 0), selectGeneral, 2), (0, (1, 5), (select coke, 0), selectGeneral, 1)
    |}"
    by eval
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def generalise_vends_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondet_0)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def choice_def)
    apply safe
    by auto
qed

definition "merged_a2_a1 = {|(0, (0, 1), select coke), (1, (0, 5), selectGeneral), (2, (0, 5), selectGeneral), (3, (1, 2), coin 50 50), (4, (2, 3), coin 50 100),
   (5, (3, 4), vend coke), (6, (5, 6), coin 100 100), (7, (6, 7), vendGeneral), (8, (5, 9), coin 50 50), (9, (9, 10), coin 50 100),
   (10, (10, 11), vendGeneral)|}"

lemma merged_a2_a1: "merge_states (arrives 2 generalise_vends) (arrives 1 generalise_vends) generalise_vends = merged_a2_a1"
  by eval

lemma select_general_directly_subsumes_self: "directly_subsumes e e' s selectGeneral selectGeneral"
proof-
  have select_general_subsumes_self: "\<forall>c. subsumes c selectGeneral selectGeneral"
    by (simp add: subsumes_def)
  show ?thesis
    by (simp add: directly_subsumes_def select_general_subsumes_self)
qed

definition "delete_select_general = {|(10, (10, 11), vendGeneral), (9, (9, 10), coin 50 100), (8, (5, 9), coin 50 50), (7, (6, 7), vendGeneral), (6, (5, 6), coin 100 100),
     (5, (3, 4), vend coke), (4, (2, 3), coin 50 100), (3, (1, 2), coin 50 50), (0, (0, 1), select coke), (2, (0, 5), selectGeneral)|}"

lemma delete_select_general: "Some (replace_transition merged_a2_a1 2 (leaves 2 merged_a2_a1) (arrives 1 merged_a2_a1) selectGeneral selectGeneral) = Some delete_select_general"
  by eval

lemma merge_l2_l1: "merge_transitions pta merged_a2_a1 (leaves 2 pta) (leaves 1 pta) (leaves 2 merged_a2_a1) (arrives 2 merged_a2_a1)
                (arrives 1 merged_a2_a1) selectGeneral 2 selectGeneral 1 null_generator (heuristic_1 traces) = Some delete_select_general"
  by (simp add: merge_transitions_def easy_merge_def select_general_directly_subsumes_self delete_select_general)

lemma nondeterministic_pairs_delete_select_general: "nondeterministic_pairs delete_select_general = {|
(0, (5, 1), (selectGeneral, 2), select coke, 0),
(0, (1, 5), (select coke, 0), selectGeneral, 2)
|}"
proof-
  have state_nondeterminism_5:  "state_nondeterminism 5 {|(9, coin 50 50, 8), (6, coin 100 100, 6)|} = {|(5, (6, 9), (coin 100 100, 6), coin 50 50, 8), (5, (9, 6), (coin 50 50, 8), coin 100 100, 6)|}"
    by eval
  have state_nondeterminism_0: "state_nondeterminism 0 {|(1, select coke, 0), (5, selectGeneral, 2)|} = {|(0, (5, 1), (selectGeneral, 2), select coke, 0), (0, (1, 5), (select coke, 0), selectGeneral, 2)|}"
    by eval
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def delete_select_general_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_5 state_nondeterminism_0)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def choice_def)
    by auto
qed

definition "merged_a2_a0 = {|(10, (10, 11), vendGeneral), (9, (9, 10), coin 50 100), (8, (1, 9), coin 50 50), (7, (6, 7), vendGeneral), (6, (1, 6), coin 100 100),
   (5, (3, 4), vend coke), (4, (2, 3), coin 50 100), (3, (1, 2), coin 50 50), (0, (0, 1), select coke), (2, (0, 1), selectGeneral)|}"

lemma merged_a2_a0:  "merge_states (arrives 2 delete_select_general) (arrives 0 delete_select_general) delete_select_general = merged_a2_a0"
  by eval

lemma general_directly_subsumes_coke: "directly_subsumes (tm pta) (tm merged_a2_a0) (leaves 0 pta) selectGeneral (select coke)"
proof-
  show ?thesis
    apply (simp add: directly_subsumes_def)
    sorry
qed

lemma not_coke_directly_subsumes_general: "\<not> directly_subsumes e e' s (select coke) selectGeneral"
proof-
  show ?thesis
    apply (simp add: directly_subsumes_def)
    sorry
qed


lemma "merge_transitions pta merged_a2_a0 (leaves 2 pta) (leaves 0 pta) (leaves 2 merged_a2_a0) (arrives 2 merged_a2_a0)
                     (arrives 0 merged_a2_a0) selectGeneral 2 (select coke) 0 null_generator (heuristic_1 traces) = a"
  apply (simp add: merge_transitions_def easy_merge_def general_directly_subsumes_coke not_coke_directly_subsumes_general)

lemma merge_6_10: "merge pta 6 10 null_generator (heuristic_1 traces) = a"
  apply (simp add: merge_def merged_6_10)
  apply (simp add: nondeterminism_def nondeterministic_pairs_merged_6_10)
  apply (simp add: sorted_list_of_fset_def merged_a10_a7 generalise_merge_vends)
  apply (simp add: nondeterministic_pairs_generalise_vends merged_a2_a1 merge_l2_l1)
  apply (simp add: nondeterministic_pairs_delete_select_general sorted_list_of_fset_def)
  apply (simp add: merged_a2_a0)



lemma "learn traces naive_score null_generator (heuristic_1 traces) = a"
  apply (simp add: learn_def)
  apply (simp add: make_PTA score_1)
  apply (simp add: merge_8_9)



end