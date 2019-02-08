theory Learn_EFSM
  imports Inference SelectionStrategies EFSM_Dot Trace_Matches
begin

declare One_nat_def [simp del]

abbreviation "coke \<equiv> STR ''coke''"
abbreviation "pepsi \<equiv> STR ''pepsi''"
abbreviation "beer \<equiv> STR ''beer''"

abbreviation "coin i out \<equiv> \<lparr>Label = STR ''coin'', Arity = 1, Guard = [gexp.Eq (V (I (1))) (L (Num i))], Outputs = [L (Num out)], Updates = []\<rparr>"
abbreviation "select i \<equiv> \<lparr>Label = STR ''select'', Arity = 1, Guard = [gexp.Eq (V (I 1)) (L (Value.Str i))], Outputs = [], Updates = []\<rparr>"
abbreviation "vend out \<equiv> \<lparr>Label = STR ''vend'', Arity = 0, Guard = [], Outputs = [L (Value.Str out)], Updates = []\<rparr>"


definition pta :: iEFSM where
  "pta = {|(0, (0, 1), select coke),  (2, (1, 2), coin 50 50), (4, (2, 3), coin 50 100),  (5, (3, 4), (vend coke)),
                                                             (3, (1, 5), coin 100 100), (6, (5, 6), (vend coke)),
           (1, (0, 7), select pepsi), (7, (7, 8), coin 50 50), (8, (8, 9), coin 50 100),  (9, (9, 10), (vend pepsi))|}"

lemma implode_pepsi: "String.implode ''pepsi'' = STR ''pepsi''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_coke: "String.implode ''coke'' = STR ''coke''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma Str_pepsi: "EFSM.Str ''pepsi'' = value.Str (STR ''pepsi'')"
  by (simp add: implode_pepsi)

lemma Str_coke: "EFSM.Str ''coke'' = value.Str (STR ''coke'')"
  by (simp add: implode_coke)

lemma explode_coke: "String.explode (STR ''coke'') = ''coke''"
  by (simp add: Literal.rep_eq zero_literal.rep_eq)

lemma explode_pepsi: "String.explode (STR ''pepsi'') = ''pepsi''"
  by (simp add: Literal.rep_eq zero_literal.rep_eq)

definition traces :: log where
  "traces = [[((STR ''select''), [(Str ''coke'')], []), ((STR ''coin''), [Num 50], [Num 50]), ((STR ''coin''), [Num 50], [Num 100]), ((STR ''vend''), [], [(Str ''coke'')])],
             [((STR ''select''), [(Str ''coke'')], []), ((STR ''coin''), [Num 100], [Num 100]), ((STR ''vend''), [], [(Str ''coke'')])],
             [((STR ''select''), [(Str ''pepsi'')], []), ((STR ''coin''), [Num 50], [Num 50]), ((STR ''coin''), [Num 50], [Num 100]), ((STR ''vend''), [], [(Str ''pepsi'')])]]"


definition filtered_pairs :: "(nat \<times> nat) set" where
  "filtered_pairs = {(9, 10), (8, 10), (8, 9), (7, 10), (7, 9), (7, 8), (6, 10), (6, 9), (6, 8), (6, 7), (5, 10), (5, 9), (5, 8), (5, 7), (5, 6), (4, 10),
  (4, 9), (4, 8), (4, 7), (4, 6), (4, 5), (3, 10), (3, 9), (3, 8), (3, 7), (3, 6), (3, 5), (3, 4), (2, 10), (2, 9), (2, 8), (2, 7), (2, 6),
  (2, 5), (2, 4), (2, 3), (1, 10), (1, 9), (1, 8), (1, 7), (1, 6), (1, 5), (1, 4), (1, 3), (1, 2), (0, 10), (0, 9), (0, 8), (0, 7), (0, 6),
  (0, 5), (0, 4), (0, 3), (0, 2), (0, 1)}"

lemma scoring_1: "sorted_list_of_fset (score pta naive_score) = [(1, 2, 7), (1, 2, 8), (1, 3, 5), (1, 3, 9), (1, 5, 9), (1, 7, 8), (2, 1, 2), (2, 1, 7), (2, 1, 8)]"
proof-
  have S_pta: "S pta = {|0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10|}"
    apply (simp add: S_def pta_def)
    by auto
  have fset_S: "fset {|0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10|} = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}"
    by (metis bot_fset.rep_eq finsert.rep_eq)
  have ffilter: "ffilter (\<lambda>(x, y). x < y) (Inference.S pta |\<times>| Inference.S pta) = Abs_fset filtered_pairs"
    apply (simp add: filtered_pairs_def ffilter_def fset_both_sides Abs_fset_inverse fprod_def)
    apply (simp only: S_pta fprod_equiv fset_S Set.filter_def)
    apply standard
     apply clarify
     apply (case_tac "a=10")
      apply auto[1]
      apply simp
      apply (case_tac "a=9")
       apply auto[1]
      apply simp
      apply (case_tac "a=8")
       apply auto[1]
      apply simp
      apply (case_tac "a=7")
       apply auto[1]
      apply simp
      apply (case_tac "a=6")
       apply auto[1]
      apply simp
      apply (case_tac "a=5")
       apply auto[1]
      apply simp
      apply (case_tac "a=4")
       apply auto[1]
      apply simp
      apply (case_tac "a=3")
       apply auto[1]
      apply simp
      apply (case_tac "a=2")
        apply auto[1]
      apply simp
      apply (case_tac "a=1")
      apply auto[1]
     apply simp
    apply clarify
    apply safe
    by auto
  have scores: "score pta naive_score = {|(Suc 0, 7, 8), (Suc 0, 5, 9), (Suc 0, 3, 9), (Suc 0, 3, 5), (Suc 0, 2, 8), (Suc 0, 2, 7), (Suc (Suc 0), 1, 8), (Suc (Suc 0), 1, 7),
     (Suc (Suc 0), 1, 2)|}"
    apply (simp add: score_def ffilter filtered_pairs_def)
    apply (simp add: outgoing_transitions_def pta_def fimage_def)
    apply (simp add: naive_score_empty set_equiv)
    apply (simp add: naive_score_def fprod_def)
    by (simp add: Abs_fset_inverse)
  show ?thesis
    by (simp add: scores sorted_list_of_fset_def)
qed

lemmas possible_steps_fst = possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse

lemma step_pta_coin50_7: "step (tm pta) 7 r (STR ''coin'') [Num 50] = Some (coin 50 50, 8, [Some (Num 50)], r)"
proof-
  have possible_steps: "possible_steps (tm pta) 7 r (STR ''coin'') [Num 50] = {|(8, coin 50 50)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: Set.filter_def tm_def pta_def)
    apply safe
                     apply simp_all
    by force
  show ?thesis
    by (simp add: step_def possible_steps)
qed

lemma step_pta_coin50_1: "step (tm pta) 1 r (STR ''coin'') [Num 50] = Some (coin 50 50, 2, [Some (Num 50)], r)"
proof-
  have possible_steps: "possible_steps (tm pta) 1 r (STR ''coin'') [Num 50] = {|(2, coin 50 50)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: Set.filter_def tm_def pta_def)
    apply safe
                     apply simp_all
    by force
  show ?thesis
    by (simp add: step_def possible_steps)
qed

lemma step_pta_vend_5: "step (tm pta) 5 r (STR ''vend'') [] = Some ((vend coke), 6, [Some ((Str ''coke''))], r)"
proof-
  have possible_steps: "possible_steps (tm pta) 5 r (STR ''vend'') [] = {|(6, (vend coke))|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: Set.filter_def tm_def pta_def)
    apply safe
                     apply simp_all
    by force
  show ?thesis
    apply (simp add: step_def possible_steps)
    by (simp add: implode_coke)
qed

lemma step_pta_coin100_1: "step (tm pta) 1 r (STR ''coin'') [Num 100] = Some (coin 100 100, 5, [Some (Num 100)], r)"
proof-
  have possible_steps: "possible_steps (tm pta) 1 r (STR ''coin'') [Num 100] = {|(5, coin 100 100)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: Set.filter_def tm_def pta_def)
    apply safe
                     apply simp_all
    by force
  show ?thesis
    by (simp add: step_def possible_steps)
qed

lemma step_pta_coin50_2: "step (tm pta) 2 r (STR ''coin'') [Num 50] = Some (coin 50 100, 3, [Some (Num 100)], r)"
proof-
  have possible_steps: "possible_steps (tm pta) 2 r (STR ''coin'') [Num 50] = {|(3, coin 50 100)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: Set.filter_def tm_def pta_def)
    apply safe
                     apply (simp_all add:)
    by force
  show ?thesis
    by (simp add: step_def possible_steps)
qed

lemma step_pta_coin50_8: "step (tm pta) 8 r (STR ''coin'') [Num 50] = Some (coin 50 100, 9, [Some (Num 100)], r)"
proof-
  have possible_steps: "possible_steps (tm pta) 8 r (STR ''coin'') [Num 50] = {|(9, coin 50 100)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: Set.filter_def tm_def pta_def)
    apply safe
                     apply simp_all
    by force
  show ?thesis
    by (simp add: step_def possible_steps)
qed

lemma step_pta_vend_3: "step (tm pta) 3 r (STR ''vend'') [] = Some ((vend coke), 4, [Some ((Str ''coke''))], r)"
proof-
  have possible_steps: "possible_steps (tm pta) 3 r (STR ''vend'') [] = {|(4, (vend coke))|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: Set.filter_def tm_def pta_def)
    apply safe
                     apply simp_all
    by force
  show ?thesis
    by (simp add: step_def possible_steps implode_coke)
qed

lemma step_pta_vend_9: "step (tm pta) 9 r (STR ''vend'') [] = Some ((vend pepsi), 10, [Some ((Str ''pepsi''))], r)"
proof-
  have possible_steps: "possible_steps (tm pta) 9 r (STR ''vend'') [] = {|(10, (vend pepsi))|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: Set.filter_def tm_def pta_def)
    apply safe
                     apply simp_all
    by force
  show ?thesis
    by (simp add: step_def possible_steps implode_pepsi)
qed

definition merged_1_8 :: iEFSM where
  "merged_1_8 = {|
(0, (0, 1), select coke),
(1, (0, 7), select pepsi),
(2, (1, 2), coin 50 50),
(3, (1, 5), coin 100 100),
(4, (2, 3), coin 50 100),
(5, (3, 4), (vend coke)),
(6, (5, 6), (vend coke)),
(7, (7, 1), coin 50 50),
(8, (1, 9), coin 50 100),
(9, (9, 10), (vend pepsi))
|}"

definition merged_2_9 :: iEFSM where
  "merged_2_9 = {|(0, (0, 1), select coke), (1, (0, 7), select pepsi), (2, (1, 2), coin 50 50), (3, (1, 5), coin 100 100), (4, (2, 3), coin 50 100),
      (5, (3, 4), (vend coke)), (6, (5, 6), (vend coke)), (7, (7, 1), coin 50 50), (8, (1, 2), coin 50 100), (9, (2, 10), (vend pepsi))|}"

lemma merge_states_2_9: "merge_states 2 9 merged_1_8 = merged_2_9 \<and> merge_states 9 2 merged_1_8 = merged_2_9"
  by (simp add: merge_states_def merge_states_aux_def merged_1_8_def merged_2_9_def)

lemma no_subsumption_coin_50_100_coin_50_50: "\<not> subsumes c (coin 50 100) (coin 50 50)"
  by (simp add: subsumes_def)

lemma no_subsumption_coin_50_50_coin_50_100: "\<not> subsumes c (coin 50 50) (coin 50 100)"
  by (simp add: subsumes_def)

lemma no_subsumption_vend_coke_vend_pepsi: "\<not> subsumes c (vend coke) (vend pepsi)"
  by (simp add: subsumes_def Str_coke implode_pepsi)

lemma vend_pepsi_not_subsumes_vend_coke: "\<not> subsumes c (vend pepsi) (vend coke)"
  by (simp add: subsumes_def Str_coke implode_pepsi)

lemma step_pta_select_coke: "step (tm pta) 0 Map.empty (STR ''select'') [(Str ''coke'')] = Some (select coke, 1, [], <>)"
proof-
  have possible_steps: "possible_steps (tm pta) 0 Map.empty (STR ''select'') [(Str ''coke'')] = {|(1, select coke)|}"
    apply (simp add: possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse)
    apply (simp add: tm_def pta_def Set.filter_def)
    apply safe
                      apply (simp_all add:  implode_coke implode_pepsi)
    using Str_coke by force
  show ?thesis
    by (simp add: step_def possible_steps)
qed

definition merged_1_7 :: iEFSM where
  "merged_1_7 = {|(0, (0, 1), select coke), (2, (1, 2), coin 50 50), (4, (2, 3), coin 50 100),  (5, (3, 4), (vend coke)), 
                                                                   (3, (1, 5), coin 100 100), (6, (5, 6), (vend coke)),
                 (1, (0, 1), select pepsi), (7, (1, 8), coin 50 50), (8, (8, 9), coin 50 100),  (9, (9, 10), (vend pepsi))|}"

lemma merge_states_1_7: "merge_states 1 7 pta = merged_1_7"
  by (simp add: merge_states_def pta_def merge_states_aux_def merged_1_7_def)

definition merged_2_8 :: iEFSM where
  "merged_2_8 = {|(0, (0, 1), select coke),  (2, (1, 2), coin 50 50),  (4, (2, 3), coin 50 100),  (5, (3, 4), (vend coke)),
                                                                      (3, (1, 5), coin 100 100), (6, (5, 6), (vend coke)),
                   (1, (0, 1), select pepsi), (7, (1, 2), coin 50 50),  (8, (2, 9), coin 50 100),  (9, (9, 10), (vend pepsi))|}"

lemma merge_states_2_8: "merge_states 2 8 merged_1_7 = merged_2_8 \<and> merge_states 8 2 merged_1_7 = merged_2_8"
  by (simp add: merge_states_def merge_states_aux_def merged_1_7_def merged_2_8_def)

lemma no_choice_coin_50_50_coin_100_100: "\<not>choice (coin 50 50) (coin 100 100)"
  by (simp add: choice_def)

definition merge_2_8_no_nondet :: iEFSM where
  "merge_2_8_no_nondet = {|(0, (0, 1), select coke), (2, (1, 2), coin 50 50), (4, (2, 3), coin 50 100), (5, (3, 4), (vend coke)), (3, (1, 5), coin 100 100),
      (6, (5, 6), (vend coke)), (1, (0, 1), select pepsi), (7, (1, 2), coin 50 50), (8, (2, 9), coin 50 100), (9, (9, 10), (vend pepsi))|}"

definition selectGeneral :: transition where
  "selectGeneral = \<lparr>Label = (STR ''select''), Arity = 1, Guard = [], Outputs = [], Updates = [(R 1, V (I 1))]\<rparr>"

definition vend_general :: transition where
  "vend_general = \<lparr>Label = (STR ''vend''), Arity = 0, Guard = [], Outputs = [V (R 1)], Updates = []\<rparr>"

definition merged_4_10 :: iEFSM where
  "merged_4_10 = {|(0, (0, 1), select coke), (7, (1, 2), coin 50 50), (8, (2, 3), coin 50 100), (5, (3, 4), (vend coke)) ,
                   (1, (0, 1), select pepsi),                                     (9, (3, 4), (vend pepsi)), 
                                            (3, (1, 5), coin 100 100), (6, (5, 6), (vend coke))|}"

definition merged_vends :: iEFSM where
  "merged_vends = {|(0, (0, 1), selectGeneral), (2, (1, 2), coin 50 50), (4, (2, 3), coin 50 100), (5, (3, 4), vend_general) ,
                                            (3, (1, 5), coin 100 100), (6, (5, 6), vend_general)|}"

definition coinGeneral :: transition where
  "coinGeneral = \<lparr>Label = (STR ''coin''), Arity = 1, Guard = [], Outputs = [Plus (V (I 1)) (V (R 2))], Updates = [(R 2, Plus (V (I 1)) (V (R 2)))]\<rparr>"

lemma merge_states_1_8: "merge_states 1 8 pta = merged_1_8"
  apply (simp add: merge_states_def merge_states_aux_def pta_def merged_1_8_def)
  by auto

lemma nondeterministic_pairs_merged_1_8: "nondeterministic_pairs merged_1_8 = {|
    (1, (9, 2), (coin 50 100, 8), coin 50 50, 2),
    (1, (2, 9), (coin 50 50, 2), coin 50 100, 8)
  |}"
proof-
  have minus_1: "{|(1, select coke, 0), (7, select pepsi, 1)|} |-| {|(7, select pepsi, 1)|} = {|(1, select coke, 0)|}"
    by auto
  have minus_2: "{|(2, coin 50 50, 2), (5, coin 100 100, 3), (9, coin 50 100, 8)|} |-| {|(5, coin 100 100, 3)|} = {|(2, coin 50 50, 2), (9, coin 50 100, 8)|}"
    by auto
  have minus_3: "{|(2, coin 50 50, 2), (5, coin 100 100, 3), (9, coin 50 100, 8)|} |-| {|(9, coin 50 100, 8)|} = {|(2, coin 50 50, 2), (5, coin 100 100, 3)|}"
    by auto
  have state_nondeterminsm_0: "state_nondeterminism 0 {|(1, select coke, 0), (7, select pepsi, 1)|} = {|(0, (7, 1), (select pepsi, 1), select coke, 0), (0, (1, 7), (select coke, 0), select pepsi, 1) |}"
    by (simp add: state_nondeterminism_def minus_1)
  have state_nondeterminism_1: "state_nondeterminism 1 {|(2, coin 50 50, 2), (5, coin 100 100, 3), (9, coin 50 100, 8)|} = {|
   (1, (9, 5), (coin 50 100, 8), coin 100 100, 3),
   (1, (9, 2), (coin 50 100, 8), coin 50 50, 2),
   (1, (5, 9), (coin 100 100, 3), coin 50 100, 8),
   (1, (5, 2), (coin 100 100, 3), coin 50 50, 2),
   (1, (2, 9), (coin 50 50, 2), coin 50 100, 8),
   (1, (2, 5), (coin 50 50, 2), coin 100 100, 3)
   |}"
    apply (simp add: state_nondeterminism_def minus_2 minus_3)
    by auto
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_1_8_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminsm_0 state_nondeterminism_1)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    by auto
qed

lemma nondeterministic_pairs_merged_1_7: "nondeterministic_pairs merged_1_7 = {|
(1, (2, 8), (coin 50 50, 2), coin 50 50, 7),
(1, (8, 2), (coin 50 50, 7), coin 50 50, 2)
|}"
proof-
  have minus_1: "{(2, coin 50 50, 2), (5, coin 100 100, 3), (8, coin 50 50, 7)} - {(5, coin 100 100, 3)} = {(2, coin 50 50, 2), (8, coin 50 50, 7)}"
    by auto
  have minus_2: "{(2, coin 50 50, 2::nat), (5, coin 100 100, 3), (8, coin 50 50, 7)} - {(8, coin 50 50, 7)} = {(2, coin 50 50, 2), (5, coin 100 100, 3)}"
    by auto
  have state_nondeterminism_1: "state_nondeterminism 1 {|(2, coin 50 50, 2), (5, coin 100 100, 3), (8, coin 50 50, 7)|} = {|
      (1, (8, 5), (coin 50 50, 7), coin 100 100, 3),
      (1, (8, 2), (coin 50 50, 7), coin 50 50, 2),
      (1, (5, 8), (coin 100 100, 3), coin 50 50, 7),
      (1, (5, 2), (coin 100 100, 3), coin 50 50, 2),
      (1, (2, 8), (coin 50 50, 2), coin 50 50, 7),
      (1, (2, 5), (coin 50 50, 2), coin 100 100, 3)
    |}"
    apply (simp add: state_nondeterminism_def fimage_def minus_1 minus_2)
    by auto
  have minus_3: "{(1, select coke, 0), (1, select pepsi, 1)} - {(1, select pepsi, 1)} = {(1, select coke, 0)}"
    by auto
  have state_nondeterminism_0: "state_nondeterminism 0 {|(1, select coke, 0), (1, select pepsi, 1)|} = {|(0, (1, 1), (select pepsi, 1), select coke, 0), (0, (1, 1), (select coke, 0), select pepsi, 1)|}"
    by (simp add: state_nondeterminism_def fimage_def minus_3)
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_1_7_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_1 state_nondeterminism_0)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse)
    apply (simp add: Set.filter_def)
    by auto
qed

definition generator :: generator_function where
  "generator oldEFSM t1FromOld t1 t2FromOld t2 = (if (oldEFSM, t1FromOld, t1, t2FromOld, t2) = (pta, 1, coin 50 50, 8, coin 50 100) then None
                                                  else None)"

definition merged_1_3 :: iEFSM where
  "merged_1_3 = {|(0, (0, 1), selectGeneral), (2, (1, 1), coin 50 50), (4, (1, 1), coin 50 100), (5, (1, 4), vend_general),
                                              (3, (1, 5), coin 100 100), (6, (5, 6), vend_general)|}"

definition selectGeneral_2 :: transition where
  "selectGeneral_2 = \<lparr>Label = (STR ''select''), Arity = 1, Guard = [], Outputs = [], Updates = [(R 1, V (I 1)), (R 2, (L (Num 0)))]\<rparr>"

definition merged_1_3_coin :: iEFSM where
  "merged_1_3_coin = {|(0, (0, 1), selectGeneral_2), (2, (1, 1), coinGeneral), (5, (1, 4), vend_general),
                                              (3, (1, 5), coin 100 100), (6, (5, 6), vend_general)|}"

definition merged_1_5 :: iEFSM where
  "merged_1_5 = {|(0, (0, 1), selectGeneral_2), (2, (1, 1), coinGeneral), (5, (1, 4), vend_general), (3, (1, 1), coin 100 100),
      (6, (1, 6), vend_general)|}"

definition merged_1_5_coin :: iEFSM where
  "merged_1_5_coin = {|(0, (0, 1), selectGeneral_2), (2, (1, 1), coinGeneral), (5, (1, 4), vend_general),
      (6, (1, 6), vend_general)|}"

definition modifier :: update_modifier where
  "modifier t1 t2 newFrom newEFSM oldEFSM = (if (newFrom, newEFSM, oldEFSM) = (1, merged_1_8, pta) then None
                                        else if (t1, t2, newFrom, newEFSM, oldEFSM) = (9, 5, 3, merged_4_10, pta) then Some merged_vends
                                        else if (t1, t2, newFrom, newEFSM, oldEFSM) = (4, 2, 1, merged_1_3, merged_vends) then Some merged_1_3_coin
                                        else if (t1, t2, newFrom, newEFSM, oldEFSM) = (3, 2, 1, merged_1_5, merged_vends) then Some merged_1_5_coin
                                        else None)"

lemma set_nequiv_def: "(s \<noteq> s') = (\<exists>e. (e \<in> s \<and> e \<notin> s') \<or> (e \<in> s' \<and> e \<notin> s))"
  apply safe
   apply simp
  by simp

lemma coin_50_50_cant_directly_subsume_coin_50_100: "\<not> directly_subsumes e t s (coin 50 50) (coin 50 100)"
  by (simp add: directly_subsumes_def subsumes_def)

lemma coin_50_100_cant_directly_subsume_coin_50_50: "\<not> directly_subsumes e t s (coin 50 100) (coin 50 50)"
  by (simp add: directly_subsumes_def subsumes_def)

definition merged_3_9 :: iEFSM where
  "merged_3_9 = {|(0, (0, 1), select coke),  (7, (1, 2), coin 50 50),   (8, (2, 3), coin 50 100), (5, (3, 4), (vend coke)),
                         (1, (0, 1), select pepsi), (3, (1, 5), coin 100 100), (6, (5, 6), (vend coke)),
                                                   (4, (2, 3), coin 50 100),  (9, (3, 10), (vend pepsi))|}"

definition merged_3_9_coin100 :: iEFSM where
  "merged_3_9_coin100 = {|(0, (0, 1), select coke),  (7, (1, 2), coin 50 50),  (5, (3, 4), (vend coke)),
                         (1, (0, 1), select pepsi), (3, (1, 5), coin 100 100), (6, (5, 6), (vend coke)),
                                                   (8, (2, 3), coin 50 100),  (9, (3, 10), (vend pepsi))|}"

lemma ctx_simp: "(\<lambda>r. and (if r = V (I 1) then snd (V (I 1), cexp.Eq (Num 50)) else cexp.Bc True) (c r)) = 
       (\<lambda>r. if r = V (I 1) then and (Eq (Num 50)) (c r) else (c r))"
  apply (rule ext)
  by simp

lemma ctx_simp_2: "(\<lambda>r. and (if r = V (I 1) then snd (V (I 1), cexp.Eq (Num m)) else cexp.Bc True)
           (and (if r = V (I 1) then snd (V (I 1), cexp.Eq (Num m)) else cexp.Bc True) (c r))) = 
(\<lambda>r. if r = V (I 1) then and (Eq (Num m)) (and (Eq (Num m)) (c r)) else c r)"
  apply (rule ext)
  by simp

lemma cval_false_eq_undef: "\<forall>r i. cval (Bc False) i = cval (Undef) i"
  by simp

lemma ctx_simp_3: "(\<lambda>r. and (if r = V (I 1) then snd (V (I 1), cexp.Eq (Num m)) else cexp.Bc True) (c r)) =
       (\<lambda>r. (if r = V (I 1) then and (cexp.Eq (Num m)) (c r) else c r))"
  apply (rule ext)
  by simp

lemma "consistent
     (\<lambda>r. and (if r = V (I 1) then snd (V (I 1), cexp.Eq (Num m)) else cexp.Bc True)
           (and (if r = V (I 1) then snd (V (I 1), cexp.Eq (Num m)) else cexp.Bc True) (c r))) \<Longrightarrow>
    consistent (\<lambda>r. and (if r = V (I 1) then snd (V (I 1), cexp.Eq (Num m)) else cexp.Bc True) (c r))"
  apply (simp add: ctx_simp_2 ctx_simp_3)
  apply (simp add: consistent_def)
  oops

lemma subsumes_coin_50_50_coin_50_50: "subsumes c (coin m n) (coin m n)"
proof-
  show ?thesis
  apply (simp add: subsumes_def)
  apply (simp add: posterior_def Let_def remove_input_constraints_def ctx_simp)
    apply clarify
    apply standard
     apply clarify
     apply (case_tac "cval (c r) i")
      apply simp
     apply simp
    apply clarify
    apply standard
     apply clarify
     apply simp

lemma subsumes_coin 50 100_coin 50 100: "subsumes c coin 50 100 coin 50 100"
proof-
  have consistent: "consistent
          (\<lambda>r. and (if r = V (I 1) then snd (V (I 1), cexp.Eq (Num 50)) else cexp.Bc True)
                (and (if r = V (I 1) then snd (V (I 1), cexp.Eq (Num 50)) else cexp.Bc True) (c r))) \<Longrightarrow>
         consistent (\<lambda>r. and (if r = V (I 1) then snd (V (I 1), cexp.Eq (Num 50)) else cexp.Bc True) (c r))"
    apply (simp add: consistent_def)
    using consistent_medial_medial_coin50
    by blast
  show ?thesis
  apply (simp add: subsumes_def coin 50 100_def posterior_def)
  apply (case_tac "consistent (\<lambda>r. and (if r = V (I 1) then snd (V (I 1), cexp.Eq (Num 50)) else cexp.Bc True)
                           (and (if r = V (I 1) then snd (V (I 1), cexp.Eq (Num 50)) else cexp.Bc True) (c r)))")
   apply (simp add: remove_input_constraints_def)
   apply clarify
   apply (case_tac "r = V (I 1)")
    apply simp
    apply (case_tac "consistent (\<lambda>r. and (if r = V (I 1) then snd (V (I 1), cexp.Eq (Num 50)) else cexp.Bc True) (c r))")
     apply (simp add: remove_input_constraints_def)
      apply simp
      apply (simp add: consistent)
     apply simp
     apply (case_tac "consistent (\<lambda>r. and (if r = V (I 1) then snd (V (I 1), cexp.Eq (Num 50)) else cexp.Bc True) (c r))")
      apply (simp add: remove_input_constraints_def option.case_eq_if)
    using consistent apply blast
    by simp
qed

definition merged_2_8_coin50 :: iEFSM where
  "merged_2_8_coin50 = {|
   (9, (9, 10), (vend pepsi)),
   (8, (2, 9), coin 50 100),
   (1, (0, 1), select pepsi),
   (6, (5, 6), (vend coke)),
   (3, (1, 5), coin 100 100),
   (5, (3, 4), (vend coke)),
   (4, (2, 3), coin 50 100),
   (0, (0, 1), select coke),
   (7, (1, 2), coin 50 50)
|}"

lemma replace_coin50: "replace_transition merged_2_8 7 1 2 coin 50 50 coin 50 50 = merged_2_8_coin50"
proof-
  have filter: "{a \<in> fset merged_2_8. snd a \<noteq> ((1, 2), coin 50 50)} = {
   (9, (9, 10), (vend pepsi)),
   (8, (2, 9), coin 50 100),
   (1, (0, 1), select pepsi),
   (6, (5, 6), (vend coke)),
   (3, (1, 5), coin 100 100),
   (5, (3, 4), (vend coke)),
   (4, (2, 3), coin 50 100),
   (0, (0, 1), select coke)}"
    apply (simp add: merged_2_8_def)
    apply standard
     apply clarify
     apply simp
     apply auto[1]
    apply clarify
    apply simp
    apply (case_tac "a=0")
     apply simp
    apply (case_tac "a=1")
     apply simp
    apply (case_tac "a=3")
     apply simp
    apply (case_tac "a=9")
     apply simp
    apply (case_tac "a=8")
     apply simp
    apply simp
    by auto
  show ?thesis
  apply (simp add: replace_transition_def ffilter_def)
  apply (simp add: Set.filter_def finsert_equiv Abs_fset_inverse)
    apply (simp add: merged_2_8_coin50_def filter)
    by auto
qed

lemma nondeterministic_pairs_merged_2_8_coin50: "nondeterministic_pairs merged_2_8_coin50 = {|(2, (3, 9), (coin 50 100, 4), coin 50 100, 8), (2, (9, 3), (coin 50 100, 8), coin 50 100, 4)|}"
proof-
  have minus_1: "{|(5, coin 100 100, 3), (2, coin 50 50, 2)|} |-| {|(2, coin 50 50, 2)|} = {|(5, coin 100 100, 3)|}"
    apply simp
    by auto
  have minus_3: "{(1, select coke, 0), (1, select pepsi, 1)} - {(1, select pepsi, 1)} = {(1, select coke, 0)}"
    apply (simp add: Str_coke Str_pepsi)
    by auto
  have minus_2: "{|(9, coin 50 100, 8::nat), (3, coin 50 100, 4)|} |-| {|(3, coin 50 100, 4)|} = {|(9, coin 50 100, 8)|}"
    apply simp
    by auto
  have state_nondeterminism_0: "state_nondeterminism 0 {|(1, select coke, 0), (1, select pepsi, 1)|} = {|(0, (1, 1), (select pepsi, 1), select coke, 0), (0, (1, 1), (select coke, 0), select pepsi, 1)|}"
    by (simp add: state_nondeterminism_def fimage_def minus_3)
  have outgoing_0_equiv: "{|(1, select pepsi, 1), (1, select coke, 0)|} = {|(1, select coke, 0), (1, select pepsi, 1)|}"
    by auto
  have state_nondeterminism_1: "state_nondeterminism 1 {|(5, coin 100 100, 3), (2, coin 50 50, 7)|} = {|(1, (2, 5), (coin 50 50, 7), coin 100 100, 3), (1, (5, 2), (coin 100 100, 3), coin 50 50, 7)|}"
    by eval
  have state_nondeterminism_2: "state_nondeterminism 2 {|(9, coin 50 100, 8), (3, coin 50 100, 4)|} = {|(2, (3, 9), (coin 50 100, 4), coin 50 100, 8), (2, (9, 3), (coin 50 100, 8), coin 50 100, 4)|}"
    by (simp add: state_nondeterminism_def minus_2)
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_2_8_coin50_def)
    apply (simp add: outgoing_transitions_def fimage_def)
    apply (simp add: outgoing_0_equiv state_nondeterminism_0 state_nondeterminism_1 state_nondeterminism_2)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply safe
    by (simp_all add: choices)
qed

lemma nondeterministic_pairs_merged_3_9_coin100: "nondeterministic_pairs merged_3_9_coin100 = {|
(3, (10, 4), ((vend pepsi), 9), (vend coke), 5), 
(3, (4, 10), ((vend coke), 5), (vend pepsi), 9)
|}"
proof-
  have minus_1: "{|(2, coin 50 50, 2), (5, coin 100 100, 3)|} |-| {|(5, coin 100 100, 3)|} = {|(2, coin 50 50, 2)|}"
    apply simp
    by auto
  have minus_2: "{|(4, (vend coke), 5), (10, (vend pepsi), 9)|} |-| {|(10, (vend pepsi), 9)|} = {|(4, (vend coke), 5)|}"
    apply (simp add: Str_coke Str_pepsi)
    by auto
  have minus_3: "{(1, select coke, 0), (1, select pepsi, 1)} - {(1, select pepsi, 1)} = {(1, select coke, 0)}"
    apply (simp add: Str_coke Str_pepsi)
    by auto
  have state_nondeterminism_0: "state_nondeterminism 0 {|(1, select coke, 0), (1, select pepsi, 1)|} = {|(0, (1, 1), (select pepsi, 1), select coke, 0), (0, (1, 1), (select coke, 0), select pepsi, 1)|}"
    by (simp add: state_nondeterminism_def fimage_def minus_3)
  have state_nondeterminism_1: "state_nondeterminism 1 {|(2, coin 50 50, 7), (5, coin 100 100, 3)|} = {|(1, (5, 2), (coin 100 100, 3), coin 50 50, 7), (1, (2, 5), (coin 50 50, 7), coin 100 100, 3)|}"
    by eval
  have state_nondeterminism_3: "state_nondeterminism 3 {|(4, (vend coke), 5), (10, (vend pepsi), 9)|} = {|(3, (10, 4), ((vend pepsi), 9), (vend coke), 5), (3, (4, 10), ((vend coke), 5), (vend pepsi), 9)|}"
    by (simp add: state_nondeterminism_def minus_2)
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_3_9_coin100_def)
    apply (simp add: outgoing_transitions_def fimage_def)
    apply (simp add: state_nondeterminism_0 state_nondeterminism_1 state_nondeterminism_3)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply standard
    prefer 2
     apply (simp add: choices)
    apply clarify
    apply simp
    using choices by auto
qed

lemma nondeterministic_simulates_trace_merged_vends_pta_4_4: "nondeterministic_simulates_trace (tm merged_vends) (tm pta) 4 4 <R 1 := (Str ''coke'')> Map.empty t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps: "\<forall>aa b. possible_steps (tm pta) 4 Map.empty aa b = {||}"
    apply (simp add: possible_steps_fst)
    by (simp add: tm_def pta_def Set.filter_def)
  case (Cons a t)
  then show ?case
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps)
qed

lemma possible_steps_not_vend: "aa = (STR ''vend'') \<longrightarrow> b \<noteq> [] \<Longrightarrow> possible_steps (tm pta) 3 Map.empty aa b = {||}"
  apply (simp add: possible_steps_fst)
  apply (simp add: tm_def pta_def Set.filter_def)
  apply (simp add: (vend coke)_def)
  by auto

lemma nondetermnistic_step_not_vend: "aa = (STR ''vend'') \<longrightarrow> b \<noteq> [] \<Longrightarrow> nondeterministic_step (tm pta) 3 Map.empty aa b = None"
  by (simp add: nondeterministic_step_def possible_steps_not_vend)

lemma possible_steps_vend: "possible_steps (tm merged_vends) 3 r (STR ''vend'') [] = {|(4, vend_general)|}"
  apply (simp add: possible_steps_fst)
  apply (simp add: tm_def merged_vends_def Set.filter_def)
  apply safe
           apply (simp_all add: selectGeneral_def vend_general_def)
  by force

lemma nondeterministic_simulates_trace_merged_vends_pta_3_3: "nondeterministic_simulates_trace (tm merged_vends) (tm pta) 3 3 <R 1 := (Str ''coke'')> Map.empty t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have regsimp: "(\<lambda>a. if a = R 1 then Some ((Str ''coke'')) else None) = <R 1 := (Str ''coke'')>"
    apply (rule ext)
    by simp
  case (Cons a t)
  then show ?case
    apply (case_tac "a=((STR ''vend''), [])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
        apply (simp add: step_nondet_step_equiv step_pta_vend_3)
       apply (simp add: possible_steps_vend)
       apply (simp add: vend_general_def regsimp)
      apply (simp add: vend_general_def)
     apply (simp add: nondeterministic_simulates_trace_merged_vends_pta_4_4)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondetermnistic_step_not_vend)
qed

lemma possible_steps_pta_2_not_coin50: "aa = (STR ''coin'') \<longrightarrow> b \<noteq> [Num 50] \<Longrightarrow> possible_steps (tm pta) 2 Map.empty aa b = {||}"
  apply (simp add: possible_steps_fst)
  apply (simp add: Set.filter_def tm_def pta_def)
  apply (simp add: coin 50 100_def hd_input2state)
  by (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))

lemma possible_steps_merged_vends_coin50_2: "\<forall>r. possible_steps (tm merged_vends) 2 r (STR ''coin'') [Num 50] = {|(3, coin 50 100)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
              apply (simp_all add: selectGeneral_def)
    by force

lemma nondeterministic_simulates_trace_merged_vends_pta_2_2: "nondeterministic_simulates_trace (tm merged_vends) (tm pta) 2 2 <R 1 := (Str ''coke'')> Map.empty t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have coin50_updates: "\<forall>r. EFSM.apply_updates (Updates coin 50 100) (join_ir [Num 50] r) r = r"
    apply clarify
    apply (rule ext)
    by (simp add:)
  have regsimp: "(\<lambda>a. if a = R 1 then Some ((Str ''coke'')) else None) = <R 1 := (Str ''coke'')>"
    apply (rule ext)
    by simp
  case (Cons a t)
  then show ?case
    apply (case_tac "a=((STR ''coin''), [Num 50])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
        apply (simp add: step_nondet_step_equiv step_pta_coin50_2)
       apply (simp add: possible_steps_merged_vends_coin50_2)
       apply (simp only: coin50_updates regsimp)
      apply (simp add: coin 50 100_def)
     apply (simp add: nondeterministic_simulates_trace_merged_vends_pta_3_3)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps_pta_2_not_coin50)
qed

lemma nondeterministic_simulates_trace_merged_vends_pta_6_6: "nondeterministic_simulates_trace (tm merged_vends) (tm pta) 6 6 <R 1 := (Str ''coke'')> Map.empty t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps: "\<forall>aa b. possible_steps (tm pta) 6 Map.empty aa b = {||}"
    apply (simp add: possible_steps_fst)
    by (simp add: tm_def pta_def Set.filter_def)
  case (Cons a t)
  then show ?case
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps)
qed

lemma possible_steps_pta_5_not_vend: "a = (STR ''vend'') \<longrightarrow> b \<noteq> [] \<Longrightarrow> possible_steps (tm pta) 5 Map.empty a b = {||}"
  apply (simp add: possible_steps_fst)
  apply (simp add: tm_def pta_def Set.filter_def (vend coke)_def)
  by force

lemma nondeterministic_simulates_trace_merged_vends_pta_5_5: "nondeterministic_simulates_trace (tm merged_vends) (tm pta) 5 5 <R 1 := (Str ''coke'')> Map.empty t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have regsimp: "(\<lambda>a. if a = R 1 then Some ((Str ''coke'')) else None) = <R 1 := (Str ''coke'')>"
    apply (rule ext)
    by simp
  have possible_steps_vend: "possible_steps (tm merged_vends) 5 <R 1 := (Str ''coke'')> (STR ''vend'') [] = {|(6, vend_general)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply (simp add: vend_general_def)
    by force
  case (Cons a t)
  case (Cons a t)
  then show ?case
    apply (case_tac "a = ((STR ''vend''), [])")
     apply (simp add: regsimp)
     apply (rule nondeterministic_simulates_trace.step_some)
        apply (simp add: step_nondet_step_equiv step_pta_vend_5)
       apply (simp add: possible_steps_vend)
       apply (simp add: vend_general_def regsimp)
      apply (simp add: vend_general_def)
     apply (simp add: nondeterministic_simulates_trace_merged_vends_pta_6_6)
    apply (case_tac a)
    apply (simp add: regsimp)
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps_pta_5_not_vend)
qed

lemma possible_steps_pta_1_not_coin: "aa = (STR ''coin'') \<longrightarrow> b \<noteq> [Num 50] \<Longrightarrow>
       aa = (STR ''coin'') \<longrightarrow> b \<noteq> [Num 100] \<Longrightarrow>
       possible_steps (tm pta) 1 Map.empty aa b = {||}"
  apply (simp add: possible_steps_fst)
  apply (simp add: tm_def pta_def Set.filter_def)
  apply clarify
  apply (case_tac "Label baa = (STR ''coin'')")
   apply simp
   apply (case_tac "ba = 2")
    apply (simp add: hd_input2state)
    apply (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))
   apply (simp add: hd_input2state)
   apply (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))
  by (simp add:)

lemma possible_steps_merged_vends_coin50_1: "possible_steps (tm merged_vends) 1 r (STR ''coin'') [Num 50] = {|(2, coin 50 50)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
              apply (simp_all add: selectGeneral_def)
  by force

lemma possible_steps_merged_vends_coin100: "possible_steps (tm merged_vends) 1 r (STR ''coin'') [Num 100] = {|(5, coin 100 100)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
              apply (simp_all add: selectGeneral_def vend_general_def)
    by force

lemma nondeterministic_simulates_trace_merged_vends_pta_1_1: "nondeterministic_simulates_trace (tm merged_vends) (tm pta) 1 1 <R 1 := (Str ''coke'')> Map.empty t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have coin50_updates: "\<forall>r. EFSM.apply_updates (Updates coin 50 50) (join_ir [Num 50] r) r = r"
    apply clarify
    apply (rule ext)
    by (simp add:)
  have regsimp: "(\<lambda>a. if a = R 1 then Some ((Str ''coke'')) else None) = <R 1 := (Str ''coke'')>"
    apply (rule ext)
    by simp
  case (Cons a t)
  then show ?case
    apply (case_tac "a=((STR ''coin''), [Num 50])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
        apply (simp add: step_nondet_step_equiv step_pta_coin50_1)
       apply (simp add: possible_steps_merged_vends_coin50_1)
       apply (simp only: coin50_updates regsimp)
      apply (simp add: coin 50 50_def)
      apply (simp add: nondeterministic_simulates_trace_merged_vends_pta_2_2)
      apply (case_tac "a=((STR ''coin''), [Num 100])")
       apply (simp add: regsimp)
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: step_nondet_step_equiv step_pta_coin100_1)
        apply (simp add: possible_steps_merged_vends_coin100)
       apply (simp add: coin 100 100_def)
      apply (simp add: coin 100 100_def)
     apply (simp add: nondeterministic_simulates_trace_merged_vends_pta_5_5)
    apply (case_tac a)
    apply (simp add: regsimp)
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps_pta_1_not_coin)
qed

lemma possible_steps_pta_9_not_vend: "aa = (STR ''vend'') \<longrightarrow> b \<noteq> [] \<Longrightarrow>
       possible_steps (tm pta) 9 Map.empty aa b = {||}"
  apply (simp add: possible_steps_fst)
  apply (simp add: tm_def pta_def Set.filter_def)
  apply (simp add: (vend pepsi)_def)
  by auto

lemma nondeterministic_simulates_trace_merged_vends_pta_3_9: "nondeterministic_simulates_trace (tm merged_vends) (tm pta) 3 9 <R 1 := (Str ''pepsi'')> Map.empty t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps: "\<forall>r. possible_steps (tm merged_vends) 3 r (STR ''vend'') [] = {|(4, vend_general)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
    apply (simp_all add: vend_general_def)
    by force
  have possible_steps_10: "\<forall>aaa b. possible_steps (tm pta) 10 Map.empty aaa b = {||}"
    apply (simp add: possible_steps_fst)
    by (simp add: tm_def pta_def Set.filter_def)
  case (Cons a t)
  then show ?case
    apply (case_tac "a=((STR ''vend''), [])")
    apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
        apply (simp add: step_nondet_step_equiv step_pta_vend_9)
       apply (simp add: possible_steps)
       apply (simp add: vend_general_def)
      apply (simp add: vend_general_def)
     apply (case_tac t)
      apply (simp add: nondeterministic_simulates_trace.base)
     apply (case_tac aa)
     apply simp
     apply (rule nondeterministic_simulates_trace.step_none)
     apply (simp add: nondeterministic_step_def possible_steps_10)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps_pta_9_not_vend)
qed

lemma possible_steps_pta_8_not_coin: "aa = (STR ''coin'') \<longrightarrow> b \<noteq> [Num 50] \<Longrightarrow>
       possible_steps (tm pta) 8 Map.empty aa b = {||}"
  apply (simp add: possible_steps_fst)
  apply (simp add: tm_def pta_def Set.filter_def)
  apply (simp add: coin 50 100_def hd_input2state)
  by (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))

lemma nondeterministic_simulates_trace_merged_vends_pta_2_8: "nondeterministic_simulates_trace (tm merged_vends) (tm pta) 2 8 <R 1 := (Str ''pepsi'')> Map.empty t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps: "possible_steps (tm merged_vends) 2 <R 1 := (Str ''pepsi'')> (STR ''coin'') [Num 50] = {|(3, coin 50 100)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
              apply (simp_all add: selectGeneral_def vend_general_def)
    by force
  case (Cons a t)
  have regsimp: "\<forall>d. (\<lambda>a. if a = R 1 then Some d else None) = <R 1 := d>"
    apply clarify
    apply (rule ext)
    by simp
  then show ?case
    apply (case_tac "a=((STR ''coin''), [Num 50])")
     apply (simp add: regsimp)
     apply (rule nondeterministic_simulates_trace.step_some)
        apply (simp add: step_nondet_step_equiv step_pta_coin50_8)
       apply (simp add: possible_steps)
       apply (simp add: coin 50 100_def)
      apply (simp add: coin 50 100_def)
     apply (simp add: nondeterministic_simulates_trace_merged_vends_pta_3_9)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps_pta_8_not_coin)
qed

lemma possible_steps_pt_7_not_coin: "aa = (STR ''coin'') \<longrightarrow> b \<noteq> [Num 50] \<Longrightarrow>
       possible_steps (tm pta) 7 Map.empty aa b = {||}"
  apply (simp add: possible_steps_fst)
  apply (simp add: tm_def pta_def Set.filter_def coin 50 50_def hd_input2state)
  by (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))

lemma nondeterministic_simulates_trace_merged_vends_pta_1_7: "nondeterministic_simulates_trace (tm merged_vends) (tm pta) 1 7 <R 1 := (Str ''pepsi'')> Map.empty t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps_coin50: "\<forall>r. possible_steps (tm merged_vends) 1 r (STR ''coin'') [Num 50] = {|(2, coin 50 50)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
              apply (simp_all add: selectGeneral_def)
    by force
  have regsimp: "\<forall>d. (\<lambda>a. if a = R 1 then Some d else None) = <R 1 := d>"
    apply clarify
    apply (rule ext)
    by simp
  case (Cons a t)
  then show ?case
    apply (case_tac "a=((STR ''coin''), [Num 50])")
     apply (simp add: regsimp)
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: step_nondet_step_equiv step_pta_coin50_7)
        apply (simp add: possible_steps_coin50)
       apply (simp add: coin 50 50_def)
      apply (simp add: coin 50 50_def)
     apply (simp add: nondeterministic_simulates_trace_merged_vends_pta_2_8)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps_pt_7_not_coin)
qed

lemma possible_steps_pta_0_not_select: " aa = (STR ''select'') \<longrightarrow> b \<noteq> [(Str ''coke'')] \<Longrightarrow>
       aa = (STR ''select'') \<longrightarrow> b \<noteq> [(Str ''pepsi'')] \<Longrightarrow>
       possible_steps (tm pta) 0 Map.empty aa b = {||}"
  apply (simp add: possible_steps_fst)
  apply (simp add: tm_def pta_def Set.filter_def)
  apply clarify
  apply simp
  apply (case_tac "ba = 1")
   apply (simp add: hd_input2state)
   apply (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))
  apply (simp add: hd_input2state)
  by (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))

lemma nondeterministic_simulates_trace_merged_vends_pta_0_0: "nondeterministic_simulates_trace (tm merged_vends) (tm pta) 0 0 Map.empty Map.empty t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps: "\<forall>d. possible_steps (tm merged_vends) 0 Map.empty (STR ''select'') [d] = {|(1, selectGeneral)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
              apply (simp_all add: selectGeneral_def)
    by force
  have selectGeneral_updates: "\<forall>d. EFSM.apply_updates (Updates selectGeneral) (join_ir [d] Map.empty) Map.empty = <R 1 := d>"
    apply clarify
    apply (rule ext)
    by (simp add: selectGeneral_def)
  case (Cons a t)
  then show ?case
    apply (case_tac "a=((STR ''select''), [(Str ''coke'')])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: step_nondet_step_equiv step_pta_select coke)
        apply (simp add: possible_steps)
       apply (simp only: selectGeneral_updates)
      apply (simp add: selectGeneral_def)
     apply (simp add: nondeterministic_simulates_trace_merged_vends_pta_1_1)
    apply (case_tac "a=((STR ''select''), [(Str ''pepsi'')])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: step_nondet_step_equiv step_pta_select pepsi)
        apply (simp add: possible_steps)
       apply (simp only: selectGeneral_updates)
      apply (simp add: selectGeneral_def)
     apply (simp add: nondeterministic_simulates_trace_merged_vends_pta_1_7)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps_pta_0_not_select)
qed

lemma nondeterministic_pairs_merged_vends: "nondeterministic_pairs merged_vends = {||}"
proof-
  have minus_1: "{|(2, coin 50 50, 2), (5, coin 100 100, 3)|} |-| {|(5, coin 100 100, 3)|} = {|(2, coin 50 50, 2)|}"
    apply simp
    by auto
  have state_nondeterminism_1: "state_nondeterminism 1 {|(2, coin 50 50, 2), (5, coin 100 100, 3)|} = {|(1, (5, 2), (coin 100 100, 3), coin 50 50, 2), (1, (2, 5), (coin 50 50, 2), coin 100 100, 3)|}"
    by (simp add: state_nondeterminism_def minus_1)
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_vends_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_1)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    using choices by auto
qed

lemma merge_1_7: "merge pta 1 7 generator modifier = Some merged_vends"
proof-
  have leaves_2_pta: "leaves 2 pta = 1"
  proof-
    have set_filter: "Set.filter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) (fset pta) = {(2, (1, 2), coin 50 50)}"
      apply (simp add: Set.filter_def pta_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: leaves_def ffilter_def fthe_elem_def Abs_fset_inverse set_filter)
  qed
  have leaves_7_pta: "leaves 7 pta = 7"
  proof-
    have set_filter: "Set.filter (\<lambda>x. \<exists>a b ba. x = (7, (a, b), ba)) (fset pta) = {(7, (7, 8), coin 50 50)}"
      apply (simp add: Set.filter_def pta_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: leaves_def ffilter_def fthe_elem_def Abs_fset_inverse set_filter)
  qed
  have arrives_2_merged_1_7: "arrives 2 merged_1_7 = 2"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_1_7 = {|(2, (1, 2), coin 50 50)|}"
      apply (simp add: ffilter_def merged_1_7_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_7_merged_1_7: "arrives 7 merged_1_7 = 8"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (7, (a, b), ba)) merged_1_7 = {|(7, (1, 8), coin 50 50)|}"
      apply (simp add: ffilter_def merged_1_7_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have directly_subsumes_coin50_coin50: "\<forall>s. directly_subsumes (tm pta) (tm merged_2_8) s coin 50 50 coin 50 50"
    by (simp add: directly_subsumes_def subsumes_coin_50_50_coin_50_50)
  have easy_merge: "easy_merge pta merged_2_8 7 1 1 2 2 coin 50 50 7 coin 50 50 2 generator = Some merged_2_8_coin50"
    unfolding easy_merge_def
    apply (simp add: directly_subsumes_coin50_coin50)
    by (simp add: replace_coin50)
  have merge_transitions: "merge_transitions pta merged_2_8 7 1 1 2 2 coin 50 50 7 coin 50 50 2 generator modifier True = Some merged_2_8_coin50"
    apply (simp add: merge_transitions_def)
    by (simp add: easy_merge)
  have leaves_2_merged_2_8: "leaves 2 merged_2_8 = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_2_8 = {|(2, (1, 2), coin 50 50)|}"
      apply (simp add: ffilter_def merged_2_8_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have arrives_2_merged_2_8: "arrives 2 merged_2_8 = 2"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_2_8 = {|(2, (1, 2), coin 50 50)|}"
      apply (simp add: ffilter_def merged_2_8_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_7_merged_2_8: "arrives 7 merged_2_8 = 2"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (7, (a, b), ba)) merged_2_8= {|(7, (1, 2), coin 50 50)|}"
      apply (simp add: ffilter_def merged_2_8_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by simp_all 
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_4_merged_2_8_coin50: "arrives 4 merged_2_8_coin50 = 3"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (4, (a, b), ba)) merged_2_8_coin50 = {|(4, (2, 3), coin 50 100)|}"
      apply (simp add: ffilter_def merged_2_8_coin50_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_8_merged_2_8_coin50: "arrives 8 merged_2_8_coin50 = 9"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (8, (a, b), ba)) merged_2_8_coin50 = {|(8, (2, 9), coin 50 100)|}"
      apply (simp add: ffilter_def merged_2_8_coin50_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have merge_states_3_9_merged_2_8_coin50: "merge_states 3 9 merged_2_8_coin50 = merged_3_9 \<and> merge_states 9 3 merged_2_8_coin50 = merged_3_9"
    apply (simp add: merge_states_def merge_states_aux_def merged_2_8_coin50_def merged_3_9_def)
    by auto
  have leaves_4_pta: "leaves 4 pta = 2"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (4, (a, b), ba)) pta = {|(4, (2, 3), coin 50 100)|}"
      apply (simp add: ffilter_def pta_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have leaves_8_pta: "leaves 8 pta = 8"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (8, (a, b), ba)) pta = {|(8, (8, 9), coin 50 100)|}"
      apply (simp add: ffilter_def pta_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have leaves_4_merged_3_9: "leaves 4 merged_3_9 = 2 \<and>arrives 4 merged_3_9 = 3"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (4, (a, b), ba)) merged_3_9 = {|(4, (2, 3), coin 50 100)|}"
      apply (simp add: ffilter_def merged_3_9_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: arrives_def leaves_def ffilter)
  qed
  have arrives_8_merged_3_9: "arrives 8 merged_3_9 = 3 \<and> leaves 8 merged_3_9 = 2"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (8, (a, b), ba)) merged_3_9 = {|(8, (2, 3), coin 50 100)|}"
      apply (simp add: ffilter_def merged_3_9_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: leaves_def arrives_def ffilter)
  qed
  have coin 50 100_subsumes_self: "directly_subsumes (tm pta) (tm merged_3_9) 2 coin 50 100 coin 50 100"
    by (simp add: directly_subsumes_def subsumes_coin 50 100_coin 50 100)
  have merge_transitions_2: "merge_transitions pta merged_3_9 8 2 2 3 3 coin 50 100 8 coin 50 100 4 generator modifier True = Some merged_3_9_coin100"
  proof-
    show ?thesis
      apply (simp add: merge_transitions_def)
      apply (simp add: easy_merge_def coin 50 100_subsumes_self)
      by eval
  qed
  have arrives_5_merged_3_9_coin100: "arrives 5 merged_3_9_coin100 = 4"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (5, (a, b), ba)) merged_3_9_coin100 = {|(5, (3, 4), (vend coke))|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_3_9_coin100_def Set.filter_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_9_merged_3_9_coin100: "arrives 9 merged_3_9_coin100 = 10"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (9, (a, b), ba)) merged_3_9_coin100 = {|(9, (3, 10), (vend pepsi))|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_3_9_coin100_def Set.filter_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have merge_states_4_10: "merge_states 4 10 merged_3_9_coin100 = merged_4_10 \<and> merge_states 10 4 merged_3_9_coin100 = merged_4_10"
    apply (simp add: merge_states_def merge_states_aux_def merged_3_9_coin100_def merged_4_10_def)
    by auto
  have leaves_5_pta: "leaves 5 pta = 3"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (5, (a, b), ba)) pta = {|(5, (3, 4), (vend coke))|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def pta_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have leaves_9_pta: "leaves 9 pta = 9"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (9, (a, b), ba)) pta = {|(9, (9, 10), (vend pepsi))|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def pta_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have leaves_5_merged_4_10: "leaves 5 merged_4_10 = 3 \<and> arrives 5 merged_4_10 = 4"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (5, (a, b), ba)) merged_4_10 = {|(5, (3, 4), (vend coke))|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def merged_4_10_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: leaves_def arrives_def ffilter)
  qed
  have arrives_9_merged_4_10: "arrives 9 merged_4_10 = 4 \<and> leaves 9 merged_4_10 = 3"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (9, (a, b), ba)) merged_4_10 = {|(9, (3, 4), (vend pepsi))|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def merged_4_10_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: leaves_def arrives_def ffilter)
  qed
  have no_direct_subsumption_(vend coke)_(vend pepsi): "\<not> directly_subsumes (tm pta) (tm merged_4_10) 9 (vend coke) (vend pepsi)"
    by (simp add: cant_directly_subsume no_subsumption_(vend coke)_(vend pepsi))
  have no_direct_subsumption_(vend pepsi)_(vend coke): "\<not> directly_subsumes (tm pta) (tm merged_4_10) 3 (vend pepsi) (vend coke)"
    by (simp add: cant_directly_subsume (vend pepsi)_not_subsumes_(vend coke))
  have merge_(vend coke)_(vend pepsi): "merge_transitions pta merged_4_10 9 3 3 4 4 (vend pepsi) 9 (vend coke) 5 generator modifier True = Some merged_vends"
  proof-
    have easy_merge: "easy_merge pta merged_4_10 9 3 3 4 4 (vend pepsi) 9 (vend coke) 5 generator = None"
      apply (simp add: easy_merge_def generator_def)
      by (simp add: no_direct_subsumption_(vend coke)_(vend pepsi) no_direct_subsumption_(vend pepsi)_(vend coke))
    show ?thesis
      apply (simp add: merge_transitions_def easy_merge)
      apply (simp only: modifier_def)
      by (simp add: nondeterministic_simulates_def nondeterministic_simulates_trace_merged_vends_pta_0_0)
  qed
  have leaves_7_merged_2_8:  "leaves 7 merged_2_8 = 1"
    by eval
  show ?thesis
    apply (simp add: merge_def merge_states_1_7 nondeterminism_def nondeterministic_pairs_merged_1_7)
    apply (simp add: sorted_list_of_fset_def)
    apply (simp add: leaves_2_pta leaves_7_pta arrives_2_merged_1_7 arrives_7_merged_1_7)
    apply (simp add: leaves_2_merged_2_8 merge_states_2_8 arrives_2_merged_2_8 arrives_7_merged_2_8 leaves_7_merged_2_8)
    apply (simp add: merge_transitions nondeterminism_def nondeterministic_pairs_merged_2_8_coin50)
    apply (simp add: sorted_list_of_fset_def rev_def)
    apply (simp add: arrives_4_merged_2_8_coin50 arrives_8_merged_2_8_coin50 merge_states_3_9_merged_2_8_coin50)
    apply (simp add: leaves_4_pta leaves_8_pta leaves_4_merged_3_9 arrives_8_merged_3_9)
    apply (simp add: merge_transitions_2 nondeterminism_def nondeterministic_pairs_merged_3_9_coin100)
    apply (simp add: sorted_list_of_fset_def)
    apply (simp add: arrives_5_merged_3_9_coin100 arrives_9_merged_3_9_coin100 merge_states_4_10)
    apply (simp add: leaves_5_pta leaves_9_pta leaves_5_merged_4_10 arrives_9_merged_4_10)
    by (simp add: merge_(vend coke)_(vend pepsi) nondeterministic_pairs_merged_vends nondeterminism_def)
qed

lemma scoring_2: "sorted_list_of_fset (score merged_vends naive_score) = [(1, 3, 5), (2, 1, 2)]"
proof-
  have S_merged_vends: "S merged_vends = {|0, 1, 2, 3, 4, 5, 6|}"
    apply (simp add: S_def merged_vends_def)
    by auto
  have fset_S: "fset {|0, 1, 2, 3, 4, 5, 6|} = {0, 1, 2, 3, 4, 5, 6}"
    by simp
  have ffilter: "ffilter (\<lambda>(x, y). x < y) (Inference.S merged_vends |\<times>| Inference.S merged_vends) = {|
    (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6),
    (1, 2), (1, 3), (1, 4), (1, 5), (1, 6),
    (2, 3), (2, 4), (2, 5), (2, 6),
    (3, 4), (3, 5), (3, 6),
    (4, 5), (4, 6),
    (5, 6)
  |}"
    apply (simp add: filtered_pairs_def ffilter_def fset_both_sides Abs_fset_inverse fprod_def)
    apply (simp only: S_merged_vends fprod_equiv fset_S Set.filter_def)
    apply standard
     apply clarify
     apply simp
      apply (case_tac "a=6")
       apply auto[1]
      apply simp
      apply (case_tac "a=5")
       apply auto[1]
      apply simp
      apply (case_tac "a=4")
       apply auto[1]
      apply simp
      apply (case_tac "a=3")
       apply auto[1]
      apply simp
      apply (case_tac "a=2")
        apply auto[1]
      apply simp
      apply (case_tac "a=1")
        apply auto[1]
     apply simp
    apply clarify
    apply safe
    by auto
  have scores: "score merged_vends naive_score = {|(2, 1, 2), (1, 3, 5)|}"
    apply (simp add: score_def ffilter)
    apply (simp add: outgoing_transitions_def merged_vends_def fimage_def)
    apply (simp add: naive_score_empty set_equiv)
    apply (simp add: naive_score_def fprod_def)
    apply (simp add: selectGeneral_def vend_general_def Abs_fset_inverse)
    by auto
  show ?thesis
    by (simp add: scores sorted_list_of_fset_def)
qed

definition merged_1_2 :: iEFSM where
  "merged_1_2 = {|(0, (0, 1), selectGeneral), (2, (1, 1), coin 50 50),  (4, (1, 3), coin 50 100), (5, (3, 4), vend_general),
                                              (3, (1, 5), coin 100 100), (6, (5, 6), vend_general)|}"

lemma merge_states_1_2: "merge_states 1 2 merged_vends = merged_1_2"
  by (simp add: merge_states_def merge_states_aux_def merged_vends_def merged_1_2_def)

lemma nondeterministic_pairs_merged_1_2: "nondeterministic_pairs merged_1_2 = {|
(1, (3, 1), (coin 50 100, 4), coin 50 50, 2),
(1, (1, 3), (coin 50 50, 2), coin 50 100, 4)
|}"
proof-
  have minus_1: "{|(1, coin 50 50, 2), (3, coin 50 100, 4), (5, coin 100 100, 3)|} |-| {|(3, coin 50 100, 4)|} = {|(1, coin 50 50, 2), (5, coin 100 100, 3)|}"
    apply simp
    by auto
  have minus_2: "{|(1, coin 50 50, 2), (3, coin 50 100, 4), (5, coin 100 100, 3)|} |-| {|(5, coin 100 100, 3)|} = {|(1, coin 50 50, 2), (3, coin 50 100, 4)|}"
    apply simp
    by auto
  have state_nondeterminism_1: "state_nondeterminism 1 {|(1, coin 50 50, 2), (3, coin 50 100, 4), (5, coin 100 100, 3)|} = {|
   (1, (5, 3), (coin 100 100, 3), coin 50 100, 4),
   (1, (5, 1), (coin 100 100, 3), coin 50 50, 2),
   (1, (3, 5), (coin 50 100, 4), coin 100 100, 3),
   (1, (3, 1), (coin 50 100, 4), coin 50 50, 2),
   (1, (1, 5), (coin 50 50, 2), coin 100 100, 3),
   (1, (1, 3), (coin 50 50, 2), coin 50 100, 4)|}"
    apply (simp add: state_nondeterminism_def minus_1 minus_2)
    by auto
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_1_2_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_1)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply safe
    by (simp_all add: choices)
qed

lemma merge_states_1_3: "merge_states 1 3 merged_1_2 = merged_1_3 \<and> merge_states 3 1 merged_1_2 = merged_1_3"
  by (simp add: merge_states_def merge_states_aux_def merged_1_2_def merged_1_3_def)

definition r1_true :: "context" where
  "r1_true = \<lbrakk>V (R 1) \<mapsto> Bc True\<rbrakk>"

lemma nondeterministic_simulates_trace_merged_1_3_coin_merged_vends_1_3: "nondeterministic_simulates_trace (tm merged_1_3_coin) (tm merged_vends) 1 3 <R 1 := hd b, R 2 := Num 100> <R 1 := hd b> t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have regsimp_1: "\<forall>d. (\<lambda>a. if a = R 1 then Some d else None) = <R 1 := d>"
    apply clarify
    apply (rule ext)
    by simp
  have regsimp_2: "\<forall>d. (\<lambda>a. if a = R 2 then Some (Num 100) else if a = R 1 then Some d else None) = <R 1 := d, R 2 := Num 100>"
    apply clarify
    apply (rule ext)
    by simp
  have possible_steps_merged_vends_vend: "\<forall>r. possible_steps (tm merged_vends) 3 r (STR ''vend'') [] = {|(4, vend_general)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: merged_vends_def Set.filter_def tm_def)
    apply safe
             apply (simp_all add: vend_general_def)
    by force
  have possible_steps_merged_1_3_coin_vend: "\<forall>r. possible_steps (tm merged_1_3_coin) 1 r (STR ''vend'') [] = {|(4, vend_general)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_1_3_coin_def Set.filter_def)
    apply safe
           apply (simp_all add: coinGeneral_def vend_general_def)
    by force
  have possible_steps_merged_vends_4: "\<forall>r l i. possible_steps (tm merged_vends) 4 r l i = {||}"
    apply (simp add: possible_steps_fst)
    by (simp add: merged_vends_def Set.filter_def tm_def)
  have possible_steps_not_vend: "\<And>aa ba.
       aa = (STR ''vend'') \<longrightarrow> ba \<noteq> [] \<Longrightarrow>
       possible_steps (tm merged_vends) 3 (\<lambda>a. if a = R 1 then Some (hd b) else None) aa ba = {||}"
    apply (simp add: possible_steps_fst)
    apply (simp add: merged_vends_def Set.filter_def tm_def)
    apply safe
    by (simp_all add: vend_general_def)
  case (Cons a t)
  then show ?case
    apply (case_tac "a= ((STR ''vend''), [])")
    apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
        apply (simp add: nondeterministic_step_def possible_steps_merged_vends_vend)
       apply (simp add: possible_steps_merged_1_3_coin_vend)
      apply (simp add: vend_general_def)
     apply (simp add: regsimp_1 vend_general_def regsimp_2)
     apply (case_tac t)
      apply (simp add: nondeterministic_simulates_trace.base)
     apply (case_tac aa)
     apply simp
     apply (rule nondeterministic_simulates_trace.step_none)
    apply (simp add: nondeterministic_step_def possible_steps_merged_vends_4)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps_not_vend)
qed

lemma nondeterministic_simulates_trace_merged_1_3_coin_merged_vends_1_2: "nondeterministic_simulates_trace (tm merged_1_3_coin) (tm merged_vends) 1 2 <R 1 := hd b, R 2 := Num 50> <R 1 := hd b> t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps_merged_1_3_coin_1_coin: "\<forall>r. possible_steps (tm merged_1_3_coin) 1 r (STR ''coin'') [Num 50] = {|(1, coinGeneral)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_1_3_coin_def Set.filter_def)
    apply safe
           apply (simp_all add: coinGeneral_def selectGeneral_2_def vend_general_def)
    by force
  have regsimp_1: "\<forall>d. (\<lambda>a. if a = R 1 then Some d else None) = <R 1 := d>"
    apply clarify
    apply (rule ext)
    by simp
  have regsimp_2: "\<forall>d. (\<lambda>x. if x = R 2
          then aval (snd (R 2, Plus (V (I 1)) (V (R 2))))
                (case_vname (\<lambda>n. input2state [Num 50] 1 (I n))
                  (\<lambda>n. if R n = R 2 then Some (Num 50) else if R n = R 1 then Some d else None))
          else EFSM.apply_updates []
                (case_vname (\<lambda>n. input2state [Num 50] 1 (I n))
                  (\<lambda>n. if R n = R 2 then Some (Num 50) else if R n = R 1 then Some d else None))
                (\<lambda>a. if a = R 2 then Some (Num 50) else if a = R 1 then Some d else None) x) = <R 1 := d, R 2 := Num 100>"
    apply clarify
    apply (rule ext)
    by simp
  have possible_steps_not_coin: "\<And>aa ba r.
       aa = (STR ''coin'') \<longrightarrow> ba \<noteq> [Num 50] \<Longrightarrow>
       possible_steps (tm merged_vends) 2 r aa ba = {||}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply (simp add: coin 50 100_def hd_input2state)
    by (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))
  case (Cons a t)
  then show ?case
    apply (case_tac "a = ((STR ''coin''), [Num 50])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: nondeterministic_step_def possible_steps_merged_vends_coin50_2)
        apply (simp add: possible_steps_merged_1_3_coin_1_coin)
       apply simp
      apply (simp add: coin 50 100_def coinGeneral_def)
     apply (simp add: coinGeneral_def coin 50 100_def regsimp_1 regsimp_2)
     apply (simp add: nondeterministic_simulates_trace_merged_1_3_coin_merged_vends_1_3)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps_not_coin)
qed

lemma nondeterministic_simulates_trace_merged_1_3_coin_merged_vends_5_5: "nondeterministic_simulates_trace (tm merged_1_3_coin) (tm merged_vends) 5 5 <R 1 := hd b, R 2 := Num 0> <R 1 := hd b> t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps_merged_vends_vend: "\<forall>r. possible_steps (tm merged_vends) 5 r (STR ''vend'') [] = {|(6, vend_general)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
             apply (simp_all add: vend_general_def)
    by force
  have possible_steps_other_vend: "\<forall>r. possible_steps (tm merged_1_3_coin) 5 r (STR ''vend'') [] = {|(6, vend_general)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_1_3_coin_def Set.filter_def)
    apply safe
             apply (simp_all add: vend_general_def)
    by force
  have stop: "\<forall>r aaa ba. possible_steps (tm merged_vends) 6 r aaa ba = {||}"
    apply (simp add: possible_steps_fst)
    by (simp add: tm_def merged_vends_def Set.filter_def)
  have stop_2: "\<And>aa ba.
       aa = (STR ''vend'') \<longrightarrow> ba \<noteq> [] \<Longrightarrow>
       possible_steps (tm merged_vends) 5 (\<lambda>a. if a = R 1 then Some (hd b) else None) aa ba = {||}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def vend_general_def)
    by auto
  case (Cons a t)
  then show ?case
    apply (case_tac "a=((STR ''vend''), [])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
        apply (simp add: nondeterministic_step_def possible_steps_merged_vends_vend)
       apply (simp add: possible_steps_other_vend)
      apply simp
     apply (simp add: vend_general_def)
     apply (case_tac t)
      apply (simp add: nondeterministic_simulates_trace.base)
    apply (case_tac aa)
    apply simp
     apply (rule nondeterministic_simulates_trace.step_none)
     apply (simp add: nondeterministic_step_def stop)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def stop_2)
qed

lemma nondeterministic_simulates_trace_merged_1_3_coin_merged_vends_1_1: "nondeterministic_simulates_trace (tm merged_1_3_coin) (tm merged_vends) 1 1 <R 1 := hd b, R 2 := Num 0> <R 1 := hd b> t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have regsimp_1: "\<forall>d. (\<lambda>a. if a = R 1 then Some d else None) = <R 1 := d>"
    apply clarify
    apply (rule ext)
    by simp
  have possible_steps_merged_1_3_coin_coin: "\<forall>r. possible_steps (tm merged_1_3_coin) 1 r (STR ''coin'') [Num 50] = {|(1, coinGeneral)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_1_3_coin_def Set.filter_def)
    apply safe
           apply (simp_all add: coinGeneral_def vend_general_def)
    by force
  have regsimp_2: "\<forall>d. (\<lambda>x. if x = R 2
          then aval (snd (R 2, Plus (V (I 1)) (V (R 2))))
                (case_vname (\<lambda>n. input2state [Num 50] 1 (I n))
                  (\<lambda>n. if R n = R 2 then Some (Num 0) else if R n = R 1 then Some d else None))
          else EFSM.apply_updates []
                (case_vname (\<lambda>n. input2state [Num 50] 1 (I n))
                  (\<lambda>n. if R n = R 2 then Some (Num 0) else if R n = R 1 then Some d else None))
                (\<lambda>a. if a = R 2 then Some (Num 0) else if a = R 1 then Some d else None) x) = <R 1 := d, R 2 := Num 50>"
    apply clarify
    apply (rule ext)
    by simp
  have possible_steps_coin_100: "\<forall>r. possible_steps (tm merged_vends) 1 r (STR ''coin'') [Num 100] = {|(5, coin 100 100)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
              apply simp_all
    by force
  have possible_steps_merged_1_3_coin_coin100: "\<forall>r. possible_steps (tm merged_1_3_coin) 1 r (STR ''coin'') [Num 100] = {|(1, coinGeneral), (5, coin 100 100)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_1_3_coin_def Set.filter_def)
    apply safe
               apply (simp_all add: coinGeneral_def vend_general_def)
    apply force
    by force
  have go_to_5: "\<forall>r. (5, coin 100 100) |\<in>|
    possible_steps (tm merged_1_3_coin) 1 r (STR ''coin'') [Num 100]"
    by (simp add: possible_steps_merged_1_3_coin_coin100)
  have regsimp_3: "\<forall>d. (\<lambda>a. if a = R 2 then Some (Num 0) else if a = R 1 then Some d else None) = <R 1 := d, R 2 := Num 0>"
    apply clarify
    apply (rule ext)
    by simp
  have stop: "\<And>aa ba.
       aa = (STR ''coin'') \<longrightarrow> ba \<noteq> [Num 50] \<Longrightarrow>
       aa = (STR ''coin'') \<longrightarrow> ba \<noteq> [Num 100] \<Longrightarrow>
       possible_steps (tm merged_vends) 1 (\<lambda>a. if a = R 1 then Some (hd b) else None) aa ba = {||}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply (simp add: coin 50 50_def coin 100 100_def)
    apply clarify
    apply simp
    apply (case_tac "bb=2")
     apply (simp add: hd_input2state)
     apply (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))
    apply (case_tac "bb=5")
     apply (simp add: hd_input2state)
     apply (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))
    by simp
  case (Cons a t)
  then show ?case
    apply (case_tac "a = ((STR ''coin''), [Num 50])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: nondeterministic_step_def possible_steps_merged_vends_coin50_1)
        apply (simp add: possible_steps_merged_1_3_coin_coin)
       apply (simp add: coinGeneral_def regsimp_2)
      apply (simp add: coin 50 50_def coinGeneral_def)
     apply (simp add: regsimp_1)
     apply (simp add: nondeterministic_simulates_trace_merged_1_3_coin_merged_vends_1_2)
    apply (case_tac "a = ((STR ''coin''), [Num 100])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
        apply (simp add: nondeterministic_step_def possible_steps_coin_100)
    using go_to_5 apply auto[1]
       apply simp
      apply (simp add: coin 100 100_def)
     apply (simp add: regsimp_1 regsimp_3 coin 100 100_def)
     apply (simp add: nondeterministic_simulates_trace_merged_1_3_coin_merged_vends_5_5)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def stop)
qed

lemma possible_steps_merged_vends_select: "\<forall>b. length b = 1 \<longrightarrow> possible_steps (tm merged_vends) 0 Map.empty (STR ''select'') b = {|(1, selectGeneral)|}"
  apply (simp add: possible_steps_fst)
  apply (simp add: tm_def merged_vends_def Set.filter_def)
  apply safe
            apply (simp_all add: selectGeneral_def)
  by force

lemma nondeterministic_simulates_trace_merged_1_3_coin_merged_vends_0_0:"nondeterministic_simulates_trace (tm merged_1_3_coin) (tm merged_vends) 0 0 Map.empty Map.empty t"
proof(induct t)
  case Nil
  then show ?case
  by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps_merged_1_3_coin_select: "\<forall>b. length b = 1 \<longrightarrow> possible_steps (tm merged_1_3_coin) 0 Map.empty (STR ''select'') b = {|(1, selectGeneral_2)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_1_3_coin_def Set.filter_def)
    apply safe
            apply (simp_all add: selectGeneral_2_def)
    by force
  have regsimp_1: "\<forall>b. length b = 1 \<longrightarrow>(\<lambda>a. if a = R 1 then aval (snd (R 1, V (I 1))) (case_vname (\<lambda>n. input2state b 1 (I n)) Map.empty)
             else EFSM.apply_updates [(R 2, L (Num 0))] (case_vname (\<lambda>n. input2state b 1 (I n)) Map.empty) Map.empty a) = <R 1 := hd b, R 2 := Num 0>"
    apply clarify
    apply (rule ext)
    by (simp add: hd_input2state)
  have regsimp_2: "\<forall>b. length b = 1 \<longrightarrow> (\<lambda>a. if a = R 1 then aval (snd (R 1, V (I 1))) (case_vname (\<lambda>n. input2state b 1 (I n)) Map.empty)
             else EFSM.apply_updates [] (case_vname (\<lambda>n. input2state b 1 (I n)) Map.empty) Map.empty a) = <R 1 := hd b>"
    apply clarify
    apply (rule ext)
    by (simp add: hd_input2state)
  have stop: "\<And>aa b.
       aa = (STR ''select'') \<longrightarrow> length b \<noteq> 1 \<Longrightarrow>
       possible_steps (tm merged_vends) 0 Map.empty aa b = {||}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
    by (simp_all add: selectGeneral_def)
  case (Cons a t)
  then show ?case
    apply (case_tac a)
    apply (case_tac "aa = (STR ''select'') \<and> length b = 1")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: nondeterministic_step_def possible_steps_merged_vends_select)
        apply (simp add: possible_steps_merged_1_3_coin_select)
       apply simp
      apply (simp add: selectGeneral_def selectGeneral_2_def)
     apply (simp add: selectGeneral_2_def selectGeneral_def)
     apply (simp add: regsimp_1 regsimp_2)
     apply (simp add: nondeterministic_simulates_trace_merged_1_3_coin_merged_vends_1_1)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def stop)
qed

lemma nondeterministic_simulates_merged_1_3_coin_merged_vends: "nondeterministic_simulates (tm merged_1_3_coin) (tm merged_vends)"
  apply (simp add: nondeterministic_simulates_def)
  by (simp add: nondeterministic_simulates_trace_merged_1_3_coin_merged_vends_0_0)

lemma nondeterministic_pairs_merged_1_3_coin: "nondeterministic_pairs merged_1_3_coin = {|
(1, (5, 1), (coin 100 100, 3), coinGeneral, 2),
(1, (1, 5), (coinGeneral, 2), coin 100 100, 3)|}"
proof-
  have minus_1: "{|(1, coinGeneral, 2), (4, vend_general, 5), (5, coin 100 100, 3)|} |-| {|(4, vend_general, 5)|} = {|(1, coinGeneral, 2), (5, coin 100 100, 3)|}"
    apply (simp add: coinGeneral_def vend_general_def)
    by auto
  have minus_2: "{|(1, coinGeneral, 2), (4, vend_general, 5), (5, coin 100 100, 3)|} |-| {|(5, coin 100 100, 3)|} = {|(1, coinGeneral, 2), (4, vend_general, 5)|}"
    apply (simp add: coinGeneral_def vend_general_def)
    by auto
  have state_nondeterminism_1: "state_nondeterminism 1 {|(1, coinGeneral, 2), (4, vend_general, 5), (5, coin 100 100, 3)|} = {|
(1, (5, 4), (coin 100 100, 3), vend_general, 5),
(1, (5, 1), (coin 100 100, 3), coinGeneral, 2),
(1, (4, 5), (vend_general, 5), coin 100 100, 3),
(1, (4, 1), (vend_general, 5), coinGeneral, 2),
(1, (1, 5),(coinGeneral, 2), coin 100 100, 3),
(1, (1, 4),(coinGeneral, 2), vend_general, 5)
|}"
    by eval
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_1_3_coin_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_1)
    apply (simp add: ffilter_def Set.filter_def fset_both_sides Abs_fset_inverse)
    apply safe
    by (simp_all add: choices)
qed

definition merged_4_6 :: iEFSM where
  "merged_4_6 = {|(0, (0, 1), selectGeneral_2), (2, (1, 1), coinGeneral), (5, (1, 4), vend_general), (6, (1, 4), vend_general)|}"

definition final :: iEFSM where
  "final = {|(0, (0, 1), selectGeneral_2), (2, (1, 1), coinGeneral), (6, (1, 4), vend_general)|}"

lemma directly_subsumes_vend_general_self: "directly_subsumes (tm merged_vends) (tm merged_4_6) 5 vend_general vend_general"
proof-
  have self_subsumpion: "\<forall>c. subsumes c vend_general vend_general"
    by (simp add: subsumes_def vend_general_def)
  show ?thesis
    by (simp add: directly_subsumes_def self_subsumpion)
qed

lemma nondeterministic_pairs_merged_1_5_coin: "nondeterministic_pairs merged_1_5_coin = {|(1, (4, 6), (vend_general, 5), vend_general, 6), (1, (6, 4), (vend_general, 6), vend_general, 5)|}"
proof-
  have minus_1: "{|(1, coinGeneral, 2::nat), (4, vend_general, 5), (6, vend_general, 6)|} |-| {|(4, vend_general, 5)|} = {|(1, coinGeneral, 2), (6, vend_general, 6)|}"
    apply (simp add: vend_general_def coinGeneral_def)
    by auto
  have minus_2: "{|(1, coinGeneral, 2::nat), (4, vend_general, 5), (6, vend_general, 6)|} |-| {|(6, vend_general, 6)|} = {|(1, coinGeneral, 2), (4, vend_general, 5)|}"
    apply (simp add: vend_general_def coinGeneral_def)
    by auto
  have state_nondeterminim_1: "state_nondeterminism 1 {|(1, coinGeneral, 2), (4, vend_general, 5), (6, vend_general, 6)|} = {|
     (1, (6, 4), (vend_general, 6), vend_general, 5),
     (1, (6, 1), (vend_general, 6), coinGeneral, 2),
     (1, (4, 6), (vend_general, 5), vend_general, 6),
     (1, (4, 1), (vend_general, 5), coinGeneral, 2),
     (1, (1, 6), (coinGeneral, 2), vend_general, 6),
     (1, (1, 4), (coinGeneral, 2), vend_general, 5)
   |}"
    by eval
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_1_5_coin_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminim_1)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply safe
    by (simp_all add: choices)
qed

lemma no_direct_subsumption_coinGeneral_coin 100 100:  "\<not>directly_subsumes (tm merged_vends) (tm merged_1_5) 1 coinGeneral coin 100 100"
proof-
  have possible_steps: "\<forall>d. possible_steps (tm merged_vends) 0 Map.empty (STR ''select'') [d] = {|(1, selectGeneral)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
              apply (simp_all add: selectGeneral_def)
    by force
  have possible_steps_merged_1_5: "\<forall>b. length b = 1 \<longrightarrow> possible_steps (tm merged_1_5) 0 Map.empty (STR ''select'') b = {|(1, selectGeneral_2)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_1_5_def Set.filter_def)
    apply safe
          apply (simp_all add: selectGeneral_2_def)
    by force
  have posterior_empty_selectGeneral_2: "posterior \<lbrakk>\<rbrakk> selectGeneral_2 = \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> Eq (Num 0)\<rbrakk>"
    apply (rule ext)
    by (simp add: posterior_def selectGeneral_2_def remove_input_constraints_def)
  have medial_coin 100 100: "medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> (Guard coin 100 100) = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0), V (I 1) \<mapsto> Eq (Num 100)\<rbrakk>"
    apply (rule ext)
    by (simp add: coin 100 100_def)
  have consistent_medial: "consistent \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0), V (I 1) \<mapsto> cexp.Eq (Num 100)\<rbrakk>"
    apply (simp add: consistent_def)
    apply (rule_tac x="<R 1 := d, R 2 := Num 0, I 1 := Num 100>" in exI)
    by (simp add: consistent_empty_4)
  have medial_coinGeneral: "\<forall>c. medial c (Guard coinGeneral) = c"
    apply clarify
    apply (rule ext)
    by (simp add: coinGeneral_def)
  have subsumption_violation: " (\<exists>r i. cval (posterior (medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> (Guard coin 100 100)) coinGeneral r) i = Some True \<and>
           cval (posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> coin 100 100 r) i \<noteq> Some True \<and>
           posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> coin 100 100 r \<noteq> Undef)"
    apply (rule_tac x="V (R 2)" in exI)
    apply (rule_tac x="Num 100" in exI)
    apply (simp add: medial_coin 100 100 posterior_def medial_coinGeneral Let_def consistent_medial)
    by (simp add: remove_input_constraints_def coinGeneral_def valid_def satisfiable_def coin 100 100_def)
  show ?thesis
    apply (simp add: directly_subsumes_def accepts_trace_def)
    apply standard
    apply (rule_tac x="[((STR ''select''), [d])]" in exI)
    apply standard
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps)
     apply (rule accepts.base)
    apply standard
     apply (rule gets_us_to.step_some)
      apply (simp add: step_def possible_steps)
     apply (simp add: gets_us_to.base)
    apply (simp add: anterior_context_def step_def possible_steps_merged_1_5 posterior_empty_selectGeneral_2)
    by (simp add: subsumes_def subsumption_violation)
qed

lemma no_direct_subsumption_coin 100 100_coinGeneral: "\<not> directly_subsumes (tm merged_vends) (tm merged_1_5) 1 coin 100 100 coinGeneral"
proof-
have possible_steps: "\<forall>d. possible_steps (tm merged_vends) 0 Map.empty (STR ''select'') [d] = {|(1, selectGeneral)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
              apply (simp_all add: selectGeneral_def)
    by force
  have possible_steps_merged_1_5: "\<forall>b. length b = 1 \<longrightarrow> possible_steps (tm merged_1_5) 0 Map.empty (STR ''select'') b = {|(1, selectGeneral_2)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_1_5_def Set.filter_def)
    apply safe
          apply (simp_all add: selectGeneral_2_def)
    by force
  have posterior_empty_selectGeneral_2: "posterior \<lbrakk>\<rbrakk> selectGeneral_2 = \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> Eq (Num 0)\<rbrakk>"
    apply (rule ext)
    by (simp add: posterior_def selectGeneral_2_def remove_input_constraints_def)
  have medial_coin 100 100: "medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> (Guard coin 100 100) = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0), V (I 1) \<mapsto> Eq (Num 100)\<rbrakk>"
    apply (rule ext)
    by (simp add: coin 100 100_def)
  have medial_coinGeneral: "\<forall>c. medial c (Guard coinGeneral) = c"
    apply clarify
    apply (rule ext)
    by (simp add: coinGeneral_def)
  have subsumption_violation: "\<exists>r i. cval (medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> (Guard coinGeneral) r) i = Some True \<and>
           cval (medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> (Guard coin 100 100) r) i \<noteq> Some True"
    apply (simp add: medial_coinGeneral medial_coin 100 100)
    by auto
  show ?thesis
    apply (simp add: directly_subsumes_def accepts_trace_def)
    apply standard
    apply (rule_tac x="[((STR ''select''), [d])]" in exI)
    apply standard
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps)
     apply (rule accepts.base)
    apply standard
     apply (rule gets_us_to.step_some)
      apply (simp add: step_def possible_steps)
     apply (simp add: gets_us_to.base)
    apply (simp add: anterior_context_def step_def possible_steps_merged_1_5 posterior_empty_selectGeneral_2)
    by (simp add: subsumes_def subsumption_violation)
qed

lemma nondeterministic_pairs_final: "nondeterministic_pairs final = {||}"
proof-
  have minus_1: "{|(1, coinGeneral, 2), (4, vend_general, 5)|} |-| {|(4, vend_general, 5)|} = {|(1, coinGeneral, 2)|}"
    apply (simp add: coinGeneral_def vend_general_def)
    by auto
  have state_nondeterminism_1: "state_nondeterminism 1 {|(1, coinGeneral, 2), (4, vend_general, 6)|} = {|(1, (1, 4), (coinGeneral, 2), vend_general, 6), (1, (4, 1), (vend_general, 6), coinGeneral, 2)|}"
    by eval
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def final_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_1)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    using choices by auto
qed

lemma possible_steps_merged_1_5_coin_coin: "\<forall>r. possible_steps (tm merged_1_5_coin) 1 r (STR ''coin'') [Num n] = {|(1, coinGeneral)|}"
  apply (simp add: possible_steps_fst)
  apply (simp add: tm_def merged_1_5_coin_def Set.filter_def)
  apply safe
       apply (simp_all add: coinGeneral_def vend_general_def selectGeneral_2_def)
  by force

lemma possible_steps_merged_1_5_coin_vend: "possible_steps (tm merged_1_5_coin) 1 r (STR ''vend'') [] = {|(4, vend_general), (6, vend_general)|}"
  apply (simp add: possible_steps_fst)
  apply (simp add: tm_def merged_1_5_coin_def Set.filter_def)
  apply safe
           apply (simp_all add: vend_general_def coinGeneral_def)
   apply force
  by force

lemma nondeterministic_simulates_trace_merged_1_5_coin_merged_vends_1_3: "nondeterministic_simulates_trace (tm merged_1_5_coin) (tm merged_vends) 1 3 <R 1 := b, R 2 := Num 100> <R 1 := b> t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps_merged_vends_4: "\<forall>r l i. possible_steps (tm merged_vends) 4 r l i = {||}"
    apply (simp add: possible_steps_fst)
    by (simp add: merged_vends_def Set.filter_def tm_def)
  have possible_steps_not_vend: "\<And>aa ba r.
       aa = (STR ''vend'') \<longrightarrow> ba \<noteq> [] \<Longrightarrow>
       possible_steps (tm merged_vends) 3 r aa ba = {||}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply (simp add: vend_general_def)
    by auto
  case (Cons a t)
  then show ?case
    apply (case_tac "a = ((STR ''vend''), [])")
    apply simp
    apply (rule nondeterministic_simulates_trace.step_some)
        apply (simp add: nondeterministic_step_def possible_steps_vend)
       apply (simp add: possible_steps_merged_1_5_coin_vend)
       apply auto[1]
       apply simp
      apply (simp add: vend_general_def)
     apply (case_tac t)
      apply (simp add: nondeterministic_simulates_trace.base)
     apply (case_tac aa)
     apply simp
     apply (rule nondeterministic_simulates_trace.step_none)
     apply (simp add: nondeterministic_step_def possible_steps_merged_vends_4)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps_not_vend)
qed

lemma nondeterministic_simulates_trace_merged_1_5_coin_merged_vends_1_2: "nondeterministic_simulates_trace (tm merged_1_5_coin) (tm merged_vends) 1 2 <R 1 := b, R 2 := Num 50> <R 1 := b> t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps_not_coin: "\<And>aa ba r.
       aa = (STR ''coin'') \<longrightarrow> ba \<noteq> [Num 50] \<Longrightarrow>
       possible_steps (tm merged_vends) 2 r aa ba = {||}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply (simp add: coin 50 100_def hd_input2state)
    by (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))
  have coin_general_updates: "\<forall>b. (EFSM.apply_updates (Updates coinGeneral)
       (\<lambda>x. case x of I n \<Rightarrow> input2state [Num 50] 1 (I n)
            | R n \<Rightarrow> if R n = R 2 then Some (Num 50) else if R n = R 1 then Some (b) else None)
       (\<lambda>a. if a = R 2 then Some (Num 50) else if a = R 1 then Some (b) else None)) = <R 1 := b, R 2 := Num 100>"
    apply clarify
    apply (rule ext)
    by (simp add: coinGeneral_def)
  have coin 50 100_updates: "\<forall> b. (EFSM.apply_updates (Updates coin 50 100)
       (case_vname (\<lambda>n. if n = 1 then Some (Num 50) else input2state [] (1 + 1) (I n)) (\<lambda>n. if n = 1 then Some (b) else None))
       (\<lambda>a. if a = R 1 then Some (b) else None)) = <R 1 := b>"
    apply clarify
    apply (rule ext)
    by (simp add: coin 50 100_def)
  case (Cons a t)
  then show ?case
    apply (case_tac "a = ((STR ''coin''), [Num 50])")
    apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: nondeterministic_step_def possible_steps_merged_vends_coin50_2)
        apply (simp add: possible_steps_merged_1_5_coin_coin)
       apply simp
      apply (simp add: coin 50 100_def coinGeneral_def)
     apply (simp add: coin_general_updates coin 50 100_updates)
     apply (simp add: nondeterministic_simulates_trace_merged_1_5_coin_merged_vends_1_3)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps_not_coin)
qed

lemma nondeterministic_simulates_trace_merged_1_5_coin_merged_vends_1_5: "nondeterministic_simulates_trace (tm merged_1_5_coin) (tm merged_vends) 1 5 <R 1 := hd b, R 2 := Num 100> <R 1 := hd b> t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps_vend: "\<forall>r. possible_steps (tm merged_vends) 5 r (STR ''vend'') [] = {|(6, vend_general)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply (simp add: vend_general_def)
    by force
  have stop: "\<forall>r aaa ba. possible_steps (tm merged_vends) 6 r aaa ba = {||}"
    apply (simp add: possible_steps_fst)
    by (simp add: tm_def merged_vends_def Set.filter_def)
  have stop_2: "\<And>aa ba r.
       aa = (STR ''vend'') \<longrightarrow> ba \<noteq> [] \<Longrightarrow>
       possible_steps (tm merged_vends) 5 r aa ba = {||}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def vend_general_def)
    by auto
  case (Cons a t)
  then show ?case
    apply (case_tac "a = ((STR ''vend''), [])")
    apply simp
    apply (rule nondeterministic_simulates_trace.step_some)
        apply (simp add: nondeterministic_step_def possible_steps_vend)
       apply (simp add: possible_steps_merged_1_5_coin_vend)
       apply auto[1]
       apply simp
       apply (simp add: vend_general_def)
      apply (case_tac t)
       apply simp
       apply (simp add: vend_general_def)
      apply (rule nondeterministic_simulates_trace.base)
     apply (case_tac aa)
     apply simp
     apply (rule nondeterministic_simulates_trace.step_none)
     apply (simp add: nondeterministic_step_def stop)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def stop_2)
qed

lemma nondeterministic_simulates_trace_merged_1_5_coin_merged_vends_1_1: "nondeterministic_simulates_trace (tm merged_1_5_coin) (tm merged_vends) 1 1 <R 1 := hd b, R 2 := Num 0> <R 1 := hd b> t"
proof (induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have stop: "\<And>aa ba r.
       aa = (STR ''coin'') \<longrightarrow> ba \<noteq> [Num 50] \<Longrightarrow>
       aa = (STR ''coin'') \<longrightarrow> ba \<noteq> [Num 100] \<Longrightarrow>
       possible_steps (tm merged_vends) 1 r aa ba = {||}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply (simp add: coin 50 50_def coin 100 100_def)
    apply clarify
    apply simp
    apply (case_tac "b=2")
     apply (simp add: hd_input2state)
     apply (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))
    apply (case_tac "b=5")
     apply (simp add: hd_input2state)
     apply (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))
    by simp
  have coin_general_updates: "\<forall>b. (EFSM.apply_updates (Updates coinGeneral)
       (\<lambda>x. case x of I n \<Rightarrow> input2state [Num 50] 1 (I n)
            | R n \<Rightarrow> if R n = R 2 then Some (Num 0) else if R n = R 1 then Some b else None)
       (\<lambda>a. if a = R 2 then Some (Num 0) else if a = R 1 then Some b else None)) = <R 1 := b, R 2 := Num 50>"
    apply clarify
    apply (rule ext)
    by (simp add: coinGeneral_def)
  have updates_coin 50 50: "\<forall>b. (EFSM.apply_updates (Updates coin 50 50)
       (case_vname (\<lambda>n. if n = 1 then Some (Num 50) else input2state [] (1 + 1) (I n)) (\<lambda>n. if n = 1 then Some (b) else None))
       (\<lambda>a. if a = R 1 then Some (b) else None)) = <R 1 := b>"
    apply clarify
    apply (rule ext)
    by (simp add: coin 50 50_def)
  have updates_coin 100 100: "\<forall>b. (EFSM.apply_updates (Updates coin 100 100)
       (case_vname (\<lambda>n. if n = 1 then Some (Num 100) else input2state [] (1 + 1) (I n)) (\<lambda>n. if n = 1 then Some (b) else None))
       (\<lambda>a. if a = R 1 then Some (b) else None)) = <R 1 := b>"
    apply clarify
    apply (rule ext)
    by (simp add: coin 100 100_def)
  have coin_general_updates_100: "\<forall>b. (EFSM.apply_updates (Updates coinGeneral)
       (\<lambda>x. case x of I n \<Rightarrow> input2state [Num 100] 1 (I n)
            | R n \<Rightarrow> if R n = R 2 then Some (Num 0) else if R n = R 1 then Some (b) else None)
       (\<lambda>a. if a = R 2 then Some (Num 0) else if a = R 1 then Some (b) else None)) = <R 1 := b, R 2 := Num 100>"
    apply clarify
    apply (rule ext)
    by (simp add: coinGeneral_def)
  case (Cons a t)
  then show ?case
    apply (case_tac "a = ((STR ''coin''), [Num 50])")
    apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: nondeterministic_step_def possible_steps_merged_vends_coin50_1)
        apply (simp add: possible_steps_merged_1_5_coin_coin)
       apply simp
      apply (simp add: coin 50 50_def coinGeneral_def)
     apply (simp only: coin_general_updates updates_coin 50 50)
     apply (simp add: nondeterministic_simulates_trace_merged_1_5_coin_merged_vends_1_2)
    apply (case_tac "a = ((STR ''coin''), [Num 100])")
       apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: nondeterministic_step_def possible_steps_merged_vends_coin100)
        apply (simp add: possible_steps_merged_1_5_coin_coin)
       apply simp
      apply (simp add: coin 100 100_def coinGeneral_def)
    apply (simp only: coin_general_updates_100 updates_coin 100 100)
    apply (simp add: nondeterministic_simulates_trace_merged_1_5_coin_merged_vends_1_5)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def stop)
qed

lemma nondeterministic_simulates_trace_merged_1_5_coin_merged_vends_0_0: "nondeterministic_simulates_trace (tm merged_1_5_coin) (tm merged_vends) 0 0 Map.empty Map.empty t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps_merged_1_5_coin_select: "\<forall>aa b. aa = (STR ''select'') \<and> length b = 1 \<longrightarrow> possible_steps (tm merged_1_5_coin) 0 Map.empty (STR ''select'') b = {|(1, selectGeneral_2)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: merged_1_5_coin_def tm_def Set.filter_def)
    apply safe
              apply (simp_all add: selectGeneral_2_def)
    by force
    have stop: "\<And>a ba r.
       a = (STR ''select'') \<longrightarrow> length ba \<noteq> 1 \<Longrightarrow>
       possible_steps (tm merged_vends) 0r a ba = {||}"
      apply (simp add: possible_steps_fst)
      apply (simp add: tm_def merged_vends_def Set.filter_def)
      apply safe
      by (simp_all add: selectGeneral_def)
    have selectGeneral_2_updates: "\<forall>b. length b = 1 \<longrightarrow> (EFSM.apply_updates (Updates selectGeneral_2) (\<lambda>x. case x of I n \<Rightarrow> input2state b 1 (I n) | R x \<Rightarrow> Map.empty x) Map.empty) = <R 1 := hd b, R 2 := Num 0>"
      apply clarify
      apply (rule ext)
      by (simp add: selectGeneral_2_def hd_input2state)
    have selectGeneral_updates: "\<forall>b. length b = 1 \<longrightarrow> (EFSM.apply_updates (Updates selectGeneral) (\<lambda>a. case a of I n \<Rightarrow> input2state b 1 (I n) | R x \<Rightarrow> Map.empty x) Map.empty) = <R 1 := hd b>"
      apply clarify
      apply (rule ext)
      by (simp add: selectGeneral_def hd_input2state)
  case (Cons a t)
  then show ?case
    apply (case_tac a)
    apply (case_tac "aa = (STR ''select'') \<and> length b = 1")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: nondeterministic_step_def possible_steps_merged_vends_select)
        apply (simp add: possible_steps_merged_1_5_coin_select)
       apply simp
      apply (simp add: selectGeneral_def selectGeneral_2_def)
     apply (simp only: selectGeneral_2_updates selectGeneral_updates)
    using nondeterministic_simulates_trace_merged_1_5_coin_merged_vends_1_1 try
    apply blast
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def stop)
qed

lemma merge_1_2: "merge merged_vends 1 2 generator modifier = Some final"
proof-
  have arrives_2_merged_1_2: "arrives 2 merged_1_2 = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_1_2 = {|(2, (1, 1), coin 50 50)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_1_2_def Set.filter_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_4_merged_1_2: "arrives 4 merged_1_2 = 3"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (4, (a, b), ba)) merged_1_2 = {|(4, (1, 3), coin 50 100)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_1_2_def Set.filter_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have leaves_2_merged_vends: "leaves 2 merged_vends = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_vends = {|(2, (1, 2), coin 50 50)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_vends_def Set.filter_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have leaves_2_merged_1_3: "(leaves 2 merged_1_3 = 1) \<and> (arrives 2 merged_1_3 = 1)"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_1_3 = {|(2, (1, 1), coin 50 50)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_1_3_def Set.filter_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: leaves_def arrives_def ffilter)
  qed
  have leaves_4_merged_vends: "leaves 4 merged_vends = 2"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (4, (a, b), ba)) merged_vends = {|(4, (2, 3), coin 50 100)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_vends_def Set.filter_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have arrives_4_merged_1_3: "arrives 4 merged_1_3 = 1 \<and> leaves 4 merged_1_3 = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (4, (a, b), ba)) merged_1_3 = {|(4, (1, 1), coin 50 100)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_1_3_def Set.filter_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: leaves_def arrives_def ffilter)
  qed
  have merged_1_3_neq_merged_1_8: "merged_1_3 \<noteq> merged_1_8"
    apply (simp add: merged_1_3_def merged_1_8_def set_equiv)
    apply (simp only: set_nequiv_def)
    apply (rule_tac x="(5, (3, 4), (vend coke))" in exI)
    by simp
  have easy_merge: "easy_merge merged_vends merged_1_3 2 1 1 1 1 coin 50 100 4 coin 50 50 2 generator = None"
    apply (simp add: easy_merge_def generator_def coin 50 50_cant_directly_subsume_coin 50 100)
    by (simp add: coin_50_100_cant_directly_subsume_coin_50_50)
  have merge_vends: "merge_transitions merged_vends merged_1_3 2 1 1 1 1 coin 50 100 4 coin 50 50 2 generator modifier True = Some merged_1_3_coin"
    apply (simp add: merge_transitions_def easy_merge)
    apply (simp add: modifier_def merged_1_3_neq_merged_1_8)
    by (simp add: nondeterministic_simulates_merged_1_3_coin_merged_vends)
  have arrives_2_merged_1_3_coin: "arrives 2 merged_1_3_coin = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_1_3_coin =  {|(2, (1, 1), coinGeneral)|}"
      apply (simp add: ffilter_def merged_1_3_coin_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_3_merged_1_3_coin: "arrives 3 merged_1_3_coin = 5"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (3, (a, b), ba)) merged_1_3_coin = {|(3, (1, 5), coin 100 100)|}"
      apply (simp add: ffilter_def merged_1_3_coin_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have merge_states_1_5:  "merge_states 1 5 merged_1_3_coin = merged_1_5 \<and> merge_states 5 1 merged_1_3_coin = merged_1_5"
    by (simp add: merge_states_def merge_states_aux_def merged_1_3_coin_def merged_1_5_def)
  have leaves_3_merged_vends: "leaves 3 merged_vends = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (3, (a, b), ba)) merged_vends = {|(3, (1, 5), coin 100 100)|}"
      apply (simp add: ffilter_def merged_vends_def Abs_fset_inverse fset_both_sides Set.filter_def)
      apply safe
      by simp_all
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have leaves_2_merged_1_5: "leaves 2 merged_1_5= 1 \<and> arrives 2 merged_1_5 = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_1_5 = {|(2, (1, 1), coinGeneral)|}"
      apply (simp add: ffilter_def merged_1_5_def Abs_fset_inverse fset_both_sides Set.filter_def)
      apply safe
      by (simp_all add: coinGeneral_def)
    show ?thesis
      by (simp add: leaves_def arrives_def ffilter)
  qed
  have arrives_3_merged_1_5: "arrives 3 merged_1_5 = 1 \<and> leaves 3 merged_1_5 = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (3, (a, b), ba)) merged_1_5 = {|(3, (1, 1), coin 100 100)|}"
      apply (simp add: ffilter_def merged_1_5_def Abs_fset_inverse fset_both_sides Set.filter_def)
      apply safe
      by (simp_all add: coinGeneral_def)
    show ?thesis
      by (simp add: leaves_def arrives_def ffilter)
  qed
  have easy_merge_1_5: "easy_merge merged_vends merged_1_5 1 1 1 1 1 coin 100 100 3 coinGeneral 2 generator = None"
  proof-
    have ffilter: "ffilter (\<lambda>x. snd x \<noteq> ((1, 1), coin 100 100) \<and> snd x \<noteq> ((1, 1), coinGeneral)) merged_1_5 = {|(0, (0, 1), selectGeneral_2), (5, (1, 4), vend_general),
      (6, (1, 6), vend_general)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_1_5_def Set.filter_def)
      by auto
    show ?thesis
      apply (simp add: easy_merge_def no_direct_subsumption_coinGeneral_coin 100 100 no_direct_subsumption_coin 100 100_coinGeneral)
      by (simp add: replace_transition_def ffilter merged_1_5_coin_def generator_def)
  qed
  have merge_coins: "merge_transitions merged_vends merged_1_5 1 1 1 1 1 coin 100 100 3 coinGeneral 2 generator modifier True = Some merged_1_5_coin"
    apply (simp add: merge_transitions_def easy_merge_1_5)
    apply (simp add: modifier_def)
    apply (simp add: nondeterministic_simulates_def nondeterministic_simulates_trace_merged_1_5_coin_merged_vends_0_0)
    by eval
  have arrives_5_merged_1_5_coin: "arrives 5 merged_1_5_coin = 4"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (5, (a, b), ba)) merged_1_5_coin = {|(5, (1, 4), vend_general)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_1_5_coin_def Set.filter_def)
      apply safe
      by (simp_all add: vend_general_def)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_6_merged_1_5_coin: "arrives 6 merged_1_5_coin = 6"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (6, (a, b), ba)) merged_1_5_coin = {|(6, (1, 6), vend_general)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_1_5_coin_def Set.filter_def)
      apply safe
      by (simp_all add: vend_general_def)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have merge_states_4_6_merged_1_5_coin: "merge_states 4 6 merged_1_5_coin = merged_4_6 \<and> merge_states 6 4 merged_1_5_coin = merged_4_6"
    by (simp add: merge_states_def merge_states_aux_def merged_1_5_coin_def merged_4_6_def)
  have leaves_5_merged_vends: "leaves 5 merged_vends = 3"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (5, (a, b), ba)) merged_vends = {|(5, (3, 4), vend_general)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_vends_def Set.filter_def)
      apply safe
      by (simp_all add: vend_general_def)
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have leaves_6_merged_vends: "leaves 6 merged_vends = 5"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (6, (a, b), ba)) merged_vends = {|(6, (5, 6), vend_general)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_vends_def Set.filter_def)
      apply safe
      by (simp_all add: vend_general_def)
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have leaves_5_merged_4_6: "leaves 5 merged_4_6 = 1 \<and> arrives 5 merged_4_6 = 4"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (5, (a, b), ba)) merged_4_6 = {|(5, (1, 4), vend_general)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_4_6_def Set.filter_def)
      apply safe
      by (simp_all add: vend_general_def)
    show ?thesis
      by (simp add: leaves_def arrives_def ffilter)
  qed
  have arrives_6_merged_4_6: "arrives 6 merged_4_6 = 4 \<and> leaves 6 merged_4_6 = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (6, (a, b), ba)) merged_4_6 = {|(6, (1, 4), vend_general)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_4_6_def Set.filter_def)
      apply safe
      by (simp_all add: vend_general_def)
    show ?thesis
      by (simp add: leaves_def arrives_def ffilter)
  qed
  have easy_merge_vends: "easy_merge merged_vends merged_4_6 5 3 1 4 4 vend_general 6 vend_general 5 generator = Some final"
  proof-
    have ffilter: "ffilter (\<lambda>x. snd x \<noteq> ((1, 4), vend_general)) merged_4_6 = {|(0, (0, 1), selectGeneral_2), (2, (1, 1), coinGeneral)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def merged_4_6_def)
      apply safe
      by (simp_all add: vend_general_def)
    show ?thesis
      apply (simp add: easy_merge_def generator_def directly_subsumes_vend_general_self)
      apply (simp add: replace_transition_def ffilter final_def)
      by auto
  qed
  have merge_vends_2: "merge_transitions merged_vends merged_4_6 5 3 1 4 4 vend_general 6 vend_general 5 generator modifier True = Some final"
    by (simp add: merge_transitions_def easy_merge_vends)
  show ?thesis
    apply (simp add: merge_def merge_states_1_2 nondeterminism_def nondeterministic_pairs_merged_1_2 sorted_list_of_fset_def)
    apply (simp add: arrives_2_merged_1_2 arrives_4_merged_1_2 merge_states_1_3 leaves_2_merged_vends)
    apply (simp add: leaves_2_merged_1_3 leaves_4_merged_vends arrives_4_merged_1_3 merge_vends)
    apply (simp add: nondeterminism_def nondeterministic_pairs_merged_1_3_coin)
    apply (simp add: nondeterministic_pairs_merged_1_2 sorted_list_of_fset_def)
    apply (simp add: arrives_2_merged_1_3_coin arrives_3_merged_1_3_coin merge_states_1_5)
    apply (simp add: leaves_2_merged_vends leaves_3_merged_vends leaves_2_merged_1_5 arrives_3_merged_1_5)
    apply (simp add: merge_coins nondeterminism_def nondeterministic_pairs_merged_1_5_coin sorted_list_of_fset_def)
    apply (simp add: arrives_5_merged_1_5_coin arrives_6_merged_1_5_coin merge_states_4_6_merged_1_5_coin)
    apply (simp add: leaves_5_merged_vends leaves_6_merged_vends leaves_5_merged_4_6 arrives_6_merged_4_6)
    by (simp add: merge_vends_2 nondeterminism_def nondeterministic_pairs_final)
qed

lemma score_final: "score final naive_score = {||}"
proof-
  have ffilter: "ffilter (\<lambda>(x, y). x < y) (Inference.S final |\<times>| Inference.S final) = {|(0, 1), (0, 4), (1, 4)|}"
    apply (simp add: S_def final_def fprod_def ffilter_def fset_both_sides Abs_fset_inverse)
    apply (simp add: Set.filter_def)
    by auto
  show ?thesis
    apply (simp add: score_def ffilter)
    apply (simp add: outgoing_transitions_def final_def fimage_def)
    apply (simp add: naive_score_empty)
    apply (simp add: naive_score_def selectGeneral_2_def coinGeneral_def vend_general_def fprod_def)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    by auto
qed

lemma "learn traces naive_score generator (heuristic_1 traces) = (tm final)"
  apply (simp add: learn_def build_pta scoring_1 merge_1_8)


(* value "iefsm2dot pta" *)
(* value "iefsm2dot merged_1_8" *)
(* value "iefsm2dot merged_1_7" *)
(* value "iefsm2dot merged_2_8" *)
(* value "iefsm2dot merged_2_8_coin50" *)
(* value "iefsm2dot merged_3_9" *)
(* value "iefsm2dot merged_3_9_coin100" *)
(* value "iefsm2dot_str merged_4_10" *)
(* value "iefsm2dot merged_vends" *)
(* value "iefsm2dot merged_1_2" *)
(* value "iefsm2dot merged_1_3" *)
(* value "iefsm2dot merged_1_3_coin" *)
(* value "iefsm2dot merged_1_5" *)
(* value "iefsm2dot merged_1_5_coin" *)
(* value "iefsm2dot final" *)
end