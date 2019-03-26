theory InferenceTest
imports Trace_Matches Increment_Reset Code_Generation InferenceTestEFSMs
begin

definition "heuristics = iterative_try_heuristics [(\<lambda>x. insert_increment), (\<lambda>x. heuristic_1 x)]"

termination infer sorry
termination resolve_nondeterminism sorry

lemma tm_same: "x = y \<Longrightarrow> tm x = tm y"
  by simp

definition "first_trace = [((STR ''select''), [(Str ''coke'')], []), ((STR ''coin''), [Num 50], [Num 50]), ((STR ''coin''), [Num 50], [Num 100]), ((STR ''vend''), [], [(Str ''coke'')])]"
definition "second_trace = [((STR ''select''), [(Str ''coke'')], []), ((STR ''coin''), [Num 100], [Num 100]), ((STR ''vend''), [], [(Str ''coke'')])]"
definition "third_trace = [((STR ''select''), [(Str ''pepsi'')], []), ((STR ''coin''), [Num 50], [Num 50]), ((STR ''coin''), [Num 50], [Num 100]), ((STR ''vend''), [], [(Str ''pepsi'')])]"

lemma traces_alt: "traces = [first_trace, second_trace, third_trace]"
  by (simp add: first_trace_def second_trace_def third_trace_def traces_def)

lemma first_branch: "toiEFSM (make_branch (tm {||}) 0 Map.empty first_trace) = first_branch"
  by eval

lemma score_first_branch: "sorted_list_of_fset (score (first_branch) naive_score) = [(1, 1, 2)]"
  by eval

lemma merge_1_2: "merge_states 1 2 first_branch = merge_1_2"
  by eval

lemma nondeterministic_pairs: "ffUnion (fimage (\<lambda>s. state_nondeterminism s (outgoing_transitions s t)) (S t)) = sn \<Longrightarrow>
                                ffilter (\<lambda>(_, (d1, d2), t, t'). choice (fst t) (fst t')) sn = nd \<Longrightarrow>
                                nondeterministic_pairs t = nd"
  by (simp add: nondeterministic_pairs_def)

lemma nondeterministic_pairs_merge_1_2: "nondeterministic_pairs merge_1_2 = {|(1, (1, 3), (coin 50 50, 1), coin 50 100, 2), (1, (3, 1), (coin 50 100, 2), coin 50 50, 1)|}"
proof-
  have union: "ffUnion ((\<lambda>s. state_nondeterminism s (outgoing_transitions s merge_1_2)) |`| Inference.S merge_1_2) = {|(1, (1, 3), (coin 50 50, 1), coin 50 100, 2), (1, (3, 1), (coin 50 100, 2), coin 50 50, 1)|}"
    by eval
  show ?thesis
    apply (rule nondeterministic_pairs)
     apply (simp add: union)
    apply (simp add: Abs_ffilter Set.filter_def)
    using choice_def
    by auto
qed

lemma merge_3_1: "merge_states 3 1 merge_1_2 = merge_3_1"
  by eval

lemma merge_transitions_heuristic: "\<not> directly_subsumes (tm oldEFSM) (tm newEFSM) t1FromOld t2 t1 \<Longrightarrow>
       \<not> directly_subsumes (tm oldEFSM) (tm newEFSM) t2FromOld t1 t2 \<Longrightarrow>
       m u1 u2 newFrom newEFSM oldEFSM = Some e \<Longrightarrow>
       merge_transitions oldEFSM newEFSM t1FromOld t2FromOld newFrom t1NewTo t2NewTo t1 u1 t2 u2 m = Some e"
  by (simp add: merge_transitions_def)

lemma merge_transitions_coin_50: "merge_transitions first_branch merge_3_1 2 1 1 1 1 (coin 50 100) 2 (coin 50 50) 1 (heuristics [first_trace]) = Some first_branch_initialise"
  apply (rule merge_transitions_heuristic)
  using coin_50_50_cant_directly_subsume_coin_50_100 apply blast
  using coin_50_100_cant_directly_subsume_coin_50_50 apply blast
  by eval

lemma Abs_fset_both_sides: "finite s \<Longrightarrow> (fset f = s) = (f = Abs_fset s)"
  apply standard
  using fset_inverse apply fastforce
  by (simp add: Abs_fset_inverse)

lemma nondeterministic_pairs_first_branch_initialise: "nondeterministic_pairs first_branch_initialise = {|
(1, (1, 1), (coin_general 1, 1), coin_general 1, 2),
(1, (1, 1), (coin_general 1, 2), coin_general 1, 1)
|}"
proof-
  have state_nondeterminism: "ffUnion ((\<lambda>s. state_nondeterminism s (outgoing_transitions s first_branch_initialise)) |`| Inference.S first_branch_initialise) = {|
    (1, (1, 1), (coin_general 1, 1), coin_general 1, 2),
    (1, (1, 4), (coin_general 1, 1), vend coke, 3),
    (1, (1, 1), (coin_general 1, 2), coin_general 1, 1),
    (1, (1, 4), (coin_general 1, 2), vend coke, 3),
    (1, (4, 1), (vend coke, 3), coin_general 1, 1),
    (1, (4, 1), (vend coke, 3), coin_general 1, 2)
    |}"
    by eval
  show ?thesis
    apply (rule nondeterministic_pairs)
     apply (simp only: state_nondeterminism)
    apply (simp add: Abs_ffilter fset Set.filter_def)
    using choice_def by auto
qed

lemma merge_transitions_first_branch: "merge_transitions first_branch merge_3_1 (origin 2 first_branch) (origin 1 first_branch) (origin 2 merge_3_1) (dest 2 merge_3_1)
           (dest 1 merge_3_1) (coin 50 100) 2 (coin 50 50) 1 (heuristics [first_trace]) = Some first_branch_initialise"
  apply (rule merge_transitions_heuristic)
   apply (simp add: coin_50_50_cant_directly_subsume_coin_50_100)
   apply (simp add: coin_50_100_cant_directly_subsume_coin_50_50)
  by eval

lemma merge_transitions_coin_general_coin_general: "merge_transitions first_branch first_branch_initialise (origin 2 first_branch) (origin 1 first_branch) (origin 2 first_branch_initialise) 1
                1 (coin_general 1) 2 (coin_general 1) 1 (heuristics [first_trace]) = Some completed_first_branch"
  apply (simp add: merge_transitions_def directly_subsumes_self)
  by eval

lemma nondeterministic_pairs_completed_first_branch: "nondeterministic_pairs completed_first_branch = {||}"
proof-
  have union: "ffUnion ((\<lambda>s. state_nondeterminism s (outgoing_transitions s completed_first_branch)) |`| Inference.S completed_first_branch) =
                {|(1, (4, 1), (vend coke, 3), coin_general 1, 2), (1, (1, 4), (coin_general 1, 2), vend coke, 3)|}"
    by eval
  show ?thesis
    apply (rule nondeterministic_pairs)
     apply (simp add: union)
    apply (simp add: Abs_ffilter Set.filter_def)
    using choice_def by auto
qed

lemma completed_first_branch_satisfactory: "satisfies {first_trace} (tm completed_first_branch)"
  by eval

lemma first_pass: "merge first_branch 1 2 (heuristics [first_trace]) (satisfies {first_trace}) = Some completed_first_branch"
proof-
  have dest_2_merge_1_2: "dest 2 merge_1_2 = 3"
    by eval
  have dest_1_merge_1_2: "dest 1 merge_1_2 = 1"
    by eval
  have dest_2_first_branch_initialise: "dest 2 first_branch_initialise = 1"
    by eval
  have dest_1_first_branch_initialise: "dest 1 first_branch_initialise = 1"
    by eval
  show ?thesis
    apply (simp add: merge_def merge_1_2 nondeterministic_pairs_merge_1_2 sorted_list_of_fset_def)
    apply (simp add: dest_2_merge_1_2 dest_1_merge_1_2 merge_3_1)
    apply (simp add: merge_transitions_first_branch nondeterministic_pairs_first_branch_initialise sorted_list_of_fset_def)
    apply (simp add: dest_2_first_branch_initialise dest_1_first_branch_initialise merge_states_reflexive)
    apply (simp add: merge_transitions_coin_general_coin_general nondeterministic_pairs_completed_first_branch deterministic_def)
    by (simp add: completed_first_branch_satisfactory)
qed

lemma score_2:  "sorted_list_of_fset (score completed_first_branch naive_score) = []"
  by eval

lemma add_second_branch: "make_branch (tm completed_first_branch) 0 Map.empty second_trace = (tm completed_first_branch)"
  by eval

lemma second_pass: "inference_step (toiEFSM (tm completed_first_branch))
                          (rev (sorted_list_of_fset (score (toiEFSM (tm completed_first_branch)) naive_score))) (heuristics [second_trace, first_trace])
                          (satisfies {second_trace, first_trace}) = None"
  by eval

lemma add_third_branch: "toiEFSM (make_branch (tm (toiEFSM (tm completed_first_branch))) 0 Map.empty third_trace) = third_branch"
  by eval

lemma score_3: "sorted_list_of_fset (score third_branch naive_score) = [(1, 1, 5), (1, 1, 6), (1, 1, 7), (1, 5, 6)]"
  by eval

lemma merge_5_6: "merge_states 5 6 third_branch = merge_5_6"
  by eval

lemma no_select_choice: "\<not>choice (select pepsi) (select_initialise coke 1)"
  by (simp add: choice_def)

lemma nondeterministic_pairs_merge_5_6: "nondeterministic_pairs merge_5_6 = {|
(5, (5, 7), (coin 50 50, 4), coin 50 100, 5),
(5, (7, 5), (coin 50 100, 5), coin 50 50, 4)
|}"
proof-
  have union: "ffUnion ((\<lambda>s. state_nondeterminism s (outgoing_transitions s merge_5_6)) |`| Inference.S merge_5_6) = {|
(5, (5, 7), (coin 50 50, 4), coin 50 100, 5), (5, (7, 5), (coin 50 100, 5), coin 50 50, 4), (1, (1, 4), (coin_general 1, 2), vend coke, 3),
   (1, (4, 1), (vend coke, 3), coin_general 1, 2), (0, (1, 5), (select_initialise coke 1, 0), select pepsi, 1),
   (0, (5, 1), (select pepsi, 1), select_initialise coke 1, 0)|}"
    by eval
  show ?thesis
    apply (rule nondeterministic_pairs)
     apply (simp add: union)
    apply (simp add: Abs_ffilter Set.filter_def)
    apply standard
     apply clarify
     apply simp
     apply (case_tac "ab = coin 50 50")
      apply simp
    apply (case_tac "ab = coin 50 100")
      apply simp
     apply simp
    using no_select_choice choice_def
    by auto
qed

lemma merge_7_5: "merge_states 7 5 merge_5_6 = merge_7_5"
  by eval

lemma merge_transitions_merge_7_5: "merge_transitions third_branch merge_7_5 (origin 5 third_branch) (origin 4 third_branch) (origin 5 merge_7_5) (dest 5 merge_7_5)
           (dest 4 merge_7_5) (coin 50 100) 5 (coin 50 50) 4 (heuristics [third_trace, second_trace, first_trace]) = Some h_merge_7_5"
  apply (rule merge_transitions_heuristic)
    apply (simp add: coin_50_50_cant_directly_subsume_coin_50_100)
   apply (simp add: coin_50_100_cant_directly_subsume_coin_50_50)
  by eval

lemma no_drink_choice: "d \<noteq> d' \<Longrightarrow> \<not>choice (select_initialise d m) (select_initialise d' n)"
  by (simp add: choice_def)

lemma nondeterministic_pairs_h_merge_7_5: "nondeterministic_pairs h_merge_7_5 = {|
(5, (5, 5), (coin_general 2, 4), coin_general 2, 5),
(5, (5, 5), (coin_general 2, 5), coin_general 2, 4)
|}"
proof-
  have union:  "ffUnion ((\<lambda>s. state_nondeterminism s (outgoing_transitions s h_merge_7_5)) |`| Inference.S h_merge_7_5) = {|
                  (5, (5, 5), (coin_general 2, 4), coin_general 2, 5), (5, (5, 8), (coin_general 2, 4), vend pepsi, 6),
                  (5, (5, 5), (coin_general 2, 5), coin_general 2, 4), (5, (5, 8), (coin_general 2, 5), vend pepsi, 6), (5, (8, 5), (vend pepsi, 6), coin_general 2, 4),
                  (5, (8, 5), (vend pepsi, 6), coin_general 2, 5), (1, (1, 4), (coin_general 1, 2), vend coke, 3), (1, (4, 1), (vend coke, 3), coin_general 1, 2),
                  (0, (1, 5), (select_initialise coke 1, 0), select_initialise pepsi 2, 1), (0, (5, 1), (select_initialise pepsi 2, 1), select_initialise coke 1, 0)
                |}"
    by eval
  show ?thesis
    apply (rule nondeterministic_pairs)
     apply (simp add: union)
    apply (simp add: Abs_ffilter Set.filter_def)
    apply standard
     apply clarify
     apply simp
     apply (case_tac "ab = select_initialise coke 1")
      apply (simp add: no_drink_choice)
    apply (case_tac "ac = select_initialise coke 1")
      apply (simp add: no_drink_choice)
    apply (case_tac "ab = vend coke")
      apply (simp add: choice_def)
     apply (case_tac "ab = vend pepsi")
    using choice_def apply auto[1]
    apply (case_tac "ac = vend coke")
    using choice_def apply auto[1]
     apply (case_tac "ac = vend pepsi")
    using choice_def by auto
qed

lemma direct_subsumption_merge_1: "directly_subsumes (tm oldEFSM) (tm newEFSM) t1FromOld t2 t1 \<Longrightarrow>
                                    replace_transition newEFSM u1 newFrom t2NewTo t1 t2 = e \<Longrightarrow>
                                    merge_transitions oldEFSM newEFSM t1FromOld t2FromOld newFrom t1NewTo t2NewTo t1 u1 t2 u2 modifier = Some e"
  by (simp add: merge_transitions_def)

lemma merge_transitions_coins: "merge_transitions third_branch h_merge_7_5 (origin 5 third_branch) (origin 4 third_branch) (origin 5 h_merge_7_5) (dest 4 h_merge_7_5)
                (dest 4 h_merge_7_5) (coin_general 2) 5 (coin_general 2) 4 (heuristics [third_trace, second_trace, first_trace]) = Some one_coin"
  apply (simp add: merge_transitions_def directly_subsumes_self)
  by eval

lemma nondeterministic_pairs_one_coin: "nondeterministic_pairs one_coin = {||}"
proof-
  have union: "ffUnion ((\<lambda>s. state_nondeterminism s (outgoing_transitions s one_coin)) |`| Inference.S one_coin) = {|
(5, (5, 8), (coin_general 2, 5), vend pepsi, 6), (5, (8, 5), (vend pepsi, 6), coin_general 2, 5), (1, (1, 4), (coin_general 1, 2), vend coke, 3),
   (1, (4, 1), (vend coke, 3), coin_general 1, 2), (0, (1, 5), (select_initialise coke 1, 0), select_initialise pepsi 2, 1),
   (0, (5, 1), (select_initialise pepsi 2, 1), select_initialise coke 1, 0)|}"
    by eval
  show ?thesis
    apply (rule nondeterministic_pairs)
     apply (simp add: union)
    apply (simp add: Abs_ffilter Set.filter_def)
    apply standard
    apply clarify
    apply simp
    apply (case_tac "ab = select_initialise coke 1")
     apply (simp add: no_drink_choice)
    apply (case_tac "ab = select_initialise pepsi 2")
     apply (simp add: no_drink_choice)
    apply (case_tac "ab = vend coke")
     apply (simp add: choice_def)
    apply (case_tac "ab = coin_general 2")
     apply (simp add: choice_def)
    apply (case_tac "ab = vend pepsi")
     apply (simp add: choice_def)
    by (simp add: choice_def)
qed

lemma third_pass: "merge third_branch 5 6 (heuristics [third_trace, second_trace, first_trace]) (satisfies {third_trace, second_trace, first_trace}) = Some one_coin"
proof-
  have dest_5_merge_5_6: "dest 5 merge_5_6 = 7"
    by eval
  have dest_4_merge_5_6: "dest 4 merge_5_6 = 5"
    by eval
  have dest_5_h_merge_7_5: "dest 5 h_merge_7_5 = dest 4 h_merge_7_5"
    by eval
  have satisfactory: "satisfies {third_trace, second_trace, first_trace} (tm one_coin)"
    by eval
  show ?thesis
    apply (simp add: merge_def merge_5_6 nondeterministic_pairs_merge_5_6 sorted_list_of_fset_def)
    apply (simp add: dest_5_merge_5_6 dest_4_merge_5_6 merge_7_5 merge_transitions_merge_7_5)
    apply (simp add: nondeterministic_pairs_h_merge_7_5 sorted_list_of_fset_def)
    apply (simp add: dest_5_h_merge_7_5 merge_states_reflexive merge_transitions_coins nondeterministic_pairs_one_coin deterministic_def)
    by (simp add: satisfactory)
qed

lemma score_4: "sorted_list_of_fset (score one_coin naive_score) = [(2, 1, 5)]"
  by eval

lemma merge_1_5: "merge_states 1 5 one_coin = merge_1_5"
  by eval

lemma nondeterministic_pairs_merge_1_5: "nondeterministic_pairs merge_1_5 = {|
(1, (1, 1), (coin_general 1, 2), coin_general 2, 5),
(1, (4, 8), (vend coke, 3), vend pepsi, 6),
(1, (1, 1), (coin_general 2, 5), coin_general 1, 2),
(1, (8, 4), (vend pepsi, 6), vend coke, 3)
|}"
proof-
  have union: "ffUnion ((\<lambda>s. state_nondeterminism s (outgoing_transitions s merge_1_5)) |`| Inference.S merge_1_5) = {|
(1, (1, 4), (coin_general 1, 2), vend coke, 3), (1, (1, 1), (coin_general 1, 2), coin_general 2, 5), (1, (1, 8), (coin_general 1, 2), vend pepsi, 6),
   (1, (4, 1), (vend coke, 3), coin_general 1, 2), (1, (4, 1), (vend coke, 3), coin_general 2, 5), (1, (4, 8), (vend coke, 3), vend pepsi, 6),
   (1, (1, 1), (coin_general 2, 5), coin_general 1, 2), (1, (1, 4), (coin_general 2, 5), vend coke, 3), (1, (1, 8), (coin_general 2, 5), vend pepsi, 6),
   (1, (8, 1), (vend pepsi, 6), coin_general 1, 2), (1, (8, 4), (vend pepsi, 6), vend coke, 3), (1, (8, 1), (vend pepsi, 6), coin_general 2, 5),
   (0, (1, 1), (select_initialise coke 1, 0), select_initialise pepsi 2, 1), (0, (1, 1), (select_initialise pepsi 2, 1), select_initialise coke 1, 0)
|}"
by eval
  show ?thesis
    apply (rule nondeterministic_pairs)
     apply (simp add: union)
    apply (simp add: Abs_ffilter Set.filter_def)
    apply standard
     apply clarify
     apply simp
     apply (case_tac "ab = coin_general 1")
    using choice_def apply auto[1]
     apply (case_tac "ab = coin_general 2")
    using choice_def apply auto[1]
    apply (case_tac "ab = select_initialise coke 1")
      apply (simp add: no_drink_choice)
     apply (case_tac "ab = select_initialise pepsi 2")
      apply (simp add: no_drink_choice)
     apply (case_tac "ac = coin_general 1")
    using choice_def apply auto[1]
     apply (case_tac "ac = coin_general 2")
    using choice_def by auto
qed

lemma merge_transitions_select_vend_merge_8_4: "merge_transitions one_coin merge_8_4 (origin 6 one_coin) (origin 3 one_coin) (origin 6 merge_8_4) (dest 6 merge_8_4) (dest 3 merge_8_4)
           (vend pepsi) 6 (vend coke) 3 (heuristics [third_trace, second_trace, first_trace]) = Some h_merge_8_4"
  apply (rule merge_transitions_heuristic)
    apply (simp add: cant_directly_subsume no_subsumption_vend_coke_vend_pepsi)
  apply (simp add: cant_directly_subsume vend_pepsi_not_subsumes_vend_coke)
  by eval

lemma nondeterministic_pairs_h_merge_8_4: "(nondeterministic_pairs h_merge_8_4) = {|
  (1, (1, 1), (coin_general 1, 2), coin_general 2, 3),
  (1, (1, 1), (coin_general 2, 3), coin_general 1, 2),
  (1, (4, 4), (vend pepsi, 4), general_vend 3, 5),
  (1, (4, 4), (general_vend 3, 5), vend pepsi, 4),
  (0, (1, 1), (select_general_initialise, 0), select_initialise pepsi 2, 1),
  (0, (1, 1), (select_initialise pepsi 2, 1), select_general_initialise, 0)|}"
proof-
  have union: "ffUnion ((\<lambda>s. state_nondeterminism s (outgoing_transitions s h_merge_8_4)) |`| Inference.S h_merge_8_4) = {|
(1, (1, 1), (coin_general 1, 2), coin_general 2, 3), (1, (1, 4), (coin_general 1, 2), vend pepsi, 4),
(1, (1, 4), (coin_general 1, 2), general_vend 3, 5), (1, (1, 1), (coin_general 2, 3), coin_general 1, 2),
(1, (1, 4), (coin_general 2, 3), vend pepsi, 4), (1, (1, 4), (coin_general 2, 3), general_vend 3, 5), (1, (4, 1), (vend pepsi, 4), coin_general 1, 2),
(1, (4, 1), (vend pepsi, 4), coin_general 2, 3), (1, (4, 4), (vend pepsi, 4), general_vend 3, 5), (1, (4, 1), (general_vend 3, 5), coin_general 1, 2),
(1, (4, 1), (general_vend 3, 5), coin_general 2, 3), (1, (4, 4), (general_vend 3, 5), vend pepsi, 4),
(0, (1, 1), (select_general_initialise, 0), select_initialise pepsi 2, 1), (0, (1, 1), (select_initialise pepsi 2, 1), select_general_initialise, 0)
|}"
    by eval
  show ?thesis
     apply (rule nondeterministic_pairs)
      apply (simp add: union)
    apply (simp add: Abs_ffilter Set.filter_def)
    apply standard
     apply clarify
     apply simp
     apply (case_tac "ab = coin_general 1")
    using choice_def apply auto[1]
     apply (case_tac "ab = coin_general 2")
    using choice_def apply auto[1]
     apply (case_tac "ab = vend pepsi")
    using choice_def apply auto[1]
     apply (case_tac "ab = vend pepsi")
      apply simp
     apply (case_tac "ab = general_vend 3")
    using choice_def by auto
qed

lemma "\<not> directly_subsumes (tm one_coin) (tm h_merge_8_4) 5 (vend pepsi) (general_vend 3)"
proof-
  have step: "step (tm one_coin) 0 Map.empty STR ''select'' [EFSM.Str ''pepsi''] = Some (select_initialise pepsi 2, 5, [], <R 2 := Num 0>)"
    apply (rule one_possible_step)
      apply (simp add: possible_steps_alt Abs_ffilter Set.filter_def tm_def one_coin_def)
      apply standard
       apply clarify
       apply (simp add: implode_pepsi)
       apply fastforce
      apply (simp add: implode_pepsi)
     apply simp
    apply (rule ext)
    by simp
  have other_step: "step (tm h_merge_8_4) 0 Map.empty STR ''select'' [EFSM.Str ''pepsi''] = None"
    by eval
  show ?thesis
  apply (rule gets_us_to_and_not_subsumes)
  apply (rule_tac x="[(STR ''select'', [Str ''pepsi''])]" in exI)
  apply standard
   apply (simp add: accepts_trace_def)
     apply (rule accepts.step)
      apply (simp add: step)
     apply (simp add: accepts.base)
    apply standard
     apply (rule gets_us_to.step_some)
      apply (simp add: step)
     apply (simp add: gets_us_to.base)
    apply (simp add: anterior_context_def)

lemma "merge_transitions one_coin h_merge_8_4 (origin 5 one_coin) (origin 4 one_coin) (origin 5 h_merge_8_4) (dest 4 h_merge_8_4)
                (dest 4 h_merge_8_4) (general_vend 3) 5 (vend pepsi) 4 (heuristics [third_trace, second_trace, first_trace]) = Some e"
proof-
  have origin_5: "origin 5 one_coin = 5"
    by eval
  show ?thesis
    apply (simp only: origin_5)
    apply (rule merge_transitions_heuristic)



lemma "merge one_coin 1 5 (heuristics [third_trace, second_trace, first_trace]) (satisfies {third_trace, second_trace, first_trace}) = Some e"
proof-
  have sorted_list: "sorted_list_of_fset (nondeterministic_pairs merge_1_5) = [(1, (1, 1), (coin_general 1, 2), coin_general 2, 5), (1, (1, 1), (coin_general 2, 5), coin_general 1, 2), (1, (4, 8), (vend coke, 3), vend pepsi, 6),
  (1, (8, 4), (vend pepsi, 6), vend coke, 3)]"
    apply (simp add: nondeterministic_pairs_merge_1_5)
    by eval
  have dest_6_merge_1_5: "dest 6 merge_1_5 = 8"
    by eval
  have dest_3_merge_1_5: "dest 3 merge_1_5 = 4"
    by eval
  have merge_8_4: "merge_states 8 4 merge_1_5 = merge_8_4"
    by eval
  have sorted_list_2: "sorted_list_of_fset (nondeterministic_pairs h_merge_8_4) = 
[(0, (1, 1), (select_general_initialise, 0), select_initialise pepsi 2, 1),
 (0, (1, 1), (select_initialise pepsi 2, 1), select_general_initialise, 0),
  (1, (1, 1), (coin_general 1, 2), coin_general 2, 3), (1, (1, 1), (coin_general 2, 3), coin_general 1, 2),
  (1, (4, 4), (vend pepsi, 4), general_vend 3, 5), (1, (4, 4), (general_vend 3, 5), vend pepsi, 4)]"
    apply (simp add: nondeterministic_pairs_h_merge_8_4)
    by eval
  have dest_5_eq_dest_4: "dest 5 h_merge_8_4 = dest 4 h_merge_8_4"
    by eval
  show ?thesis
    apply (simp add: merge_def)
    apply (simp add: merge_1_5 sorted_list)
    apply (simp add: dest_6_merge_1_5 dest_3_merge_1_5)
    apply (simp add: merge_8_4)
    apply (simp add: merge_transitions_select_vend_merge_8_4)
    apply (simp add: sorted_list_2 dest_5_eq_dest_4 merge_states_reflexive)



lemma "iterative_learn traces naive_score heuristics = (tm final)"
  apply (simp add: iterative_learn_def)
  apply (rule tm_same)
  apply (simp add: traces_alt first_branch score_first_branch)
  apply (simp add: first_pass score_2 add_second_branch second_pass)
  apply (simp add: add_third_branch score_3 third_pass)
  apply (simp add: score_4)




end