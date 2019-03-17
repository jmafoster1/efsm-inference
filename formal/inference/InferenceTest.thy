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

lemma merge_transitions_first_branch: "merge_transitions first_branch merge_3_1 (leaves 2 first_branch) (leaves 1 first_branch) (leaves 2 merge_3_1) (arrives 2 merge_3_1)
           (arrives 1 merge_3_1) (coin 50 100) 2 (coin 50 50) 1 (heuristics [first_trace]) = Some first_branch_initialise"
  apply (rule merge_transitions_heuristic)
   apply (simp add: coin_50_50_cant_directly_subsume_coin_50_100)
   apply (simp add: coin_50_100_cant_directly_subsume_coin_50_50)
  by eval

lemma merge_transitions_coin_general_coin_general: "merge_transitions first_branch first_branch_initialise (leaves 2 first_branch) (leaves 1 first_branch) (leaves 2 first_branch_initialise) 1
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
  have arrives_2_merge_1_2: "arrives 2 merge_1_2 = 3"
    by eval
  have arrives_1_merge_1_2: "arrives 1 merge_1_2 = 1"
    by eval
  have arrives_2_first_branch_initialise: "arrives 2 first_branch_initialise = 1"
    by eval
  have arrives_1_first_branch_initialise: "arrives 1 first_branch_initialise = 1"
    by eval
  show ?thesis
    apply (simp add: merge_def merge_1_2 nondeterministic_pairs_merge_1_2 sorted_list_of_fset_def)
    apply (simp add: arrives_2_merge_1_2 arrives_1_merge_1_2 merge_3_1)
    apply (simp add: merge_transitions_first_branch nondeterministic_pairs_first_branch_initialise sorted_list_of_fset_def)
    apply (simp add: arrives_2_first_branch_initialise arrives_1_first_branch_initialise merge_states_reflexive)
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

lemma merge_transitions_merge_7_5: "merge_transitions third_branch merge_7_5 (leaves 5 third_branch) (leaves 4 third_branch) (leaves 5 merge_7_5) (arrives 5 merge_7_5)
           (arrives 4 merge_7_5) (coin 50 100) 5 (coin 50 50) 4 (heuristics [third_trace, second_trace, first_trace]) = Some h_merge_7_5"
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

lemma merge_transitions_coins: "merge_transitions third_branch h_merge_7_5 (leaves 5 third_branch) (leaves 4 third_branch) (leaves 5 h_merge_7_5) (arrives 4 h_merge_7_5)
                (arrives 4 h_merge_7_5) (coin_general 2) 5 (coin_general 2) 4 (heuristics [third_trace, second_trace, first_trace]) = Some one_coin"
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
  have arrives_5_merge_5_6: "arrives 5 merge_5_6 = 7"
    by eval
  have arrives_4_merge_5_6: "arrives 4 merge_5_6 = 5"
    by eval
  have arrives_5_h_merge_7_5: "arrives 5 h_merge_7_5 = arrives 4 h_merge_7_5"
    by eval
  have satisfactory: "satisfies {third_trace, second_trace, first_trace} (tm one_coin)"
    by eval
  show ?thesis
    apply (simp add: merge_def merge_5_6 nondeterministic_pairs_merge_5_6 sorted_list_of_fset_def)
    apply (simp add: arrives_5_merge_5_6 arrives_4_merge_5_6 merge_7_5 merge_transitions_merge_7_5)
    apply (simp add: nondeterministic_pairs_h_merge_7_5 sorted_list_of_fset_def)
    apply (simp add: arrives_5_h_merge_7_5 merge_states_reflexive merge_transitions_coins nondeterministic_pairs_one_coin deterministic_def)
    by (simp add: satisfactory)
qed

lemma score_4: "sorted_list_of_fset (score one_coin naive_score) = [(2, 1, 5)]"
  by eval

lemma "iterative_learn traces naive_score heuristics = (tm final)"
  apply (simp add: iterative_learn_def)
  apply (rule tm_same)
  apply (simp add: traces_alt first_branch score_first_branch)
  apply (simp add: first_pass score_2 add_second_branch second_pass)
  apply (simp add: add_third_branch score_3 third_pass)
  apply (simp add: score_4)




end