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

lemma nondeterministic_pairs_first_branch_initialise: "nondeterministic_pairs first_branch_initialise = {||}"
proof-
  have state_nondeterminism: "ffUnion ((\<lambda>s. state_nondeterminism s (outgoing_transitions s first_branch_initialise)) |`| Inference.S first_branch_initialise) =
    {|(1, (1, 4), (coin_general 1, 2), vend coke, 3), (1, (4, 1), (vend coke, 3), coin_general 1, 2)|}"
    by eval
  show ?thesis
    apply (rule nondeterministic_pairs)
     apply (simp only: state_nondeterminism)
    apply (simp add: Abs_ffilter fset Set.filter_def)
    using choice_def by auto
qed

lemma merge_first_branch_1_2: "merge first_branch 1 2 (heuristics [first_trace]) (satisfies {first_trace}) = Some first_branch_initialise"
proof-
  have arrives_2_merge_1_2: "arrives 2 merge_1_2 = 3"
    by eval
  have arrives_1_merge_1_2: "arrives 1 merge_1_2 = 1"
    by eval
  have leaves_2_first_branch: "leaves 2 first_branch = 2"
    by eval
  have leaves_1_first_branch: "leaves 1 first_branch = 1"
    by eval
  have leaves_2_merge_3_1: "leaves 2 merge_3_1 = 1"
    by eval
  have arrives_2_merge_3_1: "arrives 2 merge_3_1 = 1"
    by eval
  have arrives_1_merge_3_1: "arrives 1 merge_3_1 = 1"
    by eval
  have first_branch_initialise_ok: "satisfies {first_trace} (tm first_branch_initialise)"
    by eval
  show ?thesis
    apply (simp add: merge_def merge_1_2 nondeterministic_pairs_merge_1_2 sorted_list_of_fset_def)
    apply (simp add:arrives_2_merge_1_2 arrives_1_merge_1_2 merge_3_1)
    apply (simp add:leaves_2_first_branch leaves_1_first_branch leaves_2_merge_3_1 arrives_2_merge_3_1 arrives_1_merge_3_1)
    apply (simp add: merge_transitions_coin_50)
    apply (simp add: deterministic_def nondeterministic_pairs_first_branch_initialise)
    by (simp add:first_branch_initialise_ok)
qed

lemma score_first_branch_initialise: "score first_branch_initialise naive_score = {||}"
  by eval

lemma second_branch: "toiEFSM (make_branch (tm first_branch_initialise) 0 Map.empty second_trace) = second_branch"
  by eval

lemma score_second_branch: "score second_branch naive_score = {||}"
  by eval

lemma third_branch: "toiEFSM (make_branch (tm second_branch) 0 Map.empty third_trace) = third_branch"
  by eval

lemma score_third_branch: "sorted_list_of_fset (score third_branch naive_score) = [(1, 1, 5), (1, 1, 6), (1, 1, 7), (1, 5, 6)]"
  by eval

lemma merge_5_6: "merge_states 5 6 third_branch = merge_5_6"
  by eval

lemma nondeterministic_pairs_merge_5_6: "(nondeterministic_pairs merge_5_6) = {|
(5, (5, 7), (coin 50 50, 4), coin 50 100, 5),
(5, (7, 5), (coin 50 100, 5), coin 50 50, 4)
|}"
proof-
  have union: "ffUnion ((\<lambda>s. state_nondeterminism s (outgoing_transitions s merge_5_6)) |`| Inference.S merge_5_6) = {|(5, (5, 7), (coin 50 50, 4), coin 50 100, 5), (5, (7, 5), (coin 50 100, 5), coin 50 50, 4), (1, (1, 4), (coin_general 1, 2), vend coke, 3),
   (1, (4, 1), (vend coke, 3), coin_general 1, 2), (0, (1, 5), (select_initialise coke 1, 0), select pepsi, 1),
   (0, (5, 1), (select pepsi, 1), select_initialise coke 1, 0)|}"
    by eval
  have no_choice: "\<not>choice (select_initialise coke 1) (select pepsi)"
    by (simp add: choice_def)
  show ?thesis
  apply (rule nondeterministic_pairs)
     apply (simp only: union)
    apply (simp add: Abs_ffilter Set.filter_def)
    apply standard
     apply clarify
     apply simp
     apply (case_tac "ab = coin 50 50")
      apply simp
     apply simp
     apply (case_tac "ab = coin 50 100")
      apply simp
     apply simp
     apply (case_tac "ab = coin_general 1")
      apply (simp add: choice_def)
     apply simp
     apply (case_tac "ab = vend coke")
      apply (simp add: choice_def)
     apply simp
     apply (case_tac "ab = select_initialise coke 1")
      apply (simp add: no_choice)
     apply (simp add: no_choice choice_symmetry)
    using choice_def by auto
qed

lemma merge_7_5: "merge_states 7 5 merge_5_6 = merge_7_5"
  by eval

lemma merge_transitions_7_5: "merge_transitions third_branch merge_7_5 6 5 5 5 5 (coin 50 100) 5 (coin 50 50) 4 (heuristics [third_trace, second_trace, first_trace]) = Some heuristics_7_5"
  apply (rule merge_transitions_heuristic)
  using coin_50_50_cant_directly_subsume_coin_50_100 apply blast
  using coin_50_100_cant_directly_subsume_coin_50_50 apply blast
  by eval

lemma no_choice: "\<forall> n m. \<not>choice (select_initialise coke n) (select_initialise pepsi m)"
  by (simp add: choice_def)

lemma nondeterministic_pairs_heuristics_7_5: "nondeterministic_pairs heuristics_7_5 = {||}"
proof-
  have union: "ffUnion ((\<lambda>s. state_nondeterminism s (outgoing_transitions s heuristics_7_5)) |`| Inference.S heuristics_7_5) = {|
(5, (5, 8), (coin_general 2, 5), vend pepsi, 6), (5, (8, 5), (vend pepsi, 6), coin_general 2, 5), (1, (1, 4), (coin_general 1, 2), vend coke, 3),
   (1, (4, 1), (vend coke, 3), coin_general 1, 2), (0, (1, 5), (select_initialise coke 1, 0), select_initialise pepsi 2, 1),
   (0, (5, 1), (select_initialise pepsi 2, 1), select_initialise coke 1, 0)|}"
    by eval
  show ?thesis
    apply (rule nondeterministic_pairs)
     apply (simp only: union)
    apply (simp add: Abs_ffilter Set.filter_def)
    apply clarify
    apply (case_tac "ab = select_initialise coke 1")
     apply (simp add: no_choice)
    apply (case_tac "ab = select_initialise pepsi 2")
     apply (simp add: no_choice choice_symmetry)
    using choice_def by auto
qed

lemma merge_third_branch: "merge third_branch 5 6 (heuristics [third_trace, second_trace, first_trace]) (satisfies {third_trace, second_trace, first_trace}) = Some heuristics_7_5"
proof-
  have arrives_5_merge_5_6: "arrives 5 merge_5_6 = 7"
    by eval
  have arrives_4_merge_5_6: "arrives 4 merge_5_6 = 5"
    by eval
  have leaves_5_third_branch: "leaves 5 third_branch = 6"
    by eval
  have leaves_4_third_branch: "leaves 4 third_branch = 5"
    by eval
  have leaves_5_merge_7_5: "leaves 5 merge_7_5 = 5"
    by eval
  have arrives_5_merge_7_5: "arrives 5 merge_7_5 = 5"
    by eval
  have arrives_4_merge_7_5: "arrives 4 merge_7_5 = 5"
    by eval
  have satisfies: "satisfies {third_trace, second_trace, first_trace} (tm heuristics_7_5)"
    by eval
  show ?thesis
    apply (simp add: merge_def merge_5_6 nondeterministic_pairs_merge_5_6 sorted_list_of_fset_def)
    apply (simp add: arrives_5_merge_5_6 arrives_4_merge_5_6 merge_7_5)
    apply (simp add: leaves_5_third_branch leaves_4_third_branch leaves_5_merge_7_5 arrives_5_merge_7_5 arrives_4_merge_7_5)
    apply (simp add: merge_transitions_7_5 nondeterministic_pairs_heuristics_7_5 deterministic_def)
    by (simp add: satisfies)
qed

lemma score_heuristics_7_5: "sorted_list_of_fset (score heuristics_7_5 naive_score) = [(2, 1, 5)]"
  by eval

lemma merge_1_5: "merge_states 1 5 heuristics_7_5 = merge_1_5"
  by eval

lemma nondeterministic_pairs_merge_1_5: "nondeterministic_pairs merge_1_5 = {|
(1, (1, 1), (coin_general 1, 2), coin_general 2, 5),
(1, (4, 8), (vend coke, 3), vend pepsi, 6),
(1, (1, 1), (coin_general 2, 5), coin_general 1, 2),
(1, (8, 4), (vend pepsi, 6), vend coke, 3)
|}"
proof-
  have union: "ffUnion ((\<lambda>s. state_nondeterminism s (outgoing_transitions s merge_1_5)) |`| Inference.S merge_1_5) = {|(1, (1, 4), (coin_general 1, 2), vend coke, 3), (1, (1, 1), (coin_general 1, 2), coin_general 2, 5), (1, (1, 8), (coin_general 1, 2), vend pepsi, 6),
   (1, (4, 1), (vend coke, 3), coin_general 1, 2), (1, (4, 1), (vend coke, 3), coin_general 2, 5), (1, (4, 8), (vend coke, 3), vend pepsi, 6),
   (1, (1, 1), (coin_general 2, 5), coin_general 1, 2), (1, (1, 4), (coin_general 2, 5), vend coke, 3), (1, (1, 8), (coin_general 2, 5), vend pepsi, 6),
   (1, (8, 1), (vend pepsi, 6), coin_general 1, 2), (1, (8, 4), (vend pepsi, 6), vend coke, 3), (1, (8, 1), (vend pepsi, 6), coin_general 2, 5),
   (0, (1, 1), (select_initialise coke 1, 0), select_initialise pepsi 2, 1), (0, (1, 1), (select_initialise pepsi 2, 1), select_initialise coke 1, 0)|}"
    by eval
  show ?thesis
    apply (rule nondeterministic_pairs)
     apply (simp only: union)
    apply (simp add: Abs_ffilter Set.filter_def)
    apply standard
     apply clarify
     apply simp
     apply (case_tac "ab = select_initialise coke 1")
     apply (simp add: no_choice)
    apply (case_tac "ab = select_initialise pepsi 2")
     apply (simp add: no_choice choice_symmetry)
     apply simp
     apply (case_tac "ab = vend coke")
      apply (case_tac "ac = vend pepsi")
       apply simp
    using choice_def apply auto[1]
     apply simp
     apply (case_tac "ab = vend pepsi")
     apply (case_tac "ac = vend coke")
       apply simp
    using choice_def apply auto[1]
     apply simp
     apply (case_tac "ac = vend coke")
      apply (case_tac "ab = vend pepsi")
       apply simp
    using choice_def apply auto[1]

     apply (case_tac "ac = vend pepsi")
      apply (case_tac "ab = vend coke")
       apply simp
    using choice_def apply auto[1]
     apply auto[1]
    apply (simp add: choice_def)
    by auto
qed

lemma merge_ar6_ar3: "merge_states (arrives 6 merge_1_5) (arrives 3 merge_1_5) merge_1_5 = merge_ar6_ar3"
  by eval

lemma merge_transitions_heuristics_7_5: "merge_transitions heuristics_7_5 merge_ar6_ar3 5 1 1 4 4 (vend pepsi) 6 (vend coke) 3 (heuristics [third_trace, second_trace, first_trace]) = Some heuristics_1_0"
  apply (rule merge_transitions_heuristic)
    apply (simp add: cant_directly_subsume no_subsumption_vend_coke_vend_pepsi)
   apply (simp add: cant_directly_subsume vend_pepsi_not_subsumes_vend_coke)
  by eval

lemma nondeterministic_pairs_heuristics_1_0: "nondeterministic_pairs heuristics_1_0 = {|
(0, (1, 5), (select_general_1, 0), select_initialise pepsi 2, 1),
(0, (5, 1), (select_initialise pepsi 2, 1), select_general_1, 0)
|}"
proof-
  have union: "ffUnion ((\<lambda>s. state_nondeterminism s (outgoing_transitions s heuristics_1_0)) |`| Inference.S heuristics_1_0) = {|
(5, (5, 8), (coin_general 2, 4), vend pepsi, 5), (5, (8, 5), (vend pepsi, 5), coin_general 2, 4), (1, (1, 4), (coin_general 1, 2), vend_general_1, 3),
   (1, (4, 1), (vend_general_1, 3), coin_general 1, 2), (0, (1, 5), (select_general_1, 0), select_initialise pepsi 2, 1),
   (0, (5, 1), (select_initialise pepsi 2, 1), select_general_1, 0)|}"
    by eval
  show ?thesis
    apply (rule nondeterministic_pairs)
     apply (simp only: union)
    apply (simp add: Abs_ffilter Set.filter_def)
    apply standard
     apply clarify
     apply simp
     apply (case_tac "ab = select_general_1")
      apply simp
     apply (case_tac "ab = select_initialise pepsi 2")
      apply simp
    using choice_def by auto
qed

lemma merge_a1_a0: "merge_states (arrives 1 heuristics_1_0) (arrives 0 heuristics_1_0) heuristics_1_0 = merge_a1_a0"
  by eval

lemma no_direct_subsumption_pepsi_general: "\<not> directly_subsumes (tm heuristics_7_5) (tm merge_a1_a0) 0 (select_initialise pepsi 2) select_general_1"
  apply (rule gets_us_to_and_not_subsumes)
  apply (rule_tac x="[]" in exI)
  apply standard
   apply (simp add: accepts_trace_def accepts.base)
  apply standard
   apply (simp add: gets_us_to.base)
  apply (simp add: anterior_context_def)
  apply (rule medial_subsumption_violation)
  apply simp
  apply (rule_tac x="V (I 1)" in exI)
  apply (rule_tac x="<>" in exI)
  apply (simp add: medial_empty cval_true)
  apply (simp add: medial_def cval_true)
  by (simp add: pairs2context_def List.maps_def cval_def)

lemma not_directly_subsumes_general_pepsi: "\<not>directly_subsumes (tm heuristics_7_5) (tm merge_a1_a0) 0 select_general_1 (select_initialise pepsi 2)"
proof-
  have posterior_select_pepsi: "(posterior \<lbrakk>\<rbrakk> (select_initialise pepsi 2)) = \<lbrakk>V (R 2) \<mapsto> {|Eq (Num 0)|}\<rbrakk>"
    apply (rule posterior_consistent_medial)
      apply (simp add: medial_def List.maps_def pairs2context_def)
     apply (simp add: consistent_def)
     apply (rule_tac x="<I 1 := Str ''pepsi''>" in exI)
     apply clarify
     apply standard+
    apply clarify
       apply (simp add: cval_def implode_pepsi)
      apply clarify
      apply (simp add: cval_def)
     apply (case_tac r)
        apply (simp add: cval_true)
       apply (case_tac x2)
        apply (simp add: cval_def)+
    apply (rule ext)
    by (simp add: remove_obsolete_constraints_def)
  have consistent_post_select_p: " consistent (posterior \<lbrakk>\<rbrakk> (select_initialise pepsi 2))"
    apply (simp add: posterior_select_pepsi consistent_def)
    apply (rule_tac x="<R 2 := Num 0>" in exI)
    apply (simp add: cval_def)
    apply clarify
    apply (case_tac r)
       apply (simp add: cval_true)
      apply (case_tac x2)
    using cval_def by auto
  have posterior_select_general: "posterior \<lbrakk>\<rbrakk> select_general_1 = \<lbrakk>V (R 3) \<mapsto> {|Bc True|}, V (R 1) \<mapsto> {|Eq (Num 0)|}\<rbrakk>"
    apply (rule posterior_consistent_medial)
      apply (simp add: medial_def List.maps_def pairs2context_def)
     apply (simp add: consistent_def)
     apply (rule_tac x="<I 1 := Str ''pepsi''>" in exI)
     apply clarify
     apply (case_tac r)
        apply (simp add: cval_true)
       apply (case_tac x2)
        apply (simp add: cval_def)+
    apply (rule ext)
    by (simp add: remove_obsolete_constraints_def)
  have consistent_posterior_select_g: "consistent (posterior \<lbrakk>\<rbrakk> select_general_1)"
    apply (simp add: posterior_select_general consistent_def)
    apply (rule_tac x="<R 1 := Num 0>" in exI)
    apply (simp add: cval_true)
    apply clarify
     apply (case_tac r)
        apply (simp add: cval_true)
       apply (case_tac x2)
    by (simp add: cval_def)+
  have not_medial: "\<not>(\<exists>r i. fBall (medial \<lbrakk>\<rbrakk> [gexp.Eq (V (I 1)) (L (value.Str pepsi))] r) (\<lambda>c. cval c r i = true) \<and> fBex (\<lbrakk>\<rbrakk> r) (\<lambda>x. cval x r i \<noteq> true))"
    apply (simp add: medial_def pairs2context_def List.maps_def)
    by auto
  have consistent_medial: "consistent (medial \<lbrakk>\<rbrakk> [gexp.Eq (V (I 1)) (L (value.Str pepsi))])"
    apply (simp add: medial_def List.maps_def pairs2context_def consistent_def)
    apply (rule_tac x="<I 1 := Str ''pepsi''>" in exI)
    apply safe
      apply (simp add: cval_def implode_pepsi)
     apply (simp add: cval_true)
    apply (case_tac r)
     apply (simp add: cval_true)
       apply (case_tac x2)
    by (simp add: cval_def)+
  have posterior_separate: "posterior_separate \<lbrakk>\<rbrakk> [gexp.Eq (V (I 1)) (L (value.Str pepsi))] [(R 3, V (I 1)), (R 1, L (Num 0))] = \<lbrakk>V (R 3) \<mapsto> {|Eq (Str ''pepsi''), Bc True|}, V (R 1) \<mapsto> {|Eq (Num 0)|}\<rbrakk>"
    apply (simp add: posterior_separate_def Let_def)
    apply standard
     apply clarify
     apply (rule ext)
     apply (simp add: remove_obsolete_constraints_def)
     apply (simp add: medial_def List.maps_def pairs2context_def)
     apply standard
      apply auto[1]
     apply (simp add: implode_pepsi)
    by (simp add: consistent_medial)
  show ?thesis
  apply (rule gets_us_to_and_not_subsumes)
  apply (rule_tac x="[]" in exI)
 apply standard
   apply (simp add: accepts_trace_def accepts.base)
  apply standard
   apply (simp add: gets_us_to.base)
  apply (simp add: anterior_context_def)
    apply (simp add: subsumes_def medial_empty consistent_post_select_p consistent_posterior_select_g)
    apply (simp add: not_medial)
    apply (simp add: posterior_select_pepsi posterior_separate)
    apply (rule_tac x="V (R 2)" in exI)
    apply simp
    apply (rule_tac x="<>" in exI)
    by (simp add: cval_def)
qed

lemma increment_none: "insert_increment 1 0 0 merge_a1_a0 heuristics_7_5 = None"
  by eval

lemma "heuristics [third_trace, second_trace, first_trace] 1 0 0 merge_a1_a0 heuristics_7_5 = Some heuristics_1_0"
  apply (simp add: heuristics_def increment_none del: insert_increment.simps)

lemma merge_transitions_a1_a0: "merge_transitions heuristics_7_5 merge_a1_a0 0 0 0 1 1 (select_initialise pepsi 2) 1 select_general_1 0
                (heuristics [third_trace, second_trace, first_trace]) = Some heuristics_1_0"
  apply (simp add: merge_transitions_def no_direct_subsumption_pepsi_general not_directly_subsumes_general_pepsi)
  by eval

lemma not_directly_subsumes_general_pepsi_2: "\<not> directly_subsumes (tm heuristics_7_5) (tm merge_a1_a0) (leaves 1 heuristics_7_5) select_general_1 (select_initialise pepsi 2)"
proof-
  have leaves_1_heuristics_7_5: "leaves 1 heuristics_7_5 = 0"
    by eval
  have medial: "medial \<lbrakk>\<rbrakk> [gexp.Eq (V (I 1)) (L (value.Str pepsi))] = \<lbrakk>V (I 1) \<mapsto> {|Eq (Str ''pepsi''), Bc True|}\<rbrakk>"
    apply (rule ext)
    by (simp add: medial_def List.maps_def pairs2context_def implode_pepsi)
  have consistent_medial: "consistent \<lbrakk>V (I 1) \<mapsto> {|cexp.Eq (EFSM.Str ''pepsi''), cexp.Bc True|}\<rbrakk>"
    apply (simp add: consistent_def)
    apply (rule_tac x="<I 1 \<mapsto> Str ''pepsi''>" in exI)
    apply clarify
    apply (simp add: cval_def)
    apply (case_tac r)
       apply (simp add: cval_true)
      apply (case_tac x2)
    using cval_def by auto
  have violation: "(\<exists>r i. fBall (posterior_separate \<lbrakk>\<rbrakk> [gexp.Eq (V (I 1)) (L (value.Str pepsi))] [(R 3, V (I 1)), (R 1, L (Num 0))] r) (\<lambda>c. cval c r i = true) \<and>
           fBex (posterior \<lbrakk>\<rbrakk> (select_initialise pepsi 2) r) (\<lambda>x. cval x r i \<noteq> true) \<and> posterior \<lbrakk>\<rbrakk> (select_initialise pepsi 2) r \<noteq> {|Undef|})"
    apply (simp add: posterior_def posterior_separate_def Let_def medial consistent_medial)
    apply (simp add: remove_obsolete_constraints_def)
    apply (rule_tac x="V (R 2)" in exI)
    apply simp
    apply (rule_tac x="<>" in exI)
    by (simp add: cval_def)
  show ?thesis
  apply (rule gets_us_to_and_not_subsumes)
  apply (rule_tac x="[]" in exI)
     apply (simp add: accepts_trace_def accepts.base)
     apply (simp add: leaves_1_heuristics_7_5 gets_us_to.base)
    apply (simp add: anterior_context_def)
    by (simp add: subsumes_def violation)
qed

lemma not_directly_subsumes_initialise_general: "\<not> directly_subsumes (tm heuristics_7_5) (tm merge_a1_a0) (leaves 0 heuristics_7_5) (select_initialise pepsi 2) select_general_1"
proof-
  have leaves_0_heuristics_7_5: "leaves 0 heuristics_7_5 = 0"
    by eval
 have medial: "medial \<lbrakk>\<rbrakk> [gexp.Eq (V (I 1)) (L (value.Str pepsi))] = \<lbrakk>V (I 1) \<mapsto> {|Eq (Str ''pepsi''), Bc True|}\<rbrakk>"
    apply (rule ext)
    by (simp add: medial_def List.maps_def pairs2context_def implode_pepsi)
  have consistent_medial: "consistent \<lbrakk>V (I 1) \<mapsto> {|cexp.Eq (EFSM.Str ''pepsi''), cexp.Bc True|}\<rbrakk>"
    apply (simp add: consistent_def)
    apply (rule_tac x="<I 1 \<mapsto> Str ''pepsi''>" in exI)
    apply clarify
    apply (simp add: cval_def)
    apply (case_tac r)
       apply (simp add: cval_true)
      apply (case_tac x2)
    using cval_def by auto
  have violation: "(\<exists>r i. fBall (posterior_separate \<lbrakk>\<rbrakk> [gexp.Eq (V (I 1)) (L (value.Str pepsi))] [(R 2, L (Num 0))] r) (\<lambda>c. cval c r i = true) \<and>
           fBex (posterior \<lbrakk>\<rbrakk> select_general_1 r) (\<lambda>x. cval x r i \<noteq> true) \<and> posterior \<lbrakk>\<rbrakk> select_general_1 r \<noteq> {|Undef|})"
    apply (simp add: posterior_def posterior_separate_def Let_def medial consistent_medial medial_empty)
    apply (simp add: remove_obsolete_constraints_def)
    apply (rule_tac x="V (R 1)" in exI)
    apply simp
    apply (rule_tac x="<>" in exI)
    by (simp add: cval_def)
  show ?thesis
  apply (rule gets_us_to_and_not_subsumes)
  apply (rule_tac x="[]" in exI)
    apply (simp add: accepts_trace_def accepts.base leaves_0_heuristics_7_5 gets_us_to.base)
    by (simp add: subsumes_def anterior_context_def violation)
qed

lemma insert_increment_none: "insert_increment 1 0 (leaves 1 merge_a1_a0) merge_a1_a0 heuristics_7_5 = None"
  by eval

lemma "merge heuristics_7_5 1 5 (heuristics [third_trace, second_trace, first_trace]) (satisfies {third_trace, second_trace, first_trace}) = Some e"
proof-
  have sorted_list_of_fset:  "sorted_list_of_fset (nondeterministic_pairs merge_1_5) =
[(1, (1, 1), (coin_general 1, 2), coin_general 2, 5), (1, (1, 1), (coin_general 2, 5), coin_general 1, 2), (1, (4, 8), (vend coke, 3), vend pepsi, 6),
  (1, (8, 4), (vend pepsi, 6), vend coke, 3)]"
  apply (simp add: nondeterministic_pairs_merge_1_5)
    by eval
  have leaves_6_heuristics_7_5: "leaves 6 heuristics_7_5 = 5"
    by eval
  have leaves_3_heuristics_7_5: "leaves 3 heuristics_7_5 = 1"
    by eval
  have leaves_6_merge_ar6_ar3: "leaves 6 merge_ar6_ar3 = 1"
    by eval
  have arrives_6_merge_ar6_ar3: "arrives 6 merge_ar6_ar3 = 4"
    by eval
  have arrives_3_merge_ar6_ar3: "arrives 3 merge_ar6_ar3 = 4"
    by eval
  have leaves_1_heuristics_7_5: "leaves 1 heuristics_7_5 = 0"
    by eval
  have leaves_0_heuristics_7_5: "leaves 0 heuristics_7_5 = 0"
    by eval
  have leaves_1_merge_a1_a0: "leaves 1 merge_a1_a0 = 0"
    by eval
  have arrives_1_merge_a1_a0: "arrives 1 merge_a1_a0 = 1"
    by eval
  have arrives_0_merge_a1_a0: "arrives 0 merge_a1_a0 = 1"
    by eval
  show ?thesis
    apply (simp add: merge_def merge_1_5 sorted_list_of_fset merge_ar6_ar3)
    apply (simp add: leaves_6_heuristics_7_5 leaves_3_heuristics_7_5 leaves_6_merge_ar6_ar3 arrives_6_merge_ar6_ar3 arrives_3_merge_ar6_ar3)
    apply (simp add: merge_transitions_heuristics_7_5)

    apply (simp add: nondeterministic_pairs_heuristics_1_0 sorted_list_of_fset_def merge_a1_a0)
    apply (simp add: leaves_1_heuristics_7_5 leaves_0_heuristics_7_5  arrives_1_merge_a1_a0 leaves_1_merge_a1_a0 arrives_0_merge_a1_a0)
    apply (simp add: merge_transitions_a1_a0)

    apply (simp add: nondeterministic_pairs_heuristics_1_0 sorted_list_of_fset_def merge_a1_a0)
    apply (simp add: leaves_1_heuristics_7_5 leaves_0_heuristics_7_5  arrives_1_merge_a1_a0 leaves_1_merge_a1_a0 arrives_0_merge_a1_a0)
    apply (simp add: merge_transitions_a1_a0)

lemma "iterative_learn traces naive_score heuristics = (tm final)"
  apply (simp add: iterative_learn_def)
  apply (rule tm_same)
  apply (simp add: traces_alt first_branch score_first_branch)
  apply (simp add: merge_first_branch_1_2 score_first_branch_initialise)
  apply (simp add: second_branch score_second_branch)
  apply (simp add: merge_first_branch_1_2 score_first_branch_initialise)
  apply (simp add: second_branch third_branch)
  apply (simp add: score_third_branch merge_third_branch)
  apply (simp add: score_heuristics_7_5)




end