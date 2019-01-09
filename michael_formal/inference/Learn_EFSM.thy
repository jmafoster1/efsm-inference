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

lemma nondeterministic_pairs_merged_1_7: "nondeterministic_pairs merged_1_7 = {|
(1, (2, 8), (coin50_50, 2), coin50_50, 7)
|}"
proof-
  have minus_1: "{(2, coin50_50, 2), (5, coin100_100, 3), (8, coin50_50, 7)} - {(5, coin100_100, 3)} = {(2, coin50_50, 2), (8, coin50_50, 7)}"
    apply (simp add: transitions)
    by auto
  have minus_2: "{(2, coin50_50, 2::nat), (5, coin100_100, 3), (8, coin50_50, 7)} - {(8, coin50_50, 7)} = {(2, coin50_50, 2), (5, coin100_100, 3)}"
    apply (simp add: transitions)
    by auto
  have state_nondeterminism_1: "state_nondeterminism 1 {|(2, coin50_50, 2), (5, coin100_100, 3), (8, coin50_50, 7)|} = {|
      (1, (5, 8), (coin100_100, 3), coin50_50, 7),
      (1, (2, 5), (coin50_50, 2), coin100_100, 3),
      (1, (2, 8), (coin50_50, 2), coin50_50, 7)
    |}"
    apply (simp add: state_nondeterminism_def fimage_def minus_1 minus_2)
    apply (simp add: fset_both_sides Abs_fset_inverse)
    by auto
  have minus_3: "{(1, selectCoke, 0), (1, selectPepsi, 1)} - {(1, selectPepsi, 1)} = {(1, selectCoke, 0)}"
    apply (simp add: transitions)
    by auto
  have state_nondeterminism_0: "state_nondeterminism 0 {|(1, selectCoke, 0), (1, selectPepsi, 1)|} = {|(0, (1, 1), (selectPepsi, 1), selectCoke, 0), (0, (1, 1), (selectCoke, 0), selectPepsi, 1)|}"
    by (simp add: state_nondeterminism_def fimage_def minus_3)
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_1_7_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_1 state_nondeterminism_0)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse)
    apply (simp add: Set.filter_def)
    apply safe
    by (simp_all add: choices)
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
  have no_direct_subsumption_coin_50_50_coin50_100: "\<not> directly_subsumes (tm pta) (tm merged_2_9) 8 coin50_50 coin50_100"
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
    apply (simp add: step_merged_2_9_selectPepsi step_merged_2_9_coin50_7)
    by (simp add: posterior_selectPepsi posterior_coin50_50 no_subsumption_coin50_50_coin50_100)
  have no_direct_subsumption_coin50_100_coin_50_50: "\<not> directly_subsumes (tm pta) (tm merged_2_9) 1 coin50_100 coin50_50"
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
    apply (simp add: step_merged_2_9_selectCoke)
    by (simp add: posterior_selectCoke no_subsumption_coin50_100_coin50_50)
  have merge_transitions: "merge_transitions pta merged_2_9 1 8 1 2 2 coin50_50 2 coin50_100 8 generator modifier True = None"
    apply (simp add: merge_transitions_def easy_merge_def)
    by (simp add: generator_def modifier_def no_direct_subsumption_coin_50_50_coin50_100
                     no_direct_subsumption_coin50_100_coin_50_50)
  have arrives_2_merged_1_8: "arrives 2 merged_1_8 = 2"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_1_8 = {|(2, (1, 2), coin50_50)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_1_8_def Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_8_merged_1_8: "arrives 8 merged_1_8 = 9"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (8, (a, b), ba)) merged_1_8 = {|(8, (1, 9), coin50_100)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_1_8_def Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have leaves_2_merged_2_9: "leaves 2 merged_2_9 = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_2_9 = {|(2, (1, 2), coin50_50)|}"
      apply (simp add: ffilter_def merged_2_9_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have arrives_2_merged_2_9: "arrives 2 merged_2_9 = 2"
      proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_2_9 = {|(2, (1, 2), coin50_50)|}"
      apply (simp add: ffilter_def merged_2_9_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_8_merged_2_9: "arrives 8 merged_2_9 = 2"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (8, (a, b), ba)) merged_2_9 = {|(8, (1, 2), coin50_100)|}"
      apply (simp add: ffilter_def merged_2_9_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions) 
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  show ?thesis
    apply (simp add: merge_def merge_states_1_8 nondeterminism_def nondeterministic_pairs_merged_1_8)
    apply (simp add: leaves_2_pta leaves_1_8_pta merge_transitions arrives_8_merged_1_8 arrives_2_merged_1_8)
    apply (simp add: merge_states_2_9 leaves_2_merged_2_9 arrives_2_merged_2_9 arrives_8_merged_2_9)
    by (simp add: merge_transitions nondeterminism_def nondeterministic_pairs_merged_1_8)
qed

lemma singleton_equiv: "is_singleton s \<Longrightarrow> (the_elem s = i) = (s = {i})"
  by (meson is_singleton_the_elem the_elem_eq)

lemma singleton_dest: "fis_singleton (possible_steps e s r aa b) \<Longrightarrow>
       fthe_elem (possible_steps e s r aa b) = (baa, aba) \<Longrightarrow>
       ((s, baa), aba) |\<in>| e"
  apply (simp add: fis_singleton_def fthe_elem_def singleton_equiv)
  apply (simp add: possible_steps_def fmember_def)
  by auto

lemma every_transition_gives_empty: "fis_singleton (possible_steps (tm merge_2_8_2) s r aa b) \<Longrightarrow>
       fthe_elem (possible_steps (tm merge_2_8_2) s r aa b) = (baa, aba) \<Longrightarrow>
       posterior \<lbrakk>\<rbrakk> aba = \<lbrakk>\<rbrakk>"
proof-
  assume premise1: "fis_singleton (possible_steps (tm merge_2_8_2) s r aa b)"
  assume premise2: "fthe_elem (possible_steps (tm merge_2_8_2) s r aa b) = (baa, aba)"
  have possible_transitions: "aba \<noteq> selectCoke \<Longrightarrow>
    aba \<noteq> selectPepsi \<Longrightarrow>
    aba \<noteq> coin50_50 \<Longrightarrow> aba \<noteq> coin50_100 \<Longrightarrow> aba \<noteq> coin100_100 \<Longrightarrow> aba \<noteq> vend_coke \<Longrightarrow> aba \<noteq> vend_pepsi \<Longrightarrow> \<nexists>fst. (fst, aba) |\<in>| (tm merge_2_8_2)"
    by (simp add: merge_2_8_2_def tm_def)
  show ?thesis
    apply (case_tac "aba = selectCoke")
     apply (simp add: posterior_selectCoke)
    apply (case_tac "aba = selectPepsi")
     apply (simp add: posterior_selectPepsi)
    apply (case_tac "aba = coin50_50")
     apply (simp add: posterior_coin50_50)
    apply (case_tac "aba = coin50_100")
     apply (simp add: posterior_coin50_100)
    apply (case_tac "aba = coin100_100")
     apply (simp add: posterior_coin100_100)
    apply (case_tac "aba = vend_coke")
     apply (simp add: posterior_vend_coke)
    apply (case_tac "aba = vend_pepsi")
     apply (simp add: posterior_vend_pepsi)
    using singleton_dest possible_transitions premise1 premise2
    by blast
qed

lemma step_empty:  "step (tm merge_2_8_2) s r aa b = Some (aba, baa, c, d) \<Longrightarrow> (posterior \<lbrakk>\<rbrakk> aba) = \<lbrakk>\<rbrakk>"
  apply (simp add: step_def)
  apply (case_tac "fis_singleton (possible_steps (tm merge_2_8_2) s r aa b)")
   defer
   apply simp
  apply (case_tac "fthe_elem (possible_steps (tm merge_2_8_2) s r aa b)")
  apply simp
  apply clarify
  by (simp add: every_transition_gives_empty)

lemma posterior_sequence_empty: "\<forall>s r. posterior_sequence \<lbrakk>\<rbrakk> (tm merge_2_8_2) s r p = \<lbrakk>\<rbrakk>"
proof(induct p)
  case Nil
  then show ?case by simp
next
  case (Cons a p)
  then show ?case
    apply clarify
    apply simp
    apply (case_tac "step (tm merge_2_8_2) s r (fst a) (snd a)")
     apply simp
    apply (simp add: step_empty)
    apply (case_tac aa)
    apply clarify
    by (simp add: step_empty)
qed

lemma anterior_context_merge_2_8_2: "anterior_context (tm merge_2_8_2) p = \<lbrakk>\<rbrakk>"
  by (simp add: anterior_context_def posterior_sequence_empty)

lemma subsumes_coin50_50_coin50_50: "subsumes \<lbrakk>\<rbrakk> coin50_50 coin50_50"
  apply (simp add: subsumes_def posterior_coin50_50)
  apply (simp add: posterior_def Let_def)
  apply (simp add: coin50_50_def remove_input_constraints_def)
  apply clarify
  using consistent_empty_1 by force

definition merge_2_8_2_coin50 :: iEFSM where
  "merge_2_8_2_coin50 = {|
   (9, (9, 10), vend_pepsi),
   (8, (2, 9), coin50_100),
   (1, (0, 1), selectPepsi),
   (6, (5, 6), vend_coke),
   (3, (1, 5), coin100_100),
   (5, (3, 4), vend_coke),
   (4, (2, 3), coin50_100),
   (0, (0, 1), selectCoke),
   (2, (1, 2), coin50_50)
|}"

lemma replace_coin50: "replace_transition merge_2_8_2 2 1 2 coin50_50 coin50_50 = merge_2_8_2_coin50"
proof-
  have filter: "{a \<in> fset merge_2_8_2. snd a \<noteq> ((1, 2), coin50_50)} = {
   (9, (9, 10), vend_pepsi),
   (8, (2, 9), coin50_100),
   (1, (0, 1), selectPepsi),
   (6, (5, 6), vend_coke),
   (3, (1, 5), coin100_100),
   (5, (3, 4), vend_coke),
   (4, (2, 3), coin50_100),
   (0, (0, 1), selectCoke)}"
    apply (simp add: merge_2_8_2_def)
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
    apply (simp add: merge_2_8_2_coin50_def filter)
    by auto
qed

lemma merge_1_7: "merge pta 1 7 generator modifier = Some x"
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
  have leaves_7_pta: "leaves 7 pta = 7"
  proof-
    have set_filter: "Set.filter (\<lambda>x. \<exists>a b ba. x = (7, (a, b), ba)) (fset pta) = {(7, (7, 8), coin50_50)}"
      apply (simp add: Set.filter_def pta_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter_def fthe_elem_def Abs_fset_inverse set_filter)
  qed

  have arrives_2_merged_1_7: "arrives 2 merged_1_7 = 2"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_1_7 = {|(2, (1, 2), coin50_50)|}"
      apply (simp add: ffilter_def merged_1_7_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_7_merged_1_7: "arrives 7 merged_1_7 = 8"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (7, (a, b), ba)) merged_1_7 = {|(7, (1, 8), coin50_50)|}"
      apply (simp add: ffilter_def merged_1_7_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have directly_subsumes_coin50_coin50: "\<forall>s. directly_subsumes (tm pta) (tm merge_2_8_2) s coin50_50 coin50_50"
    by (simp add: directly_subsumes_def anterior_context_merge_2_8_2 subsumes_coin50_50_coin50_50)
                 (* easy_merge oldEFSM newEFSM     t1FromOld t2FromOld newFrom t1NewTo t2NewTo t1        u1 t2        u2 maker *)
                 (* replace_transition newEFSM u1 newFrom t2NewTo t1 t2 *)
  have easy_merge: "easy_merge pta merge_2_8_2 1 7 1 2 2 coin50_50 2 coin50_50 7 generator = Some merge_2_8_2_coin50"
    (* apply (simp add: easy_merge_def) *)
    unfolding easy_merge_def
    apply (simp add: directly_subsumes_coin50_coin50)
    by (simp add: replace_coin50)
  have merge_transitions: "merge_transitions pta merge_2_8_2 1 7 1 2 2 coin50_50 2 coin50_50 7 generator modifier True = Some merge_2_8_2_coin50"
    apply (simp add: merge_transitions_def)
    by (simp add: easy_merge)
  have leaves_2_merge_2_8_2: "leaves 2 merge_2_8_2 = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merge_2_8_2 = {|(2, (1, 2), coin50_50)|}"
      apply (simp add: ffilter_def merge_2_8_2_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have arrives_2_merge_2_8_2: "arrives 2 merge_2_8_2 = 2"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merge_2_8_2 = {|(2, (1, 2), coin50_50)|}"
      apply (simp add: ffilter_def merge_2_8_2_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_7_merge_2_8_2: "arrives 7 merge_2_8_2 = 2"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (7, (a, b), ba)) merge_2_8_2= {|(7, (1, 2), coin50_50)|}"
      apply (simp add: ffilter_def merge_2_8_2_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions) 
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  show ?thesis
    apply (simp add: merge_def merge_states_1_7 nondeterminism_def nondeterministic_pairs_merged_1_7)
    apply (simp add: leaves_2_pta leaves_7_pta arrives_2_merged_1_7 arrives_7_merged_1_7)
    apply (simp add: leaves_2_merge_2_8_2 merge_states_2_8_2 arrives_2_merge_2_8_2 arrives_7_merge_2_8_2)
    apply (simp add: merge_transitions)

lemma "learn traces naive_score generator modifier = drinks"
  apply (simp add: learn_def build_pta scoring_1 merge_1_8)
  sorry

end