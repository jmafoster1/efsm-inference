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

lemma anterior_context_merged_2_8: "anterior_context (tm merged_2_8) p = \<lbrakk>\<rbrakk>"
proof-
  have every_transition_gives_empty: "\<forall>s r aa b baa aba. fis_singleton (possible_steps (tm merged_2_8) s r aa b) \<longrightarrow>
       fthe_elem (possible_steps (tm merged_2_8) s r aa b) = (baa, aba) \<longrightarrow>
       posterior \<lbrakk>\<rbrakk> aba = \<lbrakk>\<rbrakk>"
  proof-
    have possible_transitions: "\<forall>aba. aba \<noteq> selectCoke \<longrightarrow>
      aba \<noteq> selectPepsi \<longrightarrow>
      aba \<noteq> coin50_50 \<longrightarrow>
      aba \<noteq> coin50_100 \<longrightarrow>
      aba \<noteq> coin100_100 \<longrightarrow>
      aba \<noteq> vend_coke \<longrightarrow>
      aba \<noteq> vend_pepsi \<longrightarrow> ( \<nexists>fst. (fst, aba) |\<in>| (tm merged_2_8))"
      by (simp add: merged_2_8_def tm_def)
    show ?thesis
      apply clarify
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
      using singleton_dest possible_transitions
      by blast
  qed
  have step_empty:  "\<forall>s r aa b aba baa c d. step (tm merged_2_8) s r aa b = Some (aba, baa, c, d) \<longrightarrow> (posterior \<lbrakk>\<rbrakk> aba) = \<lbrakk>\<rbrakk>"
    apply clarify
    apply (simp add: step_def)
    apply (case_tac "fis_singleton (possible_steps (tm merged_2_8) s r aa b)")
     defer
     apply simp
    apply (case_tac "fthe_elem (possible_steps (tm merged_2_8) s r aa b)")
    apply simp
    apply clarify
    by (simp add: every_transition_gives_empty)
  have posterior_sequence_empty: "\<forall>s r. posterior_sequence \<lbrakk>\<rbrakk> (tm merged_2_8) s r p = \<lbrakk>\<rbrakk>"
  proof(induct p)
    case Nil
    then show ?case by simp
  next
    case (Cons a p)
    then show ?case
      apply clarify
      apply simp
      apply (case_tac "step (tm merged_2_8) s r (fst a) (snd a)")
       apply simp
      apply (simp add: step_empty)
      apply (case_tac aa)
      apply clarify
      by (simp add: step_empty)
  qed
  show ?thesis
    by (simp add: anterior_context_def posterior_sequence_empty)
qed

definition merged_3_9 :: iEFSM where
  "merged_3_9 = {|(0, (0, 1), selectCoke),  (2, (1, 2), coin50_50),   (8, (2, 3), coin50_100), (5, (3, 4), vend_coke),
                         (1, (0, 1), selectPepsi), (3, (1, 5), coin100_100), (6, (5, 6), vend_coke),
                                                   (4, (2, 3), coin50_100),  (9, (3, 10), vend_pepsi)|}"

definition merged_3_9_coin100 :: iEFSM where
  "merged_3_9_coin100 = {|(0, (0, 1), selectCoke),  (2, (1, 2), coin50_50),  (5, (3, 4), vend_coke),
                         (1, (0, 1), selectPepsi), (3, (1, 5), coin100_100), (6, (5, 6), vend_coke),
                                                   (4, (2, 3), coin50_100),  (9, (3, 10), vend_pepsi)|}"

definition merged_4_10 :: iEFSM where
  "merged_4_10 = {|(0, (0, 1), selectCoke), (2, (1, 2), coin50_50), (5, (3, 4), vend_coke), (1, (0, 1), selectPepsi), (3, (1, 5), coin100_100),
      (6, (5, 6), vend_coke), (4, (2, 3), coin50_100), (9, (3, 4), vend_pepsi)|}"

lemma anterior_context_merged_3_9: "anterior_context (tm merged_3_9) p = \<lbrakk>\<rbrakk>"
proof-
have every_transition_gives_empty: "\<forall>s r aa b baa aba. fis_singleton (possible_steps (tm merged_3_9) s r aa b) \<longrightarrow>
       fthe_elem (possible_steps (tm merged_3_9) s r aa b) = (baa, aba) \<longrightarrow>
       posterior \<lbrakk>\<rbrakk> aba = \<lbrakk>\<rbrakk>"
  proof-
    have possible_transitions: "\<forall>aba. aba \<noteq> selectCoke \<longrightarrow>
      aba \<noteq> selectPepsi \<longrightarrow>
      aba \<noteq> coin50_50 \<longrightarrow>
      aba \<noteq> coin50_100 \<longrightarrow>
      aba \<noteq> coin100_100 \<longrightarrow>
      aba \<noteq> vend_coke \<longrightarrow>
      aba \<noteq> vend_pepsi \<longrightarrow> ( \<nexists>fst. (fst, aba) |\<in>| (tm merged_3_9))"
      by (simp add: merged_3_9_def tm_def)
    show ?thesis
      apply clarify
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
      using singleton_dest possible_transitions
      by blast
  qed
  have step_empty:  "\<forall>s r aa b aba baa c d. step (tm merged_3_9) s r aa b = Some (aba, baa, c, d) \<longrightarrow> (posterior \<lbrakk>\<rbrakk> aba) = \<lbrakk>\<rbrakk>"
    apply clarify
    apply (simp add: step_def)
    apply (case_tac "fis_singleton (possible_steps (tm merged_3_9) s r aa b)")
     defer
     apply simp
    apply (case_tac "fthe_elem (possible_steps (tm merged_3_9) s r aa b)")
    apply simp
    apply clarify
    by (simp add: every_transition_gives_empty)
  have posterior_sequence_empty: "\<forall>s r. posterior_sequence \<lbrakk>\<rbrakk> (tm merged_3_9) s r p = \<lbrakk>\<rbrakk>"
  proof(induct p)
    case Nil
    then show ?case by simp
  next
    case (Cons a p)
    then show ?case
      apply clarify
      apply simp
      apply (case_tac "step (tm merged_3_9) s r (fst a) (snd a)")
       apply simp
      apply (simp add: step_empty)
      apply (case_tac aa)
      apply clarify
      by (simp add: step_empty)
  qed
  show ?thesis
    by (simp add: anterior_context_def posterior_sequence_empty)
qed

lemma subsumes_coin50_50_coin50_50: "subsumes \<lbrakk>\<rbrakk> coin50_50 coin50_50"
  apply (simp add: subsumes_def posterior_coin50_50)
  apply (simp add: posterior_def Let_def)
  apply (simp add: coin50_50_def remove_input_constraints_def)
  apply clarify
  using consistent_empty_1 by force

lemma subsumes_coin50_100_coin50_100: "subsumes \<lbrakk>\<rbrakk> coin50_100 coin50_100"
  apply (simp add: subsumes_def posterior_coin50_100)
  apply (simp add: posterior_def Let_def)
  apply (simp add: coin50_100_def remove_input_constraints_def)
  apply clarify
  using consistent_empty_1 by force

definition merged_2_8_coin50 :: iEFSM where
  "merged_2_8_coin50 = {|
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

lemma replace_coin50: "replace_transition merged_2_8 2 1 2 coin50_50 coin50_50 = merged_2_8_coin50"
proof-
  have filter: "{a \<in> fset merged_2_8. snd a \<noteq> ((1, 2), coin50_50)} = {
   (9, (9, 10), vend_pepsi),
   (8, (2, 9), coin50_100),
   (1, (0, 1), selectPepsi),
   (6, (5, 6), vend_coke),
   (3, (1, 5), coin100_100),
   (5, (3, 4), vend_coke),
   (4, (2, 3), coin50_100),
   (0, (0, 1), selectCoke)}"
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

lemma nondeterministic_pairs_merged_2_8_coin50: "nondeterministic_pairs merged_2_8_coin50 = {|(2, (3, 9), (coin50_100, 4), coin50_100, 8)|}"
proof-
  have minus_1: "{|(5, coin100_100, 3), (2, coin50_50, 2)|} |-| {|(2, coin50_50, 2)|} = {|(5, coin100_100, 3)|}"
    apply (simp add: transitions)
    by auto
  have minus_3: "{(1, selectCoke, 0), (1, selectPepsi, 1)} - {(1, selectPepsi, 1)} = {(1, selectCoke, 0)}"
    apply (simp add: transitions)
    by auto
  have minus_2: "{|(9, coin50_100, 8::nat), (3, coin50_100, 4)|} |-| {|(3, coin50_100, 4)|} = {|(9, coin50_100, 8)|}"
    apply (simp add: transitions)
    by auto
  have state_nondeterminism_0: "state_nondeterminism 0 {|(1, selectCoke, 0), (1, selectPepsi, 1)|} = {|(0, (1, 1), (selectPepsi, 1), selectCoke, 0), (0, (1, 1), (selectCoke, 0), selectPepsi, 1)|}"
    by (simp add: state_nondeterminism_def fimage_def minus_3)
  have outgoing_0_equiv: "{|(1, selectPepsi, 1), (1, selectCoke, 0)|} = {|(1, selectCoke, 0), (1, selectPepsi, 1)|}"
    by auto
  have state_nondeterminism_1: "state_nondeterminism 1 {|(5, coin100_100, 3), (2, coin50_50, 2)|} = {|(1, (2, 5), (coin50_50, 2), coin100_100, 3)|}"
    by (simp add: state_nondeterminism_def minus_1)
  have state_nondeterminism_2: "state_nondeterminism 2 {|(9, coin50_100, 8), (3, coin50_100, 4)|} = {|(2, (3, 9), (coin50_100, 4), coin50_100, 8)|}"
    by (simp add: state_nondeterminism_def minus_2)
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_2_8_coin50_def)
    apply (simp add: outgoing_transitions_def fimage_def)
    apply (simp add: outgoing_0_equiv state_nondeterminism_0 state_nondeterminism_1 state_nondeterminism_2)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply safe
    by (simp_all add: choices)
qed

lemma nondeterministic_pairs_merged_3_9_coin100: "nondeterministic_pairs merged_3_9_coin100 = {|(3, (4, 10), (vend_coke, 5), vend_pepsi, 9)|}"
proof-
  have minus_1: "{|(2, coin50_50, 2), (5, coin100_100, 3)|} |-| {|(5, coin100_100, 3)|} = {|(2, coin50_50, 2)|}"
    apply (simp add: transitions)
    by auto
  have minus_2: "{|(4, vend_coke, 5), (10, vend_pepsi, 9)|} |-| {|(10, vend_pepsi, 9)|} = {|(4, vend_coke, 5)|}"
    apply (simp add: transitions)
    by auto
  have minus_3: "{(1, selectCoke, 0), (1, selectPepsi, 1)} - {(1, selectPepsi, 1)} = {(1, selectCoke, 0)}"
    apply (simp add: transitions)
    by auto
  have state_nondeterminism_0: "state_nondeterminism 0 {|(1, selectCoke, 0), (1, selectPepsi, 1)|} = {|(0, (1, 1), (selectPepsi, 1), selectCoke, 0), (0, (1, 1), (selectCoke, 0), selectPepsi, 1)|}"
    by (simp add: state_nondeterminism_def fimage_def minus_3)
  have state_nondeterminism_1: "state_nondeterminism 1 {|(2, coin50_50, 2), (5, coin100_100, 3)|} = {|(1, (2, 5), (coin50_50, 2), coin100_100, 3)|}"
    by (simp add: state_nondeterminism_def minus_1)
  have state_nondeterminism_3: "state_nondeterminism 3 {|(4, vend_coke, 5), (10, vend_pepsi, 9)|} = {|(3, (4, 10), (vend_coke, 5), vend_pepsi, 9)|}"
    by (simp add: state_nondeterminism_def minus_2)
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_3_9_coin100_def)
    apply (simp add: outgoing_transitions_def fimage_def)
    apply (simp add: state_nondeterminism_0 state_nondeterminism_1 state_nondeterminism_3)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply safe
    by (simp_all add: orders choices)
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
  have directly_subsumes_coin50_coin50: "\<forall>s. directly_subsumes (tm pta) (tm merged_2_8) s coin50_50 coin50_50"
    by (simp add: directly_subsumes_def anterior_context_merged_2_8 subsumes_coin50_50_coin50_50)
                 (* easy_merge oldEFSM newEFSM     t1FromOld t2FromOld newFrom t1NewTo t2NewTo t1        u1 t2        u2 maker *)
                 (* replace_transition newEFSM u1 newFrom t2NewTo t1 t2 *)
  have easy_merge: "easy_merge pta merged_2_8 1 7 1 2 2 coin50_50 2 coin50_50 7 generator = Some merged_2_8_coin50"
    (* apply (simp add: easy_merge_def) *)
    unfolding easy_merge_def
    apply (simp add: directly_subsumes_coin50_coin50)
    by (simp add: replace_coin50)
  have merge_transitions: "merge_transitions pta merged_2_8 1 7 1 2 2 coin50_50 2 coin50_50 7 generator modifier True = Some merged_2_8_coin50"
    apply (simp add: merge_transitions_def)
    by (simp add: easy_merge)
  have leaves_2_merged_2_8: "leaves 2 merged_2_8 = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_2_8 = {|(2, (1, 2), coin50_50)|}"
      apply (simp add: ffilter_def merged_2_8_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have arrives_2_merged_2_8: "arrives 2 merged_2_8 = 2"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_2_8 = {|(2, (1, 2), coin50_50)|}"
      apply (simp add: ffilter_def merged_2_8_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_7_merged_2_8: "arrives 7 merged_2_8 = 2"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (7, (a, b), ba)) merged_2_8= {|(7, (1, 2), coin50_50)|}"
      apply (simp add: ffilter_def merged_2_8_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions) 
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_4_merged_2_8_coin50: "arrives 4 merged_2_8_coin50 = 3"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (4, (a, b), ba)) merged_2_8_coin50 = {|(4, (2, 3), coin50_100)|}"
      apply (simp add: ffilter_def merged_2_8_coin50_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_8_merged_2_8_coin50: "arrives 8 merged_2_8_coin50 = 9"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (8, (a, b), ba)) merged_2_8_coin50 = {|(8, (2, 9), coin50_100)|}"
      apply (simp add: ffilter_def merged_2_8_coin50_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have merge_states_3_9_merged_2_8_coin50: "merge_states 3 9 merged_2_8_coin50 = merged_3_9"
    apply (simp add: merge_states_def merge_states_aux_def merged_2_8_coin50_def merged_3_9_def)
    by auto
  have leaves_4_pta: "leaves 4 pta = 2"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (4, (a, b), ba)) pta = {|(4, (2, 3), coin50_100)|}"
      apply (simp add: ffilter_def pta_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have leaves_8_pta: "leaves 8 pta = 8"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (8, (a, b), ba)) pta = {|(8, (8, 9), coin50_100)|}"
      apply (simp add: ffilter_def pta_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have leaves_4_merged_3_9: "leaves 4 merged_3_9 = 2 \<and>arrives 4 merged_3_9 = 3"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (4, (a, b), ba)) merged_3_9 = {|(4, (2, 3), coin50_100)|}"
      apply (simp add: ffilter_def merged_3_9_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def leaves_def ffilter)
  qed
  have arrives_8_merged_3_9: "arrives 8 merged_3_9 = 3"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (8, (a, b), ba)) merged_3_9 = {|(8, (2, 3), coin50_100)|}"
      apply (simp add: ffilter_def merged_3_9_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have merge_transitions_2: "merge_transitions pta merged_3_9 2 8 2 3 3 coin50_100 4 coin50_100 8 generator modifier True = Some merged_3_9_coin100"
  proof-
    have ffilter: "ffilter (\<lambda>x. snd x \<noteq> ((2, 3), coin50_100)) merged_3_9 = {|
                         (0, (0, 1), selectCoke),  (2, (1, 2), coin50_50),          (5, (3, 4), vend_coke),
                         (1, (0, 1), selectPepsi), (3, (1, 5), coin100_100), (6, (5, 6), vend_coke),
                                                   (9, (3, 10), vend_pepsi)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def merged_3_9_def)
      apply standard
       apply clarify
      by auto
    have easy_merge: "easy_merge pta merged_3_9 2 8 2 3 3 coin50_100 4 coin50_100 8 generator = Some merged_3_9_coin100"
      apply (simp add: easy_merge_def directly_subsumes_def anterior_context_merged_3_9 subsumes_coin50_100_coin50_100)
      apply (simp add: replace_transition_def ffilter)
      apply (simp add: merged_3_9_coin100_def)
      by auto
    show ?thesis
      by (simp add: merge_transitions_def easy_merge)
  qed
  have arrives_5_merged_3_9_coin100: "arrives 5 merged_3_9_coin100 = 4"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (5, (a, b), ba)) merged_3_9_coin100 = {|(5, (3, 4), vend_coke)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_3_9_coin100_def Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_9_merged_3_9_coin100: "arrives 9 merged_3_9_coin100 = 10"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (9, (a, b), ba)) merged_3_9_coin100 = {|(9, (3, 10), vend_pepsi)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_3_9_coin100_def Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have merge_states_4_10: "merge_states 4 10 merged_3_9_coin100 = merged_4_10"
    by (simp add: merge_states_def merge_states_aux_def merged_3_9_coin100_def merged_4_10_def)

  have leaves_5_pta: "leaves 5 pta = 3"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (5, (a, b), ba)) pta = {|(5, (3, 4), vend_coke)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def pta_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have leaves_9_pta: "leaves 9 pta = 9"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (9, (a, b), ba)) pta = {|(9, (9, 10), vend_pepsi)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def pta_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have leaves_5_merged_4_10: "leaves 5 merged_4_10 = 3 \<and> arrives 5 merged_4_10 = 4"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (5, (a, b), ba)) merged_4_10 = {|(5, (3, 4), vend_coke)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def merged_4_10_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def arrives_def ffilter)
  qed
  have arrives_9_merged_4_10: "arrives 9 merged_4_10 = 4"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (9, (a, b), ba)) merged_4_10 = {|(9, (3, 4), vend_pepsi)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def merged_4_10_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def arrives_def ffilter)
  qed
  show ?thesis
    apply (simp add: merge_def merge_states_1_7 nondeterminism_def nondeterministic_pairs_merged_1_7)
    apply (simp add: leaves_2_pta leaves_7_pta arrives_2_merged_1_7 arrives_7_merged_1_7)
    apply (simp add: leaves_2_merged_2_8 merge_states_2_8 arrives_2_merged_2_8 arrives_7_merged_2_8)
    apply (simp add: merge_transitions nondeterminism_def nondeterministic_pairs_merged_2_8_coin50)
    apply (simp add: arrives_4_merged_2_8_coin50 arrives_8_merged_2_8_coin50 merge_states_3_9_merged_2_8_coin50)
    apply (simp add: leaves_4_pta leaves_8_pta leaves_4_merged_3_9 arrives_8_merged_3_9)
    apply (simp add: merge_transitions_2 nondeterminism_def nondeterministic_pairs_merged_3_9_coin100)
    apply (simp add: arrives_5_merged_3_9_coin100 arrives_9_merged_3_9_coin100 merge_states_4_10)
    apply (simp add: leaves_5_pta leaves_9_pta leaves_5_merged_4_10 arrives_9_merged_4_10)

lemma "learn traces naive_score generator modifier = drinks"
  apply (simp add: learn_def build_pta scoring_1 merge_1_8)
  sorry

end