theory DM_Inference
imports Inference SelectionStrategies "../examples/Drinks_Machine_2" EFSM_Dot
begin

declare One_nat_def[simp del]

lemma "max coin vend = vend"
  by (simp add: max_def coin_def vend_def less_eq_transition_ext_def less_transition_ext_def)

definition drinks2 :: iEFSM where
  "drinks2 = {|(0, (0, 1), select),
   (1, (1, 1), vend_nothing),
   (2, (1, 2), coin),
   (3, (2, 2), coin),
   (4, (2, 2), vend_fail),
   (5, (2, 3), vend)|}"

definition merged_1_2 :: iEFSM where
  "merged_1_2 = {|
              (0, (0,1), select),
              (1, (1,1), vend_nothing),
              (2, (1,1), coin),
              (3, (1,1), coin),
              (4, (1,1), vend_fail),
              (5, (1,3), vend)
         |}"

definition merged_1_3 :: iEFSM where
  "merged_1_3 = {|(0, (0, 1), select), (1, (1, 1), vend_nothing), (2, (1, 1), coin), (3, (1, 1), coin), (4, (1, 1), vend_fail), (5, (1, 1), vend)|}"

lemma merge_states_1_2: "merge_states 1 2 drinks2 = merged_1_2"
  by (simp add: merge_states_def merge_states_aux_def drinks2_def merged_1_2_def)

lemma unequal_labels[simp]: "Label t1 \<noteq> Label t2 \<Longrightarrow> t1 \<noteq> t2"
  by auto

lemma unequal_arities[simp]: "Arity t1 \<noteq> Arity t2 \<Longrightarrow> t1 \<noteq> t2"
  by auto

lemma choice_vend_vend_nothing: "choice vend vend_nothing"
  apply (simp add: choice_def transitions)
  apply (rule_tac x="<R 2 := Num 100>" in exI)
  by simp

lemma vend_nothing_lt_vend: "vend_nothing < vend"
  by (simp add: less_transition_ext_def transitions)

lemma no_choice_vend_coin: "\<not> choice vend coin"
  by (simp add: choice_def transitions)

lemma no_choice_vend_vend_fail:  "\<not> choice vend vend_fail"
  apply (simp add: choice_def transitions)
  apply safe
  apply (case_tac " MaybeBoolInt (\<lambda>x y. y < x) (Some (Num 100)) (s (R 2))")
   apply simp
  by simp

lemma vend_nothing_lt_vend_fail: "vend_nothing < vend_fail"
  by (simp add: less_transition_ext_def transitions)

lemma choice_vend_nothing_vend_fail: "choice vend_nothing vend_fail"
  apply (simp add: choice_def transitions)
  apply (rule_tac x="<R 2 := Num 0>" in exI)
  by simp

lemma vend_fail_not_lt_vend_nothing: "\<not>vend_fail < vend_nothing"
  by (simp add: transitions less_transition_ext_def)

lemma no_choice_coin_vend_nothing: "\<not> choice coin vend_nothing"
  by (simp add: choice_def coin_def vend_nothing_def)

lemma no_choice_vend_nothing_coin: "\<not> choice vend_nothing coin"
  by (simp add: choice_symmetry no_choice_coin_vend_nothing)

lemma choice_coin_coin: "choice coin coin"
  by (simp add: choice_def coin_def)

lemma choice_vend_nothing_vend_nothing: "choice vend_nothing vend_nothing"
  by (simp add: choice_def vend_nothing_def)

lemma no_choice_coin_vend_fail: "\<not> choice coin vend_fail"
  by (simp add: choice_def transitions)

lemma choice_vend_fail_vend_fail: "choice vend_fail vend_fail"
  apply (simp add: choice_def transitions)
  apply (rule_tac x="<R 2 := Num 0>" in exI)
  by simp

lemma no_choice_vend_fail_coin: "\<not> choice vend_fail coin"
  by (simp add: choice_symmetry no_choice_coin_vend_fail)

lemma choice_vend_fail_vend_nothing: "choice vend_fail vend_nothing"
  using choice_symmetry choice_vend_nothing_vend_fail by auto

lemma choice_vend_nothing_vend: "choice vend_nothing vend"
  by (simp add: choice_symmetry choice_vend_vend_nothing)

lemma no_choice_coin_vend: "\<not>choice coin vend"
  by (simp add: transitions choice_def)

lemmas choices = choice_symmetry no_choice_coin_vend choice_vend_nothing_vend no_choice_vend_vend_fail no_choice_vend_coin choice_vend_vend_nothing no_choice_coin_vend_nothing no_choice_vend_nothing_coin no_choice_vend_fail_coin choice_vend_fail_vend_nothing choice_vend_nothing_vend_fail choice_coin_coin choice_vend_nothing_vend_nothing no_choice_coin_vend_fail choice_vend_fail_vend_fail

lemma medial_vend_nothing: "(medial c (Guard vend_nothing)) = c"
  by (simp add: transitions)

lemma medial_vend_fail: "medial select_posterior (Guard vend_fail) = \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> And (Lt (Num 100)) (Eq (Num 0))\<rbrakk>"
  apply (rule ext)
  by (simp add: transitions select_posterior_def)

lemma vend_nothing_posterior: "posterior select_posterior vend_nothing = select_posterior"
  apply (simp only: posterior_def medial_vend_nothing)
  apply (simp add: consistent_select_posterior)
  apply (rule ext)
  by (simp add: transitions remove_input_constraints_def select_posterior_def)

lemma consistent_medial_vend_fail: "consistent \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> And (cexp.Lt (Num 100)) (cexp.Eq (Num 0))\<rbrakk>"
  apply (simp add: consistent_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num 0>" in exI)
  by (simp add: consistent_empty_4)

lemma vend_fail_posterior: "posterior select_posterior vend_fail = \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> And (Lt (Num 100)) (Eq (Num 0))\<rbrakk>"
  apply (simp only: posterior_def medial_vend_fail)
  apply (simp add: consistent_medial_vend_fail )
  apply (rule ext)
  by (simp add: transitions remove_input_constraints_def select_posterior_def)

lemma vend_fail_subsumes_vend_nothing: "subsumes select_posterior vend_fail vend_nothing"
  apply (simp add: subsumes_def)
  apply safe
        apply (simp add: transitions)
       apply (simp add: transitions)
      apply (simp add: transitions)
     apply (simp add: guard_vend_nothing medial_vend_fail)
     apply (simp add: select_posterior_def)
     apply auto[1]  
    apply (simp add: transitions)
   apply (simp add: medial_vend_nothing )
   apply (simp add: vend_nothing_posterior )
   apply (simp only: vend_fail_posterior)
   apply (simp )
   apply (case_tac "r = V (R 2)")
    apply simp
    apply (case_tac "ValueLt (Some i) (Some (Num 100))")
     apply simp
    apply simp
   apply (case_tac "r = V (R 1)")
    apply simp
   apply simp
    apply (simp add: vend_fail_posterior select_posterior_def)
  apply (simp add: select_posterior_def)
  apply (simp add: consistent_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num 0>" in exI)
  apply (simp add: vend_fail_posterior)
  by (simp add: consistent_empty_4 )

lemma vend_doesnt_exit_1[simp]: "\<not>exits_state drinks2 vend 1"
  by (simp add: exits_state_def drinks2_def transitions )

lemma vend_nothing_exits_1[simp]: "exits_state drinks2 vend_nothing 1"
  apply (simp add: exits_state_def drinks2_def)
  by auto

definition coin50 :: "transition" where
"coin50 \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [(gexp.Eq (V (I 1)) (L (Num 50)))],
        Outputs = [Plus (V (R 2)) (V (I 1))],
        Updates = [
                    (R 1, V (R 1)),
                    (R 2, Plus (V (R 2)) (V (I 1)))
                  ]
      \<rparr>"

definition basically_drinks :: iEFSM where
  "basically_drinks = {|(2, (1, 1), coin), (1, (1, 1), vend_fail), (0, (0, 1), select), (5, (1, 3), vend)|}"

lemma no_subsumption_vend_nothing_vend: "\<not>subsumes c vend_nothing vend"
  by (simp add: subsumes_def transitions)

lemma no_subsumption_vend_vend_nothing: "\<not>subsumes c vend vend_nothing"
  by (simp add: subsumes_def transitions)

lemma scoring: "rev (sorted_list_of_fset (score drinks2 naive_score)) = [(3, 1, 2)]"
proof-
  have S_drinks2: "S drinks2 = {|0, 1, 2, 3|}"
    apply (simp add: S_def drinks2_def)
    by auto
  have S_drinks2_squared: "{|0, 1, 2, 3|} |\<times>| {|0, 1, 2, 3|} = {|
      (0, 0), (0, 1), (0, 2), (0, 3),
      (1, 0), (1, 1), (1, 2), (1, 3),
      (2, 0), (2, 1), (2, 2), (2, 3),
      (3, 0), (3, 1), (3, 2), (3, 3)
    |}"
    apply (simp add: fprod_def fset_both_sides Abs_fset_inverse)
    by auto
  have ffilter: "ffilter (\<lambda>(x, y). x < y) (S drinks2 |\<times>| S drinks2) = {|
      (0, 1), (0, 2), (0, 3),
              (1, 2), (1, 3),
                      (2, 3)
    |}"
    apply (simp add: S_drinks2 S_drinks2_squared)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    by auto
  have score: "score DM_Inference.drinks2 naive_score = {|(3, 1, 2)|}"
    apply (simp add: score_def ffilter)
    apply (simp add: outgoing_transitions_def drinks2_def fimage_def)
    apply (simp add: naive_score_empty set_equiv)
    apply (simp add: naive_score_def fprod_def)
    by (simp add: transitions Abs_fset_inverse)
  show ?thesis
    by (simp add: score sorted_list_of_fset_def)
qed

lemma nondeterministic_pairs_merged_1_2: "nondeterministic_pairs merged_1_2 = {|
      (1, (3, 1),(vend, 5),vend_nothing, 1),
      (1, (1, 1),(vend_fail, 4),vend_nothing, 1),
      (1, (1, 1),(coin,3),coin,2),
      (1, (1, 1),(coin,2),coin,3),
      (1, (1, 3), (vend_nothing, 1),vend, 5),
      (1, (1, 1), (vend_nothing, 1),vend_fail, 4)
|}"
proof-
  have minus_1: "{(1, vend_nothing, 1::nat), (1, coin, 2), (1, coin, 3), (1, vend_fail, 4), (3, vend, 5)} - {(1, coin, 2)} = {(1, vend_nothing, 1), (1, coin, 3), (1, vend_fail, 4), (3, vend, 5)}"
    apply (simp add: transitions)
    by auto
  have minus_2: "{(1, vend_nothing, 1::nat), (1, coin, 2), (1, coin, 3), (1, vend_fail, 4), (3, vend, 5)} - {(1, coin, 3)} = {(1, vend_nothing, 1), (1, coin, 2), (1, vend_fail, 4), (3, vend, 5)}"
    apply (simp add: transitions)
    by auto
  have minus_3: "{(1, vend_nothing, 1::nat), (1, coin, 2), (1, coin, 3), (1, vend_fail, 4), (3, vend, 5)} - {(1, vend_fail, 4)} = {(1, vend_nothing, 1), (1, coin, 2), (1, coin, 3), (3, vend, 5)}"
    apply (simp add: transitions)
    by auto
  have minus_4: "{(1, vend_nothing, 1::nat), (1, coin, 2), (1, coin, 3), (1, vend_fail, 4), (3, vend, 5)} -
                                     {(3, vend, 5)} = {(1, vend_nothing, 1), (1, coin, 2), (1, coin, 3), (1, vend_fail, 4)}"
    apply (simp add: transitions)
    by auto
  have state_nondeterminism_1: "state_nondeterminism 1 {|(1, vend_nothing, 1), (1, coin, 2), (1, coin, 3), (1, vend_fail, 4), (3, vend, 5)|} = {|
      (1, (3, 1),(vend, 5),vend_fail, 4),
      (1, (3, 1),(vend, 5),coin, 3),
      (1, (3, 1),(vend, 5),coin,2),
      (1, (3, 1),(vend, 5),vend_nothing, 1),
      (1, (1, 3),(vend_fail, 4),vend, 5),
      (1, (1, 1),(vend_fail, 4),coin,3),
      (1, (1, 1),(vend_fail, 4),coin,2),
      (1, (1, 1),(vend_fail, 4),vend_nothing, 1),
      (1, (1, 3),(coin,3),vend, 5),
      (1, (1, 1),(coin,3),vend_fail, 4),
      (1, (1, 1),(coin,3),coin,2),
      (1, (1, 1),(coin,3),vend_nothing, 1),
      (1, (1, 3),(coin,2),vend, 5),
      (1, (1, 1),(coin,2),vend_fail, 4),
      (1, (1, 1),(coin,2),coin,3),
      (1, (1, 1),(coin,2),vend_nothing, 1),
      (1, (1, 3), (vend_nothing, 1),vend, 5),
      (1, (1, 1), (vend_nothing, 1),vend_fail, 4),
      (1, (1, 1), (vend_nothing, 1),coin,3),
      (1, (1, 1), (vend_nothing, 1),coin,2)
    |}"
    by eval
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_1_2_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_1)
    apply (simp add: ffilter_def Set.filter_def fset_both_sides Abs_fset_inverse)
    apply standard
     prefer 2
     apply (simp add: choices)
    apply clarify
    apply simp
    apply (case_tac "a = 1")
     apply (case_tac "aa = 3")
    using choices apply auto[1]
     apply (case_tac "aa = 1")
      apply (case_tac "ba = 4")
    using choices by auto
qed

lemma coin_lt_vend_nothing: "coin < vend_nothing"
  by (simp add: transitions less_transition_ext_def)

lemma tm_drinks2: "tm drinks2 = Drinks_Machine_2.drinks2"
  by (simp add: tm_def drinks2_def Drinks_Machine_2.drinks2_def)

lemma step_merge_1_2_select: " length b = 1 \<Longrightarrow> step (tm merged_1_2) 0 Map.empty ''select'' b = Some (select, 1, [], <R 1 := hd b, R 2 := Num 0>)"
proof-
  assume premise: "length b = 1"
  have possible_steps: "possible_steps (tm merged_1_2) 0 Map.empty ''select'' b = {|(1, select)|}"
    apply (simp add: possible_steps_def ffilter_def tm_def merged_1_2_def fimage_def fset_both_sides Abs_fset_inverse)
    apply (simp add: Set.filter_def)
    apply safe
    using premise
         apply (simp_all add: transitions)
    by force
  show ?thesis
    using premise
    apply (simp add: step_def possible_steps select_def)
    apply (rule ext)
    by (simp add: hd_input2state)
qed

lemma step_merge_1_2_vend_nothing: "\<nexists>n. ra (R 2) = Some (Num n) \<Longrightarrow>
       step (tm merged_1_2) 1 ra ''vend'' [] = Some (vend_nothing, 1, [], ra)"
proof-
  assume premise: "\<nexists>n. ra (R 2) = Some (Num n)"
  have possible_steps: "possible_steps (tm merged_1_2) 1 ra ''vend'' [] = {|(1, vend_nothing)|}"
    apply (case_tac "ra (R 2)")
    apply (simp add: possible_steps_def ffilter_def tm_def merged_1_2_def fimage_def)
    apply (simp add: fset_both_sides Abs_fset_inverse)
     apply (simp add: Set.filter_def)
     apply (simp add: transitions)
     apply force
    apply (case_tac a)
    using premise apply simp
    apply (simp add: possible_steps_def ffilter_def tm_def merged_1_2_def fimage_def)
    apply (simp add: fset_both_sides Abs_fset_inverse)
     apply (simp add: Set.filter_def)
     apply (simp add: transitions)
    by force
  show ?thesis
    apply (simp add: step_def possible_steps)
    apply (simp add: vend_nothing_def)
    apply (rule ext)
    by simp
qed

lemma possible_steps_merge_coin: "length i = 1 \<Longrightarrow> possible_steps (tm merged_1_2) 1 r ''coin'' i = {|(1, coin)|}"
  apply (simp add: possible_steps_def ffilter_def tm_def merged_1_2_def fimage_def)
  apply (simp add: fset_both_sides Abs_fset_inverse)
  apply (simp add: Set.filter_def transitions)
  by force

lemma step_merge_1_2_vend: "d' (R 2) = Some (Num x1) \<Longrightarrow>
       x1 < 100 \<Longrightarrow>
       step (tm merged_1_2) 1 d' ''vend'' [] = None"

proof-
  assume premise1: "d' (R 2) = Some (Num x1)"
  assume premise2: "x1 < 100"
  have possible_steps: "possible_steps (tm merged_1_2) 1 d' ''vend'' [] = {|(1, vend_nothing), (1, vend_fail)|}"
    apply (simp add: possible_steps_def ffilter_def tm_def merged_1_2_def fimage_def)
    apply (simp add: fset_both_sides Abs_fset_inverse)
    apply (simp add: Set.filter_def)
    apply safe
           apply (simp_all add: transitions premise1 premise2)
     apply force
    using premise1 premise2
    by force
  show ?thesis
    apply (simp add: step_def possible_steps)
    by (simp add: transitions fis_singleton_def is_singleton_def)
qed

lemma step_merge_1_2_vend_2: "d' (R 2) = Some (Num n) \<Longrightarrow> n \<ge> 100 \<Longrightarrow> step (tm merged_1_2) 1 d' ''vend'' [] = None"
proof-
  assume premise1: "d' (R 2) = Some (Num n)"
  assume premise2: "n \<ge> 100"
  have possible_steps: "possible_steps (tm merged_1_2) 1 d' ''vend'' [] = {|(1, vend_nothing), (3, vend)|}"
    apply (simp add: possible_steps_def ffilter_def tm_def merged_1_2_def fimage_def)
    apply (simp add: fset_both_sides Abs_fset_inverse)
    apply (simp add: Set.filter_def)
    apply safe
           apply (simp_all add: transitions premise1 premise2)
    using premise2 apply auto[1]
    using premise2 apply auto[1]
     apply force
    using premise1 premise2
    by force
  show ?thesis
    apply (simp add: step_def possible_steps)
    by (simp add: transitions fis_singleton_def is_singleton_def)
qed

lemma gets_us_to_aux: "\<forall>r. gets_us_to 1 Drinks_Machine_2.drinks2 1 r p \<longrightarrow>
       accepts Drinks_Machine_2.drinks2 1 r p \<longrightarrow>
       posterior_sequence select_posterior (tm merged_1_2) 1 r p = select_posterior"
proof(induct p)
  case Nil
  then show ?case
    by simp
next
  case (Cons a p)
  then show ?case
    apply simp
    apply clarify
    apply (rule gets_us_to.cases)
       apply simp
      apply simp
     defer
     apply clarify
     apply (simp add: no_step_none)
    apply clarify
    apply simp

    apply (case_tac "aa = ''vend'' \<and> b = []")
     apply simp
     apply (rule accepts.cases)
       apply simp
      apply simp
     apply simp
     apply clarify
     apply (simp add: step_drinks2_vend_fail)
     apply clarify
     apply simp
     apply (case_tac "d' (R 2)")
      apply (simp add: step_merge_1_2_vend_nothing vend_nothing_posterior)

     apply (case_tac aa)
      defer
      apply (simp add: step_merge_1_2_vend_nothing vend_nothing_posterior)

     apply (case_tac "aa = ''coin'' \<and> length b = 1")
      apply (rule accepts.cases)
        apply simp
       apply simp
      apply simp
      apply (simp add: step_def)
      apply (simp add: possible_steps_merge_coin possible_steps_1 posterior_coin_first)
      apply clarify
      apply simp
      apply (simp add: possible_steps_1)
      apply clarify
      apply simp
    using no_route_from_2_to_1 apply blast
     apply (simp add: step_def drinks2_1_invalid)
    apply clarify
    apply simp
    apply (case_tac "x1 < 100")
     apply (simp add: step_merge_1_2_vend)
    by (simp add: step_merge_1_2_vend_2)
qed

lemma directly_subsumes_aux: "accepts_trace Drinks_Machine_2.drinks2 p \<Longrightarrow>
                              gets_us_to 1 Drinks_Machine_2.drinks2 0 Map.empty p \<Longrightarrow>
                              anterior_context (tm merged_1_2) p = select_posterior"
proof(induct p)
  case Nil
  then show ?case
    by (simp add: no_further_steps)
next
  case (Cons a p)
  then show ?case
    apply (case_tac a)
    apply simp
    apply (rule gets_us_to.cases)
       apply simp
      apply simp
     apply clarify
     apply simp
     apply (case_tac "step Drinks_Machine_2.drinks2 0 Map.empty aa ba = Some (select, 1, [], <R 1 := hd ba, R 2 := Num 0>)")
      prefer 2
    using step_drinks_2
      apply simp

      apply simp
     apply clarify
     apply (case_tac "aa = ''select'' \<and> length ba = 1")
      apply (simp add: anterior_context_def step_merge_1_2_select select_posterior)
      apply (simp add: accepts_trace_def)
      apply (rule accepts.cases)
        apply simp
       apply simp
      apply clarify
      apply simp
      apply clarify
      apply simp
      defer
     apply (simp add: step_def drinks2_0_invalid)
     apply clarify
     apply simp
    by (simp add: gets_us_to_aux)
qed

lemma directly_subsumes_vend_fail_vend_nothing: "directly_subsumes (tm DM_Inference.drinks2) (tm merged_1_2) 1 vend_fail vend_nothing"
  by (simp add: tm_drinks2 directly_subsumes_def directly_subsumes_aux vend_fail_subsumes_vend_nothing)

definition two_coins :: iEFSM where
  "two_coins = {|(1, (1, 1), vend_fail), (0, (0, 1), select), (2, (1, 1), coin), (3, (1, 1), coin), (5, (1, 3), vend)|}"

lemma merge_vend_nothing_vend_fail: "merge_transitions drinks2 merged_1_2 1 2 1 1 1 vend_nothing 1 vend_fail 4 null_generator null_modifier True = Some two_coins"
proof-
  have minus_1: "{((0, 1), select), ((1, 1), coin), ((1, 1), vend_fail), ((1, 3), vend)} - {((1, 1), vend_fail)} = {((0, 1), select), ((1, 1), coin), ((1, 3), vend)}"
    apply (simp add: transitions)
    by auto
  show ?thesis
    apply (simp add: merge_transitions_def easy_merge_def)
    apply (simp add: directly_subsumes_vend_fail_vend_nothing)
    apply (simp add: replace_transition_def)
    apply (simp add: finsert_def Abs_fset_inverse fset_both_sides)
    by (simp add: merged_1_2_def two_coins_def transitions)
qed

lemma merge_vend_nothing_vend: "merge_transitions DM_Inference.drinks2 merged_1_3 1 2 1 1 1 vend_nothing 1 vend 5 null_generator null_modifier True = None"
proof-
  have accepts_and_gets_us_to: " accepts_trace Drinks_Machine_2.drinks2 [(''select'', [Str ''coke'']), (''coin'', [Num 50])] \<and>
    gets_us_to 2 Drinks_Machine_2.drinks2 0 Map.empty [(''select'', [Str ''coke'']), (''coin'', [Num 50])]"
    apply standard
     apply (simp add: accepts_trace_def)
     apply (rule accepts.step)
      apply simp
      apply (simp add: step_def possible_steps_0)
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps_1)
     apply (rule accepts.base)
    apply (rule gets_us_to.step_some)
     apply (simp add: step_def possible_steps_0)
    apply (rule gets_us_to.step_some)
     apply (simp add: step_def possible_steps_1)
    by (simp add: gets_us_to.base)
  show ?thesis
  apply (simp add: merge_transitions_def easy_merge_def tm_drinks2 null_generator_def null_modifier_def)
  apply (simp add: directly_subsumes_def)
  apply standard
     apply (rule_tac x="[(''select'', [Str ''coke'']), (''coin'', [Num 50])]" in exI)
     apply (simp add: accepts_and_gets_us_to no_subsumption_vend_nothing_vend)
    apply standard
     apply (simp add: no_subsumption_vend_vend_nothing)
    apply (rule_tac x="[(''select'', [Str ''coke''])]" in exI)
    apply standard
     apply (simp add: accepts_trace_def)
     apply (rule accepts.step)
      apply simp
      apply (simp add: step_def possible_steps_0)
     apply (rule accepts.base)
    apply (rule gets_us_to.step_some)
     apply (simp add: step_def possible_steps_0)
    by (simp add: gets_us_to.base)
qed

lemma nondeterministic_pairs_two_coins: "nondeterministic_pairs two_coins = {|
      (1, (1, 1),(coin,3),coin,2),
      (1, (1, 1),(coin,2),coin,3)
|}"
proof-
  have minus_1: "{(1, vend_fail, 1::nat), (1, coin, 2), (1, coin, 3), (3, vend, 5)} - {(1, coin, 2)} = {(1, vend_fail, 1), (1, coin, 3), (3, vend, 5)}"
    apply (simp add: transitions)
    by auto
  have minus_2: "{(1, vend_fail, 1::nat), (1, coin, 2), (1, coin, 3), (3, vend, 5)} - {(1, coin, 3)} = {(1, vend_fail, 1), (1, coin, 2), (3, vend, 5)}"
    apply (simp add: transitions)
    by auto
  have minus_4: "{(1, vend_fail, 1::nat), (1, coin, 2), (1, coin, 3), (3, vend, 5)} - {(3, vend, 5)} = {(1, vend_fail, 1), (1, coin, 2), (1, coin, 3)}"
    apply (simp add: transitions)
    by auto
  have state_nondeterminism_1: "state_nondeterminism 1 {|(1, vend_fail, 1), (1, coin, 2), (1, coin, 3), (3, vend, 5)|} = {|
      (1, (3, 1),(vend, 5),coin,3),
      (1, (3, 1),(vend, 5),coin,2),
      (1, (3, 1),(vend, 5),vend_fail, 1),
      (1, (1, 3),(coin,3),vend, 5),
      (1, (1, 1),(coin,3),coin,2),
      (1, (1, 1),(coin,3),vend_fail, 1),
      (1, (1, 3),(coin,2),vend, 5),
      (1, (1, 1),(coin,2),coin,3),
      (1, (1, 1),(coin,2),vend_fail, 1),
      (1, (1, 3),(vend_fail, 1),vend, 5),
      (1, (1, 1),(vend_fail, 1),coin,3),
      (1, (1, 1),(vend_fail, 1),coin,2)
    |}"
    apply (simp add: state_nondeterminism_def fimage_def)
    apply (simp add: minus_1 minus_2 minus_4)
    by auto
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def two_coins_def fimage_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_1)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply safe
    by (simp_all add: choices)
qed

lemma coin_lt_vend_fail: "coin < vend_fail"
  by (simp add: transitions less_transition_ext_def)

lemma subsumes_coin_coin: "subsumes c coin coin"
  apply (simp add: subsumes_def)
  by (simp add: guard_coin)

lemma merge_coin_coin: "merge_transitions DM_Inference.drinks2 two_coins 1 2 1 1 1 coin 2 coin 3 null_generator null_modifier True = Some basically_drinks"
proof-
  have set_filter: "ffilter (\<lambda>x. snd x \<noteq> ((1, 1), coin)) two_coins = {|(1, (1, 1), vend_fail), (0, (0, 1), select), (5, (1, 3), vend)|}"
    apply (simp add: ffilter_def Set.filter_def two_coins_def)
    apply (simp add: fset_both_sides Abs_fset_inverse)
    apply (safe)
    by (simp_all add: transitions)
  have easy_merge: "easy_merge DM_Inference.drinks2 two_coins 1 2 1 1 1 coin 2 coin 3 null_generator = Some basically_drinks"
    apply (simp add: easy_merge_def null_generator_def directly_subsumes_def subsumes_coin_coin)
    by (simp add: replace_transition_def set_filter basically_drinks_def)
  show ?thesis
    by (simp add: merge_transitions_def easy_merge)
qed

lemma nondetermnistic_pairs_basically_drinks: "nondeterministic_pairs basically_drinks = {||}"
proof-
  have minus_1: "{(1, coin, 2), (1, vend_fail, 1), (3, vend, 5)} - {(1, vend_fail, 1)} = {(1, coin, 2), (3, vend, 5)}"
    apply (simp add: transitions)
    by auto
  have minus_2: "{(1, coin, 2), (1, vend_fail, 1), (3, vend, 5)} - {(3, vend, 5)} = {(1, coin, 2), (1, vend_fail, 1)}"
    apply (simp add: transitions)
    by auto
  have state_nondetermininism:  "state_nondeterminism 1 {|(1, coin, 2), (1, vend_fail, 1), (3, vend, 5)|} = {|
(1, (3, 1),(vend, 5),vend_fail, 1),
(1, (3, 1),(vend, 5),coin,2),
(1, (1, 3),(vend_fail, 1),vend, 5),
(1, (1, 1),(vend_fail, 1),coin,2),
(1, (1, 3),(coin,2),vend, 5),
(1, (1, 1),(coin,2),vend_fail, 1)
|}"
    apply (simp add: state_nondeterminism_def fimage_def)
    apply (simp add: minus_1 minus_2)
    by auto
  show ?thesis
    apply (simp add: nondeterministic_pairs_def fimage_def S_def basically_drinks_def outgoing_transitions_def state_nondetermininism)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply clarify
    apply simp
    using choice_symmetry no_choice_coin_vend no_choice_vend_fail_coin no_choice_vend_vend_fail by blast
qed

lemma score_2: "sorted_list_of_fset (score basically_drinks naive_score) = []"
proof-
  have ffilter: "ffilter (\<lambda>(x, y). x < y) (Inference.S basically_drinks |\<times>| Inference.S basically_drinks) =
    {|(0, 1), (0, 3), (1, 3)|}"
    apply (simp add: S_def basically_drinks_def)
    apply (simp add: fprod_def ffilter_def Abs_fset_inverse fset_both_sides)
    apply (simp add: Set.filter_def)
    by auto
  have score: "score basically_drinks naive_score = {||}"
    apply (simp add: score_def ffilter)
    apply (simp add: outgoing_transitions_def basically_drinks_def fimage_def)
    apply (simp add: naive_score_empty set_equiv)
    apply (simp add: naive_score_def fprod_def)
    by (simp add: transitions Abs_fset_inverse)
  show ?thesis
    by (simp add: score sorted_list_of_fset_def)
qed

lemma possible_steps_select_dm_2:  "possible_steps (tm DM_Inference.drinks2) 0 Map.empty ''select'' [Str ''coke''] = {|(1, select)|}"
  by eval

lemma consistent_posterior_vend_nothing: "consistent c \<Longrightarrow> consistent (posterior c vend_nothing)"
  apply (simp add: posterior_def vend_nothing_def remove_input_constraints_def consistent_def)
  apply clarify
  apply (rule_tac x=s in exI)
  apply clarify
  apply (case_tac "r = V (R 1)")
   apply simp
  apply simp
  using consistent_empty_4 by blast

lemma aux1: "c r \<noteq> Undef \<and> gval (cexp2gexp r (c r)) s \<noteq> Some True \<Longrightarrow>
       (r = V (R 2) \<longrightarrow>
             and (cexp.Lt (Num 100)) (c (V (R 2))) \<noteq> Undef \<and>
             gval (cexp2gexp (V (R 2)) (and (cexp.Lt (Num 100)) (c (V (R 2))))) s \<noteq> Some True) \<and>
            (r \<noteq> V (R 2) \<longrightarrow> c r \<noteq> Undef \<and> gval (cexp2gexp r (c r)) s \<noteq> Some True)"
  apply simp
  apply (case_tac "r = V (R 2)")
   apply simp
   apply (case_tac "c (V (R 2))")
         apply simp
        apply (simp add: option.case_eq_if)
       apply simp
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some (Num 100)) (s (R 2))")
        apply simp
       apply simp
      apply simp
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some (Num 100)) (s (R 2))")
       apply simp
      apply simp
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (s (R 2))")
       apply simp
      apply simp
     apply simp
     apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some (Num 100)) (s (R 2))")
      apply simp
     apply simp
     apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (s (R 2)) (Some x5)")
      apply simp
     apply simp
    apply simp
    apply (case_tac "gval (cexp2gexp (V (R 2)) x6) s")
     apply simp
     apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some (Num 100)) (s (R 2))")
      apply simp
     apply simp
    apply simp
  apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some (Num 100)) (s (R 2))")
     apply simp
    apply simp
   apply simp
   apply (case_tac "gval (cexp2gexp (V (R 2)) x71) s")
    apply simp
    apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some (Num 100)) (s (R 2))")
     apply simp
    apply simp
   apply simp
   apply (case_tac "gval (cexp2gexp (V (R 2)) x72) s")
    apply simp
    apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some (Num 100)) (s (R 2))")
     apply simp
    apply simp
   apply simp
   apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some (Num 100)) (s (R 2))")
    apply simp
   apply simp
  by simp

lemma inconsistent_c: "\<not> consistent c \<Longrightarrow>
    \<not> consistent (\<lambda>r. and (if r = V (R 2) then snd (V (R 2), cexp.Lt (Num 100)) else cexp.Bc True) (c r))"
  apply (simp add: consistent_def)
  using aux1
  by blast

lemma inconsistent_posterior_vend_fail: "\<not> consistent c \<Longrightarrow> \<not>consistent (posterior c vend_fail)"
  apply (simp add: posterior_def vend_fail_def Let_def inconsistent_c)
  by (simp add: inconsistent_false)

lemma vend_nothing_subsumes_vend_fail: "subsumes c vend_nothing vend_fail"
  apply (simp add: subsumes_def)
  apply (standard, simp add: transitions)+
   apply clarify
   apply (case_tac "r = V (R 2)")
    apply simp
    apply clarify
    apply (case_tac "ValueLt (Some i) (Some (Num 100))")
     apply simp
    apply simp
    apply (case_tac "cval (c (V (R 2))) i")
     apply simp
    apply simp
   apply simp
   apply clarify
   apply (case_tac "cval (c r) i")
    apply simp
   apply simp
  apply standard
   apply (simp add: transitions)
  apply standard
   defer
   apply (case_tac "consistent c")
    apply (simp add: consistent_posterior_vend_nothing)
   apply (simp add: inconsistent_posterior_vend_fail)

  apply clarify
  apply (case_tac "consistent (\<lambda>r. and (if r = V (R 2) then snd (V (R 2), cexp.Lt (Num 100)) else cexp.Bc True) (c r))")
  apply (simp add: posterior_def vend_nothing_def remove_input_constraints_def vend_fail_def)
   apply (case_tac "ValueLt (Some i) (Some (Num 100))")
    apply auto[1]
   apply auto[1]
  by (simp add: posterior_def vend_nothing_def remove_input_constraints_def vend_fail_def)

lemma directly_subsumes_vend_nothing_vend_fail: "directly_subsumes (tm DM_Inference.drinks2) (tm merged_1_2) 2 vend_nothing vend_fail"
  by (simp add: directly_subsumes_def vend_nothing_subsumes_vend_fail)

definition "merged_wrong_vends = {|(5, (1, 3), vend), (3, (1, 1), coin), (2, (1, 1), coin), (0, (0, 1), select), (4, (1, 1), vend_nothing)|}"

lemma merge_vend_fail_vend_nothing: "merge_transitions DM_Inference.drinks2 merged_1_2 2 1 1 1 1 vend_fail 4 vend_nothing 1 null_generator null_modifier
                     True = Some merged_wrong_vends"
  apply (simp add: merge_transitions_def easy_merge_def null_generator_def null_modifier_def)
  apply (simp add: directly_subsumes_vend_fail_vend_nothing directly_subsumes_vend_nothing_vend_fail)
  by eval

lemma nondeterministic_pairs_merged_wrong_vends: "nondeterministic_pairs merged_wrong_vends = 
{|
  (1, (1, 3), (vend_nothing, 4),vend, 5),
  (1, (1, 1),(coin,2),coin,3),
  (1, (1, 1),(coin,3),coin,2),
  (1, (3, 1),(vend, 5),vend_nothing, 4)
|}"
proof-
  have state_nondeterminism_1: "state_nondeterminism 1 {|(3, vend, 5), (1, coin, 3), (1, coin, 2), (1, vend_nothing, 4)|} = {|
      (1, (1, 1), (vend_nothing, 4),coin,2),
      (1, (1, 1), (vend_nothing, 4),coin,3),
      (1, (1, 3), (vend_nothing, 4),vend, 5),
      (1, (1, 1),(coin,2),vend_nothing, 4),
      (1, (1, 1),(coin,2),coin,3),
      (1, (1, 3),(coin,2),vend, 5),
      (1, (1, 1),(coin,3),vend_nothing, 4),
      (1, (1, 1),(coin,3),coin,2),
      (1, (1, 3),(coin,3),vend, 5),
      (1, (3, 1),(vend, 5),vend_nothing, 4),
      (1, (3, 1),(vend, 5),coin,2),
      (1, (3, 1),(vend, 5),coin,3)
    |}"
    by eval
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_wrong_vends_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_1)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply standard
     prefer 2
     apply (simp add: choices)
    apply clarify
    apply (case_tac "a = 1")
     apply (case_tac "aa = 1")
      apply (case_tac "b = 1")
    using choices by auto
qed

definition "merged_1_3_2 = {|(5, (1, 1),
    vend),
   (3, (1, 1),
    coin),
   (2, (1, 1),
    coin),
   (0, (0, 1), select),
   (4, (1, 1), vend_nothing)|}"

lemma merge_1_3_2: "merge_states 3 1 merged_wrong_vends = merged_1_3_2 \<and> merge_states 1 3 merged_wrong_vends = merged_1_3_2"
  by eval

lemma possible_steps_coin_dm_2: "possible_steps (tm drinks2) 1 r ''coin'' [Num n] = {|(2, coin)|}"
    apply (simp add: possible_steps_def drinks2_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse tm_def)
    apply (simp add: Set.filter_def)
    apply safe
           apply (simp_all add: transitions)
  by force

lemma no_direct_subsumption_vend_nothing_vend: "\<not> directly_subsumes (tm DM_Inference.drinks2) (tm merged_1_3_2) 2 vend_nothing vend"
    apply (simp add: directly_subsumes_def)
    apply (rule_tac x="[(''select'', [Str ''coke'']), (''coin'', [Num 50])]" in exI)
    apply standard
     apply (simp add: accepts_trace_def)
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps_select_dm_2)
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps_coin_dm_2)
     apply (rule accepts.base)
    apply standard
    apply (rule gets_us_to.step_some)
      apply (simp add: step_def possible_steps_select_dm_2)
    apply (rule gets_us_to.step_some)
      apply (simp add: step_def possible_steps_coin_dm_2)
     apply (simp add: gets_us_to.base)
    using no_subsumption_vend_nothing_vend by blast

lemma cant_merge_vend_nothing_vend: "merge_transitions DM_Inference.drinks2 merged_1_3_2 2 2 (leaves 5 merged_1_3_2) (arrives 5 merged_1_3_2)
                     (arrives 4 merged_1_3_2) vend 5 vend_nothing 4 null_generator null_modifier True = None"
proof-
  show ?thesis
    apply (simp add: merge_transitions_def easy_merge_def null_generator_def null_modifier_def)
    apply (simp add: no_direct_subsumption_vend_nothing_vend)
    apply (simp add: directly_subsumes_def)
    apply (rule_tac x="[(''select'', [Str ''coke'']), (''coin'', [Num 50])]" in exI)
    apply standard
     apply (simp add: accepts_trace_def)
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps_select_dm_2)
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps_coin_dm_2)
     apply (rule accepts.base)
    apply standard
    apply (rule gets_us_to.step_some)
      apply (simp add: step_def possible_steps_select_dm_2)
    apply (rule gets_us_to.step_some)
      apply (simp add: step_def possible_steps_coin_dm_2)
     apply (simp add: gets_us_to.base)
    by (simp add: no_subsumption_vend_vend_nothing)
qed

definition "merged_3_2 = {|(5, (1, 3),
    vend),
   (3, (1, 1),
    coin),
   (2, (1, 1),
    coin),
   (0, (0, 1), select),
   (4, (1, 1), vend_nothing)|}"

definition "merged_3_2_coins = {|(4, (1, 1), vend_nothing),
   (0, (0, 1), select),
   (5, (1, 3),
    vend),
   (3, (1, 1),
    coin)|}"

lemma merge_3_2_coins: "merge_transitions DM_Inference.drinks2 merged_3_2 (leaves 3 DM_Inference.drinks2) (leaves 2 DM_Inference.drinks2)
                     (leaves 3 merged_3_2) (arrives 3 merged_3_2) (arrives 2 merged_3_2) coin 3 coin 2 null_generator null_modifier True = Some merged_3_2_coins"
  apply (simp add: merge_transitions_def easy_merge_def null_generator_def null_modifier_def)
  apply (simp add: directly_subsumes_def subsumes_coin_coin)
  by eval

lemma nondeterministic_pairs_merged_3_2_coins: "nondeterministic_pairs merged_3_2_coins = {|
      (1, (3, 1),(vend, 5),vend_nothing, 4),
      (1, (1, 3), (vend_nothing, 4),vend, 5)
|}"
proof-
  have state_nondeterminism_1:  "state_nondeterminism 1 {|(1, vend_nothing, 4), (3, vend, 5), (1, coin, 3)|} = {|
      (1, (1, 3),(coin,3),vend, 5),
      (1, (1, 1),(coin,3),vend_nothing, 4),
      (1, (3, 1),(vend, 5),coin,3),
      (1, (3, 1),(vend, 5),vend_nothing, 4),
      (1, (1, 1), (vend_nothing, 4),coin,3),
      (1, (1, 3), (vend_nothing, 4),vend, 5)
    |}"
    by eval
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_3_2_coins_def )
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_1)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply safe
    by (simp_all add: choices)
qed

definition "merged_4_5 = {|(4, (1, 1), vend_nothing),
   (0, (0, 1), select),
   (5, (1, 1), vend),
   (3, (1, 1), coin)|}"

lemma merged_4_5:  "merge_states (arrives 4 merged_3_2_coins) (arrives 5 merged_3_2_coins) merged_3_2_coins = merged_4_5 \<and>
                    merge_states (arrives 5 merged_3_2_coins) (arrives 4 merged_3_2_coins) merged_3_2_coins = merged_4_5"
  by eval

lemma cant_merge_vends_2: "merge_transitions DM_Inference.drinks2 merged_4_5 (leaves 5 DM_Inference.drinks2) (leaves 4 DM_Inference.drinks2)
                     (leaves 5 merged_4_5) (arrives 5 merged_4_5) (arrives 4 merged_4_5) vend 5 vend_nothing 4 null_generator null_modifier
                     True = None"
proof-
  have leaves_5: "leaves 5 DM_Inference.drinks2 = 2"
    by eval
  have leaves_4: "leaves 4 DM_Inference.drinks2 = 2"
    by eval
  have no_direct_subsumption_vend_nothing_vend: "\<not> directly_subsumes (tm DM_Inference.drinks2) (tm merged_4_5) 2 vend_nothing vend"
    apply (simp add: directly_subsumes_def)
    apply (rule_tac x="[(''select'', [Str ''coke'']), (''coin'', [Num 50])]" in exI)
    apply standard
     apply (simp add: accepts_trace_def)
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps_select_dm_2)
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps_coin_dm_2)
     apply (rule accepts.base)
    apply standard
    apply (rule gets_us_to.step_some)
      apply (simp add: step_def possible_steps_select_dm_2)
    apply (rule gets_us_to.step_some)
      apply (simp add: step_def possible_steps_coin_dm_2)
     apply (simp add: gets_us_to.base)
  by (simp add: no_subsumption_vend_nothing_vend)
  show ?thesis
    apply (simp add: merge_transitions_def easy_merge_def null_generator_def null_modifier_def leaves_5 leaves_4)
    apply (simp add: no_direct_subsumption_vend_nothing_vend)
    apply (simp add: directly_subsumes_def)
    apply (rule_tac x="[(''select'', [Str ''coke'']), (''coin'', [Num 50])]" in exI)
    apply standard
     apply (simp add: accepts_trace_def)
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps_select_dm_2)
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps_coin_dm_2)
     apply (rule accepts.base)
    apply standard
    apply (rule gets_us_to.step_some)
      apply (simp add: step_def possible_steps_select_dm_2)
    apply (rule gets_us_to.step_some)
      apply (simp add: step_def possible_steps_coin_dm_2)
     apply (simp add: gets_us_to.base)
    by (simp add: no_subsumption_vend_vend_nothing)
qed

lemma cant_merge_vends_3: "merge_transitions DM_Inference.drinks2 merged_4_5 (leaves 4 DM_Inference.drinks2) (leaves 5 DM_Inference.drinks2)
                     (leaves 4 merged_4_5) (arrives 4 merged_4_5) (arrives 5 merged_4_5) vend_nothing 4 vend 5 null_generator null_modifier
                     True = None"
proof-
  have leaves_5: "leaves 5 DM_Inference.drinks2 = 2"
    by eval
  have leaves_4: "leaves 4 DM_Inference.drinks2 = 2"
    by eval
  have no_direct_subsumption_vend_nothing_vend: "\<not> directly_subsumes (tm DM_Inference.drinks2) (tm merged_4_5) 2 vend_nothing vend"
    apply (simp add: directly_subsumes_def)
    apply (rule_tac x="[(''select'', [Str ''coke'']), (''coin'', [Num 50])]" in exI)
    apply standard
     apply (simp add: accepts_trace_def)
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps_select_dm_2)
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps_coin_dm_2)
     apply (rule accepts.base)
    apply standard
    apply (rule gets_us_to.step_some)
      apply (simp add: step_def possible_steps_select_dm_2)
    apply (rule gets_us_to.step_some)
      apply (simp add: step_def possible_steps_coin_dm_2)
     apply (simp add: gets_us_to.base)
  by (simp add: no_subsumption_vend_nothing_vend)
  show ?thesis
    apply (simp add: merge_transitions_def easy_merge_def null_generator_def null_modifier_def leaves_5 leaves_4)
    apply (simp add: no_direct_subsumption_vend_nothing_vend)
    apply (simp add: directly_subsumes_def)
    apply (rule_tac x="[(''select'', [Str ''coke'']), (''coin'', [Num 50])]" in exI)
    apply standard
     apply (simp add: accepts_trace_def)
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps_select_dm_2)
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps_coin_dm_2)
     apply (rule accepts.base)
    apply standard
    apply (rule gets_us_to.step_some)
      apply (simp add: step_def possible_steps_select_dm_2)
    apply (rule gets_us_to.step_some)
      apply (simp add: step_def possible_steps_coin_dm_2)
     apply (simp add: gets_us_to.base)
    by (simp add: no_subsumption_vend_vend_nothing)
qed

lemma cant_merge_vends_merged_1_3: "merge_transitions DM_Inference.drinks2 merged_1_3 2 1 1 1 1 vend 5 vend_nothing 1 null_generator null_modifier True = None"
proof-
  have no_direct_subsumption_vend_vend_nothing: "\<not> directly_subsumes (tm DM_Inference.drinks2) (tm merged_1_3) 1 vend vend_nothing"
    apply (simp add: directly_subsumes_def accepts_trace_def)
    apply (rule_tac x="[(''select'', [Str ''coke''])]" in exI)
    apply standard
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps_select_dm_2)
     apply (simp add: accepts.base)
    apply standard
     apply (rule gets_us_to.step_some)
      apply (simp add: possible_steps_select_dm_2 step_def)
     apply (simp add: gets_us_to.base)
    by (simp add: no_subsumption_vend_vend_nothing)
  show ?thesis
    apply (simp add: merge_transitions_def easy_merge_def null_generator_def null_modifier_def)
    apply (simp add: no_direct_subsumption_vend_vend_nothing)
    apply (simp add: directly_subsumes_def accepts_trace_def)
    apply (rule_tac x="[(''select'', [Str ''coke'']), (''coin'', [Num 50])]" in exI)
    apply standard
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps_select_dm_2)
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps_coin_dm_2)
     apply (simp add: accepts.base)
    apply standard
     apply (rule gets_us_to.step_some)
      apply (simp add: possible_steps_select_dm_2 step_def)
     apply (rule gets_us_to.step_some)
      apply (simp add: step_def possible_steps_coin_dm_2)
     apply (simp add: gets_us_to.base)
    by (simp add: no_subsumption_vend_nothing_vend)
qed

lemma gets_us_to_2_dm_2: "accepts_trace (tm DM_Inference.drinks2) [(''select'', [Str ''coke'']), (''coin'', [Num 50])] \<and>
    gets_us_to 2 (tm DM_Inference.drinks2) 0 Map.empty [(''select'', [Str ''coke'']), (''coin'', [Num 50])]"
  apply standard
  apply (simp add: accepts_trace_def)
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps_select_dm_2)
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps_coin_dm_2)
     apply (simp add: accepts.base)
     apply (rule gets_us_to.step_some)
      apply (simp add: possible_steps_select_dm_2 step_def)
     apply (rule gets_us_to.step_some)
      apply (simp add: step_def possible_steps_coin_dm_2)
  by (simp add: gets_us_to.base)

lemma gets_us_to_1_dm_2: "accepts_trace (tm DM_Inference.drinks2) [(''select'', [Str ''coke''])] \<and>
    gets_us_to 1 (tm DM_Inference.drinks2) 0 Map.empty [(''select'', [Str ''coke''])]"
  apply standard
  apply (simp add: accepts_trace_def)
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps_select_dm_2)
     apply (simp add: accepts.base)
     apply (rule gets_us_to.step_some)
      apply (simp add: possible_steps_select_dm_2 step_def)
  by (simp add: gets_us_to.base)

lemma cant_merge_vends_merged_1_3_2: "merge_transitions DM_Inference.drinks2 (merge_states 1 3 merged_1_2) (leaves 1 DM_Inference.drinks2)
                     (leaves 5 DM_Inference.drinks2) (leaves 1 (merge_states 1 3 merged_1_2)) (arrives 1 (merge_states 1 3 merged_1_2))
                     (arrives 5 (merge_states 1 3 merged_1_2)) vend_nothing 1 vend 5 null_generator null_modifier True = None"
proof-
  have merge_1_3: "merge_states 1 3 merged_1_2 = {|
    (0, (0, 1), select),
    (1, (1, 1), vend_nothing),
    (2, (1, 1), coin),
    (3, (1, 1), coin),
    (4, (1, 1), vend_fail),
    (5, (1, 1), vend)
  |}"
    by eval
  have leaves_5:  "leaves 5 DM_Inference.drinks2 = 2"
    by eval
  have leaves_1: "leaves 1 DM_Inference.drinks2 = 1"
    by eval
  have no_direct_subsumption_1: "\<not> directly_subsumes (tm DM_Inference.drinks2)
        (tm {|(0, (0, 1), select), (1, (1, 1), vend_nothing), (2, (1, 1), coin), (3, (1, 1), coin), (4, (1, 1), vend_fail),
              (5, (1, 1), vend)|})
        (leaves 5 DM_Inference.drinks2) vend_nothing vend"
    apply (simp add: directly_subsumes_def leaves_5)
    apply (rule_tac x="[(''select'', [Str ''coke'']), (''coin'', [Num 50])]" in exI)
    by (simp add: gets_us_to_2_dm_2 no_subsumption_vend_nothing_vend)
  show ?thesis
    apply (simp add: merge_1_3 Let_def merge_transitions_def easy_merge_def null_generator_def null_modifier_def)
    apply (simp add: no_direct_subsumption_1)
    apply (simp add: directly_subsumes_def leaves_1)
    apply (rule_tac x="[(''select'', [Str ''coke''])]" in exI)
    by (simp add: gets_us_to_1_dm_2 no_subsumption_vend_vend_nothing)
qed

lemma next_fmax: "fMax ({|(1::nat, (1::nat, 1::nat), (vend_fail, 4::nat), vend_nothing, 1::nat), (1, (1, 1), (coin, 3), coin, 2), (1, (1, 1), (coin, 2), coin, 3),
                        (1, (1, 3), (vend_nothing, 1), vend, 5), (1, (1, 1), (vend_nothing, 1), vend_fail, 4)|} |-|
                      {|(1, (1, 3), (vend_nothing, 1), vend, 5)|}) = (1, (1, 1),
  (vend_fail, 4), vend_nothing, 1)"
  by eval

lemma next_fmax_2: "fMax
                     ({|(1::nat, (1::nat, 3::nat), (vend_nothing, 4::nat), vend, 5::nat), (1, (1, 1), (coin, 2), coin, 3), (1, (1, 1), (coin, 3), coin, 2),
                        (1, (3, 1), (vend, 5), vend_nothing, 4)|} |-|
                      {|(1, (3, 1), (vend, 5), vend_nothing, 4)|}) = (1, (1, 3), (vend_nothing, 4), vend, 5)"
  by eval

lemma cant_merge_vend_nothing_vend_2: "merge_transitions DM_Inference.drinks2 merged_1_3_2 2 2 (leaves 4 merged_1_3_2) (arrives 4 merged_1_3_2)
                     (arrives 5 merged_1_3_2) vend_nothing 4 vend 5 null_generator null_modifier True = None"
proof-
  show ?thesis
    apply (simp add: merge_transitions_def easy_merge_def null_generator_def null_modifier_def)
    apply (simp add: no_direct_subsumption_vend_nothing_vend)
    apply (simp add: directly_subsumes_def)
    apply (rule_tac x="[(''select'', [Str ''coke'']), (''coin'', [Num 50])]" in exI)
    by (simp add: gets_us_to_2_dm_2 no_subsumption_vend_vend_nothing)
qed

lemma set_equiv_elem: "(s \<noteq> s') = (\<exists>e. (e \<in> s \<and> e \<notin> s') \<or> (e \<in> s' \<and> e \<notin> s))"
  by auto

lemma drinks2_neq_basically_drinks: "drinks2 \<noteq> basically_drinks"
  apply (simp add: drinks2_def basically_drinks_def set_equiv)
  apply (simp add: set_equiv_elem)
  apply (rule_tac x=3 in exI)
  by simp

lemma next_fmax_3:  "fMax ({|(1::nat, (1::nat, 3::nat), (vend_nothing, 4::nat), vend, 5::nat), (1, (1, 1), (coin, 2), coin, 3), (1, (1, 1), (coin, 3), coin, 2)|} |-|
                      {|max (1, (1, 3), (vend_nothing, 4), vend, 5)
                         (max (1, (1, 1), (coin, 2), coin, 3) (1, (1, 1), (coin, 3), coin, 2))|}) = (1, (1, 1), (coin, 3), coin, 2)"
  by eval

lemma minus_simp: "{|(1, (1, 3), (vend_nothing, 4), vend, 5), (1, (1, 1), (coin, 2), coin, 3), (1, (1, 1), (coin, 3), coin, 2),
         (1, (3, 1), (vend, 5), vend_nothing, 4)|} |-|
       {|(1, (3, 1), (vend, 5), vend_nothing, 4)|} = {|(1, (1, 3), (vend_nothing, 4), vend, 5), (1, (1, 1), (coin, 2), coin, 3), (1, (1, 1), (coin, 3), coin, 2)|}"
  apply (simp add: transitions)
  by auto

lemma "infer drinks2 naive_score null_generator null_modifier = basically_drinks"
proof-
  have leaves_1_drinks2: "leaves 1 drinks2 = 1"
  proof-
    have set_filter: "Set.filter (\<lambda>x. \<exists>a b ba. x = (1, (a, b), ba)) (fset DM_Inference.drinks2) = {(1, (1, 1), vend_nothing)}"
      apply (simp add: Set.filter_def drinks2_def)
      by auto
    show ?thesis
      by (simp add: leaves_def ffilter_def fthe_elem_def Abs_fset_inverse set_filter)
  qed
  have leaves_4_drinks2: "leaves 4 drinks2 = 2"
  proof-
    have set_filter: "Set.filter (\<lambda>x. \<exists>a b ba. x = (4, (a, b), ba)) (fset drinks2) = {(4, (2, 2), vend_fail)}"
      apply (simp add: Set.filter_def drinks2_def)
      by auto
    show ?thesis
      by (simp add: leaves_def ffilter_def fthe_elem_def Abs_fset_inverse set_filter)
  qed
  have leaves_5_drinks2: "leaves 5 drinks2 = 2"
  proof-
    have set_filter: "Set.filter (\<lambda>x. \<exists>a b ba. x = (5, (a, b), ba)) (fset drinks2) = {(5, (2, 3), vend)}"
      apply (simp add: Set.filter_def drinks2_def)
      by auto
    show ?thesis
      by (simp add: leaves_def ffilter_def fthe_elem_def Abs_fset_inverse set_filter)
  qed
  have minus_1: "{|(1, (1, 1), (coin, 2), coin, 3), (1, (1, 3), (vend_nothing, 1), vend, 5), (1, (1, 1), (vend_nothing, 1), vend_fail, 4)|} |-|
                      {|(1, (1, 3), (vend_nothing, 1), vend, 5)|} = {|(1, (1, 1), (coin, 2), coin, 3), (1, (1, 1), (vend_nothing, 1), vend_fail, 4)|}"
    apply (simp add: transitions)
    by auto
  have leaves_2_drinks2: "leaves 2 drinks2 = 1"
  proof-
    have set_filter: "Set.filter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) (fset drinks2) = {(2, (1, 2), coin)}"
      apply (simp add: Set.filter_def drinks2_def)
      by auto
    show ?thesis
      by (simp add: leaves_def ffilter_def fthe_elem_def Abs_fset_inverse set_filter)
  qed
  have leaves_3_drinks2: "leaves 3 drinks2 = 2"
  proof-
    have set_filter: "Set.filter (\<lambda>x. \<exists>a b ba. x = (3, (a, b), ba)) (fset drinks2) = {(3, (2, 2), coin)}"
      apply (simp add: Set.filter_def drinks2_def)
      by auto
    show ?thesis
      by (simp add: leaves_def ffilter_def fthe_elem_def Abs_fset_inverse set_filter)
  qed
  have arrives_1_merged_1_2: "arrives 1 merged_1_2 = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (1, (a, b), ba)) merged_1_2 = {|(1, (1,1), vend_nothing)|}"
      apply (simp add: ffilter_def Set.filter_def merged_1_2_def fset_both_sides Abs_fset_inverse)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_5_merged_1_2: "arrives 5 merged_1_2 = 3"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (5, (a, b), ba)) merged_1_2 = {|(5, (1,3), vend)|}"
      apply (simp add: ffilter_def Set.filter_def merged_1_2_def fset_both_sides Abs_fset_inverse)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have merge_states_1_3: "merge_states 3 1 merged_1_2 = merged_1_3"
    by (simp add: merge_states_def merge_states_aux_def merged_1_2_def merged_1_3_def)
  have leaves_1_merged_1_3: "leaves 1 merged_1_3 = 1 \<and> arrives 1 merged_1_3 = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (1, (a, b), ba)) merged_1_3 = {|(1, (1, 1), vend_nothing)|}"
      apply (simp add: ffilter_def Set.filter_def merged_1_3_def fset_both_sides Abs_fset_inverse)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def arrives_def ffilter)
  qed
  have arrives_5_merged_1_3: "arrives 5 merged_1_3 = 1 \<and> leaves 5 merged_1_3 = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (5, (a, b), ba)) merged_1_3 = {|(5, (1, 1), vend)|}"
      apply (simp add: ffilter_def Set.filter_def merged_1_3_def fset_both_sides Abs_fset_inverse)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def arrives_def ffilter)
  qed
  have arrives_1_merged_1_2: "leaves 1 merged_1_2 = 1\<and> arrives 1 merged_1_2 = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (1, (a, b), ba)) merged_1_2 = {|(1, (1, 1), vend_nothing)|}"
      apply (simp add: ffilter_def Set.filter_def merged_1_2_def fset_both_sides Abs_fset_inverse)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def arrives_def ffilter)
  qed
  have arrives_4_merged_1_2: "arrives 4 merged_1_2 = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (4, (a, b), ba)) merged_1_2 = {|(4, (1,1), vend_fail)|}"
      apply (simp add: ffilter_def Set.filter_def merged_1_2_def fset_both_sides Abs_fset_inverse)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_2_two_coins: "arrives 2 two_coins = 1 \<and> leaves 2 two_coins = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) two_coins = {|(2, (1, 1), coin)|}"
      apply (simp add: ffilter_def Set.filter_def two_coins_def fset_both_sides Abs_fset_inverse)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def leaves_def ffilter)
  qed
  have arrives_3_two_coins: "arrives 3 two_coins = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (3, (a, b), ba)) two_coins = {|(3, (1, 1), coin)|}"
      apply (simp add: ffilter_def Set.filter_def two_coins_def fset_both_sides Abs_fset_inverse)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have fminus: "{|(1, (1, 1), (vend_fail, 4), vend_nothing, 1), (1, (1, 1), (coin, 3), coin, 2), (1, (1, 1), (coin, 2), coin, 3),
                        (1, (1, 3), (vend_nothing, 1), vend, 5), (1, (1, 1), (vend_nothing, 1), vend_fail, 4)|} |-|
                      {|(1, (1, 3), (vend_nothing, 1), vend, 5)|} = {|(1, (1, 1), (vend_fail, 4), vend_nothing, 1), (1, (1, 1), (coin, 3), coin, 2), (1, (1, 1), (coin, 2), coin, 3),
                        (1, (1, 1), (vend_nothing, 1), vend_fail, 4)|}"
    apply (simp add: minus_fset_def fset_both_sides Abs_fset_inverse transitions)
    by auto
  have fmax: "fMax
                     {|(1::nat, (1::nat, 1::nat), (vend_fail, 4::nat), vend_nothing, 1::nat), (1, (1, 1), (coin, 3), coin, 2), (1, (1, 1), (coin, 2), coin, 3),
                       (1, (1, 1), (vend_nothing, 1), vend_fail, 4)|} = (1, (1, 1), (vend_fail, 4), vend_nothing, 1)"
    apply (simp add: transitions max_def)
    using coin_def coin_lt_vend_nothing vend_fail_def vend_fail_not_lt_vend_nothing vend_nothing_def by auto
  have arrives_4_merged_1_2:  "arrives 4 merged_1_2 = 1 \<and> leaves 4 merged_1_2 = 1"
    by eval
  have arrives_1_merged_1_2: "arrives 1 merged_1_2 = 1"
    by eval
  have merge_states_1_1: "merge_states 1 1 merged_1_2 = merged_1_2"
    apply (simp add: merge_states_def merge_states_aux_def)
    by force
  have arrives_4_merged_wrong_vends: "arrives 4 merged_wrong_vends = 1"
    by eval
  have arrives_5_merged_wrong_vends: "arrives 5 merged_wrong_vends = 3"
    by eval
  have merge_3_2: "merge_states (arrives 3 merged_wrong_vends) (arrives 2 merged_wrong_vends) merged_wrong_vends = merged_3_2"
    by eval
  show ?thesis
    apply (simp add: scoring)
    apply (simp add: merge_def)
    apply (simp only: merge_states_1_2 Let_def nondeterministic_pairs_merged_1_2)
    apply (simp add: nondeterminism_def nondeterministic_pairs_merged_1_2 del: resolve_nondeterminism.simps)
    apply (simp add: max_def arrives_1_merged_1_2 arrives_5_merged_1_2)
    apply (simp add: merge_states_1_3 leaves_1_drinks2 leaves_5_drinks2 leaves_1_merged_1_3 arrives_5_merged_1_3)
    apply (simp add: cant_merge_vends_merged_1_3 max_def arrives_1_merged_1_2 arrives_5_merged_1_2)
    apply (simp add: Let_def cant_merge_vends_merged_1_3_2 max_def next_fmax)
    apply (simp add: nondeterminism_def nondeterministic_pairs_merged_1_2)
    apply (simp add: arrives_4_merged_1_2 arrives_1_merged_1_2 leaves_4_drinks2 leaves_1_drinks2 merge_states_reflexive)
    apply (simp add: merge_vend_fail_vend_nothing nondeterminism_def nondeterministic_pairs_merged_1_2)
    apply (simp add: nondeterministic_pairs_merged_wrong_vends max_def)
    apply (simp add: arrives_5_merged_wrong_vends arrives_4_merged_wrong_vends leaves_5_drinks2 leaves_4_drinks2)
    apply (simp add: merge_1_3_2 cant_merge_vend_nothing_vend)
    apply (simp add: nondeterminism_def nondeterministic_pairs_merged_wrong_vends max_def next_fmax_2)
    apply (simp add: merge_1_3_2 arrives_5_merged_wrong_vends arrives_4_merged_wrong_vends leaves_5_drinks2 leaves_4_drinks2)
    apply (simp add: cant_merge_vend_nothing_vend_2)
    apply (simp add: nondeterminism_def nondeterministic_pairs_merged_wrong_vends max_def)
    apply (simp add: drinks2_neq_basically_drinks minus_simp)
    apply (simp add: next_fmax_3 merge_3_2 merge_3_2_coins nondeterminism_def nondeterministic_pairs_merged_3_2_coins)
    apply (simp add: max_def merged_4_5 cant_merge_vends_2 cant_merge_vends_3)
    apply (simp add: drinks2_neq_basically_drinks)
    apply (simp add: nondeterminism_def nondeterministic_pairs_merged_3_2_coins)


qed

value "iefsm2dot_str drinks2"

end