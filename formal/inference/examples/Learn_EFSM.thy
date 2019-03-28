theory Learn_EFSM
  imports "../Code_Generation"
begin

declare One_nat_def [simp del]
declare gval.simps [simp]
declare ValueEq_def [simp]

abbreviation "coke \<equiv> STR ''coke''"
abbreviation "pepsi \<equiv> STR ''pepsi''"

lemma Suc_zero_def: "Suc 0 = 1"
  by simp

abbreviation select :: "String.literal \<Rightarrow> transition" where
  "select drink \<equiv> \<lparr>Label = (STR ''select''), Arity = 1, Guard = [gexp.Eq (V (I 1)) (L ((value.Str drink)))], Outputs = [], Updates = []\<rparr>"

abbreviation coin :: "int \<Rightarrow> int \<Rightarrow> transition" where
  "coin i p \<equiv> \<lparr>Label = (STR ''coin''), Arity = 1, Guard = [gexp.Eq (V (I 1)) (L (Num i))], Outputs = [L (Num p)], Updates = []\<rparr>"

abbreviation vend :: "String.literal \<Rightarrow> transition" where
  "vend drink \<equiv> \<lparr>Label = (STR ''vend''), Arity = 0, Guard = [], Outputs = [L ((value.Str drink))], Updates = []\<rparr>"

definition pta :: iEFSM where
  "pta = {|(0, (0, 1), (select coke)),  (2, (1, 2), (coin 50 50)), (4, (2, 3), (coin 50 100)),  (5, (3, 4), (vend coke)),
                                                             (3, (1, 5), (coin 100 100)), (6, (5, 6), (vend coke)),
           (1, (0, 7), (select pepsi)), (7, (7, 8), (coin 50 50)), (8, (8, 9), (coin 50 100)),  (9, (9, 10), (vend pepsi))|}"

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

value "let relevant = filter (\<lambda>(((_, u1'), io, _), (_, u2'), io', _). io = In \<and> io' = Out \<and> (5 = u1' \<or> 9 = u1' \<or> 5 = u2' \<or> 9 = u2')) (find_intertrace_matches traces pta);
           newReg = max_reg pta + 1;
           replacements = map (\<lambda>(((t1, u1), io1, inx1), (t2, u2), io2, inx2). (((remove_guard_add_update t1 (inx1+1) newReg, u1), io1, inx1), (generalise_output t2 newReg inx2, u2), io2, inx2)) relevant;
           comparisons = zip relevant replacements;
           stripped_replacements = map strip_uids replacements;
           to_replace = filter (\<lambda>(_, s). count (strip_uids s) stripped_replacements > 1) comparisons
       in stripped_replacements"

lemma build_pta: "toiEFSM (make_pta traces {||}) = pta"
  by eval

definition filtered_pairs :: "(nat \<times> nat) set" where
  "filtered_pairs = {(9, 10), (8, 10), (8, 9), (7, 10), (7, 9), (7, 8), (6, 10), (6, 9), (6, 8), (6, 7), (5, 10), (5, 9), (5, 8), (5, 7), (5, 6), (4, 10),
  (4, 9), (4, 8), (4, 7), (4, 6), (4, 5), (3, 10), (3, 9), (3, 8), (3, 7), (3, 6), (3, 5), (3, 4), (2, 10), (2, 9), (2, 8), (2, 7), (2, 6),
  (2, 5), (2, 4), (2, 3), (1, 10), (1, 9), (1, 8), (1, 7), (1, 6), (1, 5), (1, 4), (1, 3), (1, 2), (0, 10), (0, 9), (0, 8), (0, 7), (0, 6),
  (0, 5), (0, 4), (0, 3), (0, 2), (0, 1)}"

lemma scoring_1: "sorted_list_of_fset (score pta naive_score) = [(1, 2, 7), (1, 2, 8), (1, 3, 5), (1, 3, 9), (1, 5, 9), (1, 7, 8), (2, 1, 2), (2, 1, 7), (2, 1, 8)]"
  by eval

lemmas possible_steps_fst = possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse

lemma step_pta_coin50_7: "step (tm pta) 7 r (STR ''coin'') [Num 50] = Some ((coin 50 50), 8, [Some (Num 50)], r)"
  apply (rule one_possible_step)
    apply (rule possible_steps_singleton)
    apply (simp add: Abs_ffilter Set.filter_def pta_def tm_def)
  by auto

lemma step_pta_coin50_1: "step (tm pta) 1 r (STR ''coin'') [Num 50] = Some ((coin 50 50), 2, [Some (Num 50)], r)"
  apply (rule one_possible_step)
    apply (rule possible_steps_singleton)
    apply (simp add: Abs_ffilter Set.filter_def pta_def tm_def)
  by auto

lemma step_pta_vend_5: "step (tm pta) 5 r (STR ''vend'') [] = Some ((vend coke), 6, [Some ((Str ''coke''))], r)"
  apply (rule one_possible_step)
    apply (rule possible_steps_singleton)
    apply (simp add: Abs_ffilter Set.filter_def pta_def tm_def)
  using implode_coke
  by auto

lemma step_pta_coin100_1: "step (tm pta) 1 r (STR ''coin'') [Num 100] = Some ((coin 100 100), 5, [Some (Num 100)], r)"
  apply (rule one_possible_step)
    apply (rule possible_steps_singleton)
    apply (simp add: Abs_ffilter Set.filter_def pta_def tm_def)
  by auto

lemma step_pta_coin50_2: "step (tm pta) 2 r (STR ''coin'') [Num 50] = Some ((coin 50 100), 3, [Some (Num 100)], r)"
  apply (rule one_possible_step)
    apply (rule possible_steps_singleton)
    apply (simp add: Abs_ffilter Set.filter_def pta_def tm_def)
  by auto

lemma step_pta_coin50_8: "step (tm pta) 8 r (STR ''coin'') [Num 50] = Some ((coin 50 100), 9, [Some (Num 100)], r)"
  apply (rule one_possible_step)
    apply (rule possible_steps_singleton)
    apply (simp add: Abs_ffilter Set.filter_def pta_def tm_def)
  by auto

lemma step_pta_vend_3: "step (tm pta) 3 r (STR ''vend'') [] = Some ((vend coke), 4, [Some ((Str ''coke''))], r)"
  apply (rule one_possible_step)
    apply (rule possible_steps_singleton)
    apply (simp add: Abs_ffilter Set.filter_def pta_def tm_def)
  using implode_coke
  by auto

lemma step_pta_vend_9: "step (tm pta) 9 r (STR ''vend'') [] = Some ((vend pepsi), 10, [Some ((Str ''pepsi''))], r)"
  apply (rule one_possible_step)
    apply (rule possible_steps_singleton)
    apply (simp add: Abs_ffilter Set.filter_def pta_def tm_def)
  using implode_pepsi
  by auto

definition merged_1_8 :: iEFSM where
  "merged_1_8 = {|
(0, (0, 1), (select coke)),
(1, (0, 7), (select pepsi)),
(2, (1, 2), (coin 50 50)),
(3, (1, 5), (coin 100 100)),
(4, (2, 3), (coin 50 100)),
(5, (3, 4), (vend coke)),
(6, (5, 6), (vend coke)),
(7, (7, 1), (coin 50 50)),
(8, (1, 9), (coin 50 100)),
(9, (9, 10), (vend pepsi))
|}"

definition merged_2_9 :: iEFSM where
  "merged_2_9 = {|(0, (0, 1), (select coke)), (1, (0, 7), (select pepsi)), (2, (1, 2), (coin 50 50)), (3, (1, 5), (coin 100 100)), (4, (2, 3), (coin 50 100)),
      (5, (3, 4), (vend coke)), (6, (5, 6), (vend coke)), (7, (7, 1), (coin 50 50)), (8, (1, 2), (coin 50 100)), (9, (2, 10), (vend pepsi))|}"

lemma merge_states_2_9: "merge_states 2 9 merged_1_8 = merged_2_9 \<and> merge_states 9 2 merged_1_8 = merged_2_9"
  by (simp add: merge_states_def merge_states_aux_def merged_1_8_def merged_2_9_def)

lemma no_subsumption_coin_50_100_coin_50_50: "\<not> subsumes (coin 50 100) c (coin 50 50)"
  by (simp add: subsumes_def)

lemma no_subsumption_coin_50_50_coin_50_100: "\<not> subsumes (coin 50 50) c (coin 50 100)"
  by (simp add: subsumes_def)

lemma no_subsumption_vend_coke_vend_pepsi: "\<not> subsumes (vend coke) c (vend pepsi)"
  by (simp add: subsumes_def Str_coke implode_pepsi)

lemma vend_pepsi_not_subsumes_vend_coke: "\<not> subsumes (vend pepsi) c (vend coke)"
  by (simp add: subsumes_def Str_coke implode_pepsi)

lemma step_pta_select_coke: "step (tm pta) 0 Map.empty (STR ''select'') [(Str ''coke'')] = Some ((select coke), 1, [], <>)"
  apply (rule one_possible_step)
    apply (rule possible_steps_singleton)
    apply (simp add: Abs_ffilter Set.filter_def pta_def tm_def)
  using implode_coke implode_pepsi
  by auto

definition merged_1_7 :: iEFSM where
  "merged_1_7 = {|(0, (0, 1), (select coke)), (2, (1, 2), (coin 50 50)), (4, (2, 3), (coin 50 100)),  (5, (3, 4), (vend coke)), 
                                                                   (3, (1, 5), (coin 100 100)), (6, (5, 6), (vend coke)),
                 (1, (0, 1), (select pepsi)), (7, (1, 8), (coin 50 50)), (8, (8, 9), (coin 50 100)),  (9, (9, 10), (vend pepsi))|}"

lemma merge_states_1_7: "merge_states 1 7 pta = merged_1_7"
  by (simp add: merge_states_def pta_def merge_states_aux_def merged_1_7_def)

definition merged_2_8 :: iEFSM where
  "merged_2_8 = {|(0, (0, 1), (select coke)),  (2, (1, 2), (coin 50 50)),  (4, (2, 3), (coin 50 100)),  (5, (3, 4), (vend coke)),
                                                                      (3, (1, 5), (coin 100 100)), (6, (5, 6), (vend coke)),
                   (1, (0, 1), (select pepsi)), (7, (1, 2), (coin 50 50)),  (8, (2, 9), (coin 50 100)),  (9, (9, 10), (vend pepsi))|}"

lemma merge_states_2_8: "merge_states 2 8 merged_1_7 = merged_2_8 \<and> merge_states 8 2 merged_1_7 = merged_2_8"
  by (simp add: merge_states_def merge_states_aux_def merged_1_7_def merged_2_8_def)

lemma no_choice_coin_50_50_coin_100_100: "\<not>choice (coin 50 50) (coin 100 100)"
  by (simp add: choice_def)

definition merge_2_8_no_nondet :: iEFSM where
  "merge_2_8_no_nondet = {|(0, (0, 1), (select coke)), (2, (1, 2), (coin 50 50)), (4, (2, 3), (coin 50 100)), (5, (3, 4), (vend coke)), (3, (1, 5), (coin 100 100)),
      (6, (5, 6), (vend coke)), (1, (0, 1), (select pepsi)), (7, (1, 2), (coin 50 50)), (8, (2, 9), (coin 50 100)), (9, (9, 10), (vend pepsi))|}"

definition selectGeneral :: transition where
  "selectGeneral = \<lparr>Label = (STR ''select''), Arity = 1, Guard = [], Outputs = [], Updates = [(R 1, V (I 1))]\<rparr>"

definition vend_general :: transition where
  "vend_general = \<lparr>Label = (STR ''vend''), Arity = 0, Guard = [], Outputs = [V (R 1)], Updates = []\<rparr>"

definition merged_4_10 :: iEFSM where
  "merged_4_10 = {|(0, (0, 1), (select coke)), (7, (1, 2), (coin 50 50)), (8, (2, 3), (coin 50 100)), (5, (3, 4), (vend coke)) ,
                   (1, (0, 1), (select pepsi)),                                     (9, (3, 4), (vend pepsi)), 
                                            (3, (1, 5), (coin 100 100)), (6, (5, 6), (vend coke))|}"

definition merged_vends :: iEFSM where
  "merged_vends = {|(0, (0, 1), selectGeneral), (2, (1, 2), (coin 50 50)), (4, (2, 3), (coin 50 100)), (5, (3, 4), vend_general) ,
                                            (3, (1, 5), (coin 100 100)), (6, (5, 6), vend_general)|}"

definition coinGeneral :: transition where
  "coinGeneral = \<lparr>Label = (STR ''coin''), Arity = 1, Guard = [], Outputs = [Plus (V (I 1)) (V (R 2))], Updates = [(R 2, Plus (V (I 1)) (V (R 2)))]\<rparr>"

lemma no_choice_coin_100_100_coin_50_50: "\<not>choice (coin 100 100) (coin 50 50)"
  by (simp add: choice_def)

lemma no_choice_coin_100_100_coin_50_100: "\<not>choice (coin 100 100) (coin 50 100)"
  by (simp add: choice_def)

lemma no_choice_select_coke_select_pepsi: "\<not>choice (select coke) (select pepsi)"
  by (simp add: choice_def Str_coke Str_pepsi)

lemma choice_coin_50_100_coin_50_50: "choice (coin 50 100) (coin 50 50)"
  apply (simp add: choice_def)
  by auto

lemma choice_coin_50_50_coin_50_50: "choice (coin 50 50) (coin 50 50)"
  apply (simp add: choice_def)
  by auto

lemma choice_coin_50_100_coin_50_100: "choice (coin 50 100) (coin 50 100)"
  apply (simp add: choice_def)
  by auto

lemma choice_vend_coke_vend_pepsi: "choice (vend coke) (vend pepsi)"
  by (simp add: choice_def)

lemma no_coice_vend_general_coin_100_100:  "\<not>choice vend_general (coin 100 100)"
  by (simp add: choice_def vend_general_def)

lemma no_choice_coinGeneral_vend_general: "\<not>choice coinGeneral vend_general"
  by (simp add: choice_def coinGeneral_def vend_general_def)

lemma choice_coinGeneral_coin_100_100: "choice coinGeneral (coin 100 100)"
  apply (simp add: coinGeneral_def choice_def)
  by auto

lemma no_coice_coin_100_100_vend_general: "\<not>choice (coin 100 100) vend_general"
  by (simp add: choice_def vend_general_def)

lemma choice_coin_100_100_coinGeneral: "choice (coin 100 100) coinGeneral"
  apply (simp add: coinGeneral_def choice_def)
  by auto

lemma choice_vend_general_vend_general: "choice vend_general vend_general"
  by (simp add: choice_def vend_general_def)

lemma no_choice_coin_50_100_coin_100_100: "\<not>choice (coin 50 100) (coin 100 100)"
  by (simp add: choice_def)

lemmas choices = choice_vend_general_vend_general choice_coin_100_100_coinGeneral
                 no_coice_coin_100_100_vend_general choice_coinGeneral_coin_100_100
                 no_choice_coinGeneral_vend_general no_coice_vend_general_coin_100_100
                 choice_vend_coke_vend_pepsi choice_coin_50_100_coin_50_100
                 choice_coin_50_50_coin_50_50 choice_coin_50_100_coin_50_50
                 no_choice_select_coke_select_pepsi no_choice_coin_100_100_coin_50_100
                 no_choice_coin_100_100_coin_50_50 no_choice_coin_50_50_coin_100_100 
                 no_choice_coin_50_100_coin_100_100 choice_symmetry

lemma coin_50_50_lt_coin_50_100: "(coin 50 50) < (coin 50 100)"
  by (simp add: less_transition_ext_def less_aexp_def)

lemma vend_coke_lt_vend_pepsi: "(vend coke) < (vend pepsi)"
  apply (simp add: less_transition_ext_def less_aexp_def Str_coke Str_pepsi)
  by (simp add: String.less_literal_def explode_coke explode_pepsi)

lemmas orders = vend_coke_lt_vend_pepsi coin_50_50_lt_coin_50_100

lemma merge_states_1_8: "merge_states 1 8 pta = merged_1_8"
  apply (simp add: merge_states_def merge_states_aux_def pta_def merged_1_8_def)
  by auto

lemma nondeterministic_pairs_merged_1_8: "nondeterministic_pairs merged_1_8 = {|
    (1, (9, 2), ((coin 50 100), 8), (coin 50 50), 2),
    (1, (2, 9), ((coin 50 50), 2), (coin 50 100), 8)
  |}"
proof-
  have minus_1: "{|(1, (select coke), 0), (7, (select pepsi), 1)|} |-| {|(7, (select pepsi), 1)|} = {|(1, (select coke), 0)|}"
    by auto
  have minus_2: "{|(2, (coin 50 50), 2), (5, (coin 100 100), 3), (9, (coin 50 100), 8)|} |-| {|(5, (coin 100 100), 3)|} = {|(2, (coin 50 50), 2), (9, (coin 50 100), 8)|}"
    by auto
  have minus_3: "{|(2, (coin 50 50), 2), (5, (coin 100 100), 3), (9, (coin 50 100), 8)|} |-| {|(9, (coin 50 100), 8)|} = {|(2, (coin 50 50), 2), (5, (coin 100 100), 3)|}"
    by auto
  have state_nondeterminsm_0: "state_nondeterminism 0 {|(1, (select coke), 0), (7, (select pepsi), 1)|} = {|(0, (7, 1), ((select pepsi), 1), (select coke), 0), (0, (1, 7), ((select coke), 0), (select pepsi), 1) |}"
    by (simp add: state_nondeterminism_def minus_1)
  have state_nondeterminism_1: "state_nondeterminism 1 {|(2, (coin 50 50), 2), (5, (coin 100 100), 3), (9, (coin 50 100), 8)|} = {|
   (1, (9, 5), ((coin 50 100), 8), (coin 100 100), 3),
   (1, (9, 2), ((coin 50 100), 8), (coin 50 50), 2),
   (1, (5, 9), ((coin 100 100), 3), (coin 50 100), 8),
   (1, (5, 2), ((coin 100 100), 3), (coin 50 50), 2),
   (1, (2, 9), ((coin 50 50), 2), (coin 50 100), 8),
   (1, (2, 5), ((coin 50 50), 2), (coin 100 100), 3)
   |}"
    apply (simp add: state_nondeterminism_def minus_2 minus_3)
    by auto
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_1_8_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminsm_0 state_nondeterminism_1)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply standard
     apply clarify
     apply simp
     apply (case_tac "a=0")
      apply simp
    using choice_symmetry no_choice_select_coke_select_pepsi apply blast
     apply (case_tac "a=1")
      apply simp
    using choices apply blast
     apply simp
    apply clarify
    apply simp
     apply (case_tac "a=0")
     apply simp
     apply (case_tac "a=1")
     apply simp
     apply (case_tac "ab = coin 50 50")
    using choice_def by auto
qed

lemma nondeterministic_pairs_merged_1_7: "nondeterministic_pairs merged_1_7 = {|
(1, (2, 8), ((coin 50 50), 2), (coin 50 50), 7),
(1, (8, 2), ((coin 50 50), 7), (coin 50 50), 2)
|}"
proof-
  have minus_1: "{(2, (coin 50 50), 2), (5, (coin 100 100), 3), (8, (coin 50 50), 7)} - {(5, (coin 100 100), 3)} = {(2, (coin 50 50), 2), (8, (coin 50 50), 7)}"
    by auto
  have minus_2: "{(2, (coin 50 50), 2::nat), (5, (coin 100 100), 3), (8, (coin 50 50), 7)} - {(8, (coin 50 50), 7)} = {(2, (coin 50 50), 2), (5, (coin 100 100), 3)}"
    by auto
  have state_nondeterminism_1: "state_nondeterminism 1 {|(2, (coin 50 50), 2), (5, (coin 100 100), 3), (8, (coin 50 50), 7)|} = {|
      (1, (8, 5), ((coin 50 50), 7), (coin 100 100), 3),
      (1, (8, 2), ((coin 50 50), 7), (coin 50 50), 2),
      (1, (5, 8), ((coin 100 100), 3), (coin 50 50), 7),
      (1, (5, 2), ((coin 100 100), 3), (coin 50 50), 2),
      (1, (2, 8), ((coin 50 50), 2), (coin 50 50), 7),
      (1, (2, 5), ((coin 50 50), 2), (coin 100 100), 3)
    |}"
    apply (simp add: state_nondeterminism_def fimage_def minus_1 minus_2)
    by auto
  have minus_3: "{(1, (select coke), 0), (1, (select pepsi), 1)} - {(1, (select pepsi), 1)} = {(1, (select coke), 0)}"
    by auto
  have state_nondeterminism_0: "state_nondeterminism 0 {|(1, (select coke), 0), (1, (select pepsi), 1)|} = {|(0, (1, 1), ((select pepsi), 1), (select coke), 0), (0, (1, 1), ((select coke), 0), (select pepsi), 1)|}"
    by (simp add: state_nondeterminism_def fimage_def minus_3)
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_1_7_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_1 state_nondeterminism_0)
    apply (simp add: Abs_ffilter Set.filter_def)
    apply standard
     apply clarify
     apply simp
     apply (case_tac "a=0")
      apply simp
    using choices apply blast
     apply (case_tac "a=1")
    using choices apply blast
    apply simp
    apply clarify
    apply simp
    apply (case_tac "a = 0")
     apply simp
    apply (case_tac "a = 1")
     apply simp
     apply (case_tac "ab = coin 50 50")
      apply simp
      apply (case_tac "ac = coin 100 100")
    using choice_def by auto
qed

definition merged_1_3 :: iEFSM where
  "merged_1_3 = {|(0, (0, 1), selectGeneral), (2, (1, 1), (coin 50 50)), (4, (1, 1), (coin 50 100)), (5, (1, 4), vend_general),
                                              (3, (1, 5), (coin 100 100)), (6, (5, 6), vend_general)|}"

definition selectGeneral_2 :: transition where
  "selectGeneral_2 = \<lparr>Label = (STR ''select''), Arity = 1, Guard = [], Outputs = [], Updates = [(R 1, V (I 1)), (R 2, (L (Num 0)))]\<rparr>"

definition merged_1_3_coin :: iEFSM where
  "merged_1_3_coin = {|(0, (0, 1), selectGeneral_2), (2, (1, 1), coinGeneral), (5, (1, 4), vend_general),
                                              (3, (1, 5), (coin 100 100)), (6, (5, 6), vend_general)|}"

definition merged_1_5 :: iEFSM where
  "merged_1_5 = {|(0, (0, 1), selectGeneral_2), (2, (1, 1), coinGeneral), (5, (1, 4), vend_general), (3, (1, 1), (coin 100 100)),
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
  by (simp add: directly_subsumes_def no_subsumption_coin_50_50_coin_50_100)

lemma coin_50_100_cant_directly_subsume_coin_50_50: "\<not> directly_subsumes e t s (coin 50 100) (coin 50 50)"
  by (simp add: cant_directly_subsume no_subsumption_coin_50_100_coin_50_50)

lemma cant_merge_coins: "merge_transitions pta merged_2_9 8 1 1 2 2 (coin 50 100) 8 (coin 50 50) 2 modifier = None"
  apply (simp add: merge_transitions_def coin_50_100_cant_directly_subsume_coin_50_50 coin_50_50_cant_directly_subsume_coin_50_100)
  by (simp add: modifier_def)

lemma cant_merge_coins_2: "merge_transitions pta (merge_states (dest 2 merged_1_8) (dest 8 merged_1_8) merged_1_8) (origin 2 pta) (origin 8 pta)
           (origin 2 (merge_states (dest 2 merged_1_8) (dest 8 merged_1_8) merged_1_8))
           (dest 2 (merge_states (dest 2 merged_1_8) (dest 8 merged_1_8) merged_1_8))
           (dest 8 (merge_states (dest 2 merged_1_8) (dest 8 merged_1_8) merged_1_8)) (coin 50 50) 2 (coin 50 100) 8 modifier
            = None"
proof-
  have modify_none: "modifier 2 8 (origin 2 (merge_states (dest 2 merged_1_8) (dest 8 merged_1_8) merged_1_8))
             (merge_states (dest 2 merged_1_8) (dest 8 merged_1_8) merged_1_8) pta = None"
    by (simp add: modifier_def)
  show ?thesis
    apply (simp add: merge_transitions_def modify_none)
    by (simp add: coin_50_100_cant_directly_subsume_coin_50_50 coin_50_50_cant_directly_subsume_coin_50_100)
qed

definition merged_3_9 :: iEFSM where
  "merged_3_9 = {|(0, (0, 1), (select coke)),  (7, (1, 2), (coin 50 50)),   (8, (2, 3), (coin 50 100)), (5, (3, 4), (vend coke)),
                         (1, (0, 1), (select pepsi)), (3, (1, 5), (coin 100 100)), (6, (5, 6), (vend coke)),
                                                   (4, (2, 3), (coin 50 100)),  (9, (3, 10), (vend pepsi))|}"

definition merged_3_9_coin100 :: iEFSM where
  "merged_3_9_coin100 = {|(0, (0, 1), (select coke)),  (7, (1, 2), (coin 50 50)),  (5, (3, 4), (vend coke)),
                         (1, (0, 1), (select pepsi)), (3, (1, 5), (coin 100 100)), (6, (5, 6), (vend coke)),
                                                   (8, (2, 3), (coin 50 100)),  (9, (3, 10), (vend pepsi))|}"

definition merged_2_8_coin50 :: iEFSM where
  "merged_2_8_coin50 = {|
   (9, (9, 10), (vend pepsi)),
   (8, (2, 9), (coin 50 100)),
   (1, (0, 1), (select pepsi)),
   (6, (5, 6), (vend coke)),
   (3, (1, 5), (coin 100 100)),
   (5, (3, 4), (vend coke)),
   (4, (2, 3), (coin 50 100)),
   (0, (0, 1), (select coke)),
   (7, (1, 2), (coin 50 50))
|}"

lemma replace_coin50: "replace_transition merged_2_8 7 1 2 (coin 50 50) (coin 50 50) = merged_2_8_coin50"
proof-
  have filter: "{a \<in> fset merged_2_8. snd a \<noteq> ((1, 2), (coin 50 50))} = {
   (9, (9, 10), (vend pepsi)),
   (8, (2, 9), (coin 50 100)),
   (1, (0, 1), (select pepsi)),
   (6, (5, 6), (vend coke)),
   (3, (1, 5), (coin 100 100)),
   (5, (3, 4), (vend coke)),
   (4, (2, 3), (coin 50 100)),
   (0, (0, 1), (select coke))}"
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

lemma nondeterministic_pairs_merged_2_8_coin50: "nondeterministic_pairs merged_2_8_coin50 = {|(2, (3, 9), ((coin 50 100), 4), (coin 50 100), 8), (2, (9, 3), ((coin 50 100), 8), (coin 50 100), 4)|}"
proof-
  have minus_1: "{|(5, (coin 100 100), 3), (2, (coin 50 50), 2)|} |-| {|(2, (coin 50 50), 2)|} = {|(5, (coin 100 100), 3)|}"
    by auto
  have minus_3: "{(1, (select coke), 0), (1, (select pepsi), 1)} - {(1, (select pepsi), 1)} = {(1, (select coke), 0)}"
    by auto
  have minus_2: "{|(9, (coin 50 100), 8::nat), (3, (coin 50 100), 4)|} |-| {|(3, (coin 50 100), 4)|} = {|(9, (coin 50 100), 8)|}"
    by auto
  have state_nondeterminism_0: "state_nondeterminism 0 {|(1, (select coke), 0), (1, (select pepsi), 1)|} = {|(0, (1, 1), ((select pepsi), 1), (select coke), 0), (0, (1, 1), ((select coke), 0), (select pepsi), 1)|}"
    by (simp add: state_nondeterminism_def fimage_def minus_3)
  have outgoing_0_equiv: "{|(1, (select pepsi), 1), (1, (select coke), 0)|} = {|(1, (select coke), 0), (1, (select pepsi), 1)|}"
    by auto
  have state_nondeterminism_1: "state_nondeterminism 1 {|(5, (coin 100 100), 3), (2, (coin 50 50), 7)|} = {|(1, (2, 5), ((coin 50 50), 7), (coin 100 100), 3), (1, (5, 2), ((coin 100 100), 3), (coin 50 50), 7)|}"
    by eval
  have state_nondeterminism_2: "state_nondeterminism 2 {|(9, (coin 50 100), 8), (3, (coin 50 100), 4)|} = {|(2, (3, 9), ((coin 50 100), 4), (coin 50 100), 8), (2, (9, 3), ((coin 50 100), 8), (coin 50 100), 4)|}"
    by (simp add: state_nondeterminism_def minus_2)
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_2_8_coin50_def)
    apply (simp add: outgoing_transitions_def fimage_def)
    apply (simp add: outgoing_0_equiv state_nondeterminism_0 state_nondeterminism_1 state_nondeterminism_2)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply standard
     apply clarify
     apply simp
     apply (case_tac "a=0")
      apply simp
    using choice_symmetry no_choice_select_coke_select_pepsi apply blast
     apply simp
     apply (case_tac "a=2")
      apply auto[1]
     apply simp
    using no_choice_coin_100_100_coin_50_50 no_choice_coin_50_50_coin_100_100 apply blast
    apply clarify
    apply simp
     apply (case_tac "a=0")
     apply simp
     apply (case_tac "a=2")
     apply simp
    using choice_coin_50_100_coin_50_100 apply blast
    by simp
qed

lemma nondeterministic_pairs_merged_3_9_coin100: "nondeterministic_pairs merged_3_9_coin100 = {|
(3, (10, 4), ((vend pepsi), 9), (vend coke), 5), 
(3, (4, 10), ((vend coke), 5), (vend pepsi), 9)
|}"
proof-
  have minus_1: "{|(2, (coin 50 50), 2), (5, (coin 100 100), 3)|} |-| {|(5, (coin 100 100), 3)|} = {|(2, (coin 50 50), 2)|}"
    by auto
  have minus_2: "{|(4, (vend coke), 5), (10, (vend pepsi), 9)|} |-| {|(10, (vend pepsi), 9)|} = {|(4, (vend coke), 5)|}"
    by auto
  have minus_3: "{(1, (select coke), 0), (1, (select pepsi), 1)} - {(1, (select pepsi), 1)} = {(1, (select coke), 0)}"
    by auto
  have state_nondeterminism_0: "state_nondeterminism 0 {|(1, (select coke), 0), (1, (select pepsi), 1)|} = {|(0, (1, 1), ((select pepsi), 1), (select coke), 0), (0, (1, 1), ((select coke), 0), (select pepsi), 1)|}"
    by (simp add: state_nondeterminism_def fimage_def minus_3)
  have state_nondeterminism_1: "state_nondeterminism 1 {|(2, (coin 50 50), 7), (5, (coin 100 100), 3)|} = {|(1, (5, 2), ((coin 100 100), 3), (coin 50 50), 7), (1, (2, 5), ((coin 50 50), 7), (coin 100 100), 3)|}"
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
    apply standard
     apply (case_tac "a=0")
      apply simp
    using choice_symmetry no_choice_select_coke_select_pepsi apply blast
     apply simp
     apply (case_tac "a=3")
      apply simp
     apply simp
    using no_choice_coin_100_100_coin_50_50 no_choice_coin_50_50_coin_100_100 apply blast
     apply (case_tac "a=0")
     apply simp
    using choice_symmetry no_choice_select_coke_select_pepsi apply blast
     apply (case_tac "a=3")
     apply auto[1]
    using no_choice_coin_100_100_coin_50_50 no_choice_coin_50_50_coin_100_100 by auto
qed

lemma possible_steps_not_vend: "aa = (STR ''vend'') \<longrightarrow> b \<noteq> [] \<Longrightarrow> possible_steps (tm pta) 3 Map.empty aa b = {||}"
  apply (simp add: possible_steps_fst)
  apply (simp add: tm_def pta_def Set.filter_def)
  by auto

lemma possible_steps_vend: "possible_steps (tm merged_vends) 3 r (STR ''vend'') [] = {|(4, vend_general)|}"
  apply (rule possible_steps_singleton)
  apply (simp add: Abs_ffilter Set.filter_def merged_vends_def tm_def)
  apply safe
  by (simp_all add: vend_general_def)

lemma possible_steps_pta_2_not_coin50: "aa = (STR ''coin'') \<longrightarrow> b \<noteq> [Num 50] \<Longrightarrow> possible_steps (tm pta) 2 Map.empty aa b = {||}"
  apply (simp add: possible_steps_def Abs_ffilter pta_def tm_def Set.filter_def)
  by (metis One_nat_def hd_input2state le_numeral_extra(4) length_0_conv length_Suc_conv list.sel(1) option.sel)

lemma possible_steps_merged_vends_coin50_2: "possible_steps (tm merged_vends) 2 r (STR ''coin'') [Num 50] = {|(3, (coin 50 100))|}"
  apply (rule possible_steps_singleton)
  apply (simp add: Abs_ffilter Set.filter_def merged_vends_def tm_def)
  by auto

lemma possible_steps_pta_5_not_vend: "a = (STR ''vend'') \<longrightarrow> b \<noteq> [] \<Longrightarrow> possible_steps (tm pta) 5 Map.empty a b = {||}"
  apply (simp add: possible_steps_def Abs_ffilter Set.filter_def pta_def tm_def)
  by auto

lemma possible_steps_pta_1_not_coin: "aa = (STR ''coin'') \<longrightarrow> b \<noteq> [Num 50] \<Longrightarrow>
       aa = (STR ''coin'') \<longrightarrow> b \<noteq> [Num 100] \<Longrightarrow>
       possible_steps (tm pta) 1 Map.empty aa b = {||}"
  apply (simp add: possible_steps_def Abs_ffilter Set.filter_def pta_def tm_def)
  apply clarify
  apply (case_tac "ba = 2")
  apply simp
  apply (metis One_nat_def hd_input2state le_numeral_extra(4) length_0_conv length_Suc_conv list.sel(1) option.sel trilean.distinct(1))
  apply simp
  by (metis One_nat_def hd_input2state le_numeral_extra(4) length_0_conv length_Suc_conv list.sel(1) option.sel trilean.distinct(1))

lemma possible_steps_merged_vends_coin50_1: "possible_steps (tm merged_vends) 1 r (STR ''coin'') [Num 50] = {|(2, (coin 50 50))|}"
  apply (rule possible_steps_singleton)
  apply (simp add: Abs_ffilter Set.filter_def merged_vends_def tm_def)
  by auto

lemma possible_steps_merged_vends_coin100: "possible_steps (tm merged_vends) 1 r (STR ''coin'') [Num 100] = {|(5, (coin 100 100))|}"
  apply (rule possible_steps_singleton)
  apply (simp add: Abs_ffilter Set.filter_def merged_vends_def tm_def)
  by auto

lemma possible_steps_pta_9_not_vend: "aa = (STR ''vend'') \<longrightarrow> b \<noteq> [] \<Longrightarrow>
       possible_steps (tm pta) 9 Map.empty aa b = {||}"
  apply (simp add: possible_steps_def Abs_ffilter Set.filter_def pta_def tm_def)
  by auto

lemma possible_steps_pta_8_not_coin: "aa = (STR ''coin'') \<longrightarrow> b \<noteq> [Num 50] \<Longrightarrow>
       possible_steps (tm pta) 8 Map.empty aa b = {||}"
  apply (simp add: possible_steps_def Abs_ffilter Set.filter_def pta_def tm_def)
  by (metis One_nat_def hd_input2state le_numeral_extra(4) length_0_conv length_Suc_conv list.sel(1) option.sel)

lemma possible_steps_pt_7_not_coin: "aa = (STR ''coin'') \<longrightarrow> b \<noteq> [Num 50] \<Longrightarrow>
       possible_steps (tm pta) 7 Map.empty aa b = {||}"
  apply (simp add: possible_steps_def Abs_ffilter Set.filter_def pta_def tm_def)
  by (metis One_nat_def hd_input2state le_numeral_extra(4) length_0_conv length_Suc_conv list.sel(1) option.sel)

lemma possible_steps_pta_0_not_select: " aa = (STR ''select'') \<longrightarrow> b \<noteq> [(Str ''coke'')] \<Longrightarrow>
       aa = (STR ''select'') \<longrightarrow> b \<noteq> [(Str ''pepsi'')] \<Longrightarrow>
       possible_steps (tm pta) 0 Map.empty aa b = {||}"
  apply (simp add: possible_steps_def Abs_ffilter Set.filter_def pta_def tm_def)
  apply clarify
  apply (case_tac "ba = 1")
   apply simp
  sorry

lemma nondeterministic_pairs_merged_vends: "nondeterministic_pairs merged_vends = {||}"
proof-
  have minus_1: "{|(2, (coin 50 50), 2), (5, (coin 100 100), 3)|} |-| {|(5, (coin 100 100), 3)|} = {|(2, (coin 50 50), 2)|}"
    by auto
  have state_nondeterminism_1: "state_nondeterminism 1 {|(2, (coin 50 50), 2), (5, (coin 100 100), 3)|} = {|(1, (5, 2), ((coin 100 100), 3), (coin 50 50), 2), (1, (2, 5), ((coin 50 50), 2), (coin 100 100), 3)|}"
    by (simp add: state_nondeterminism_def minus_1)
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_vends_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_1)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    using choices by auto
qed

lemma "learn traces naive_score modifier = (tm final)"
  oops

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