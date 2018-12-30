theory DM_Inference
imports Inference SelectionStrategies "../examples/Drinks_Machine_2"
begin

declare One_nat_def[simp del]

lemma "max coin vend = vend"
  by (simp add: max_def coin_def vend_def less_eq_transition_ext_def less_transition_ext_def)

lemma merge_states_1_2: "merge_states 1 2 drinks2 = {|
              ((0,1), select),
              ((1,1), vend_nothing),
              ((1,1), coin),
              ((1,1), vend_fail),
              ((1,3), vend)
         |}"
  by (simp add: merge_states_def merge_states_aux_def drinks2_def )

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

lemma coin_not_vend_fail: "coin \<noteq> vend_fail"
  by (simp add: transitions)

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

lemma filter_all_pairs: "(Set.filter (\<lambda>(((origin1, dest1), t1), (origin2, dest2), t2). origin1 = origin2 \<and> t1 < t2 \<and> choice t1 t2)
       (fset (all_pairs (merge_states 1 2 drinks2)))) = {(((1, 1), vend_nothing), (1, 1), vend_fail), (((1, 1), vend_nothing), (1, 3), vend)}"
proof
  show "Set.filter (\<lambda>(((origin1, dest1), t1), (origin2, dest2), t2). origin1 = origin2 \<and> t1 < t2 \<and> choice t1 t2)
     (fset (all_pairs (merge_states 1 2 drinks2)))
    \<subseteq> {(((1, 1), vend_nothing), (1, 1), vend_fail), (((1, 1), vend_nothing), (1, 3), vend)}"
    apply (simp add: merge_states_1_2 all_pairs_def Set.filter_def)
    apply clarify
    apply simp
    apply (case_tac "bb=1")
     apply (case_tac "aa=1")
     apply (case_tac "ba=vend_nothing")
       apply simp
       apply (metis (no_types, hide_lams) coin_def Updates_coin arity_vend choice_def choice_vend_vend_nothing label_coin not_less_iff_gr_or_eq select_convs(2) vend_nothing_lt_vend zero_neq_one)
      apply simp
    using choice_def label_coin label_vend_fail label_vend_nothing no_choice_vend_coin no_choice_vend_vend_fail vend_nothing_lt_vend vend_nothing_lt_vend_fail apply fastforce
     apply simp
    apply simp
    using choice_symmetry no_choice_vend_coin no_choice_vend_vend_fail by auto
  show "{(((1, 1), vend_nothing), (1, 1), vend_fail), (((1, 1), vend_nothing), (1, 3), vend)}
    \<subseteq> Set.filter (\<lambda>(((origin1, dest1), t1), (origin2, dest2), t2). origin1 = origin2 \<and> t1 < t2 \<and> choice t1 t2)
        (fset (all_pairs (merge_states 1 2 drinks2)))"
    apply (simp add: merge_states_1_2 all_pairs_def Set.filter_def)
    using choice_symmetry choice_vend_nothing_vend_fail choice_vend_vend_nothing vend_nothing_lt_vend vend_nothing_lt_vend_fail by blast
qed

lemma ffilter_all_pairs: "ffilter (\<lambda>(((origin1, dest1), t1), (origin2, dest2), t2). origin1 = origin2 \<and> t1 < t2 \<and> choice t1 t2) (all_pairs (merge_states 1 2 drinks2)) =
                          {|(((1, 1), vend_nothing), (1, 1), vend_fail), (((1, 1), vend_nothing), (1, 3), vend)|}"
  apply (simp add: ffilter_def )
  using filter_all_pairs
  by (metis (no_types, lifting) bot_fset.rep_eq finsert.rep_eq fset_inverse)

lemma nondeterminisitic_pairs: "(nondeterministic_pairs (merge_states 1 2 drinks2)) = {|(1, (1, 3), (vend_nothing, vend)), (1, (1, 1), vend_nothing, vend_fail)|}"
  apply (simp add: nondeterministic_pairs_def ffilter_all_pairs )
  by auto

lemma vend_nothing_vend_nondeterminism: "(1, (1, 3), (vend_nothing, vend)) |\<in>| nondeterministic_pairs (merge_states 1 2 drinks2)"
  by (simp add: nondeterminisitic_pairs )

lemma vend_vend_nothing_nondeterminism: "nondeterministic_pairs (merge_states 1 2 drinks2) \<noteq> {||}"
  by (simp add: nondeterminisitic_pairs )

lemma vend_nothing_vend_fail_nondeterminism: "(1, (1, 1), vend_nothing, vend_fail) |\<in>| nondeterministic_pairs (merge_states 1 2 drinks2)"
  by (simp add: nondeterminisitic_pairs )

lemma nond_transitions_not_none: "nondeterministic_transitions (merge_states 1 2 drinks2) \<noteq> None"
  by (simp add: nondeterminisitic_pairs nondeterministic_transitions_def )

lemma nondeterministic_pairs_members: "x |\<in>| nondeterministic_pairs (merge_states 1 2 drinks2) \<Longrightarrow> x = (1, (1, 3), (vend_nothing, vend)) \<or> x = (1, (1, 1), vend_nothing, vend_fail)"
  by (simp add: nondeterminisitic_pairs )

lemma no_nondeterminism_0: "\<forall>aa b ab ba. nondeterministic_transitions (merge_states 1 2 drinks2) \<noteq> Some (0, (aa, b), ab, ba)"
  by (simp add: nondeterminisitic_pairs nondeterministic_transitions_def max_def )

lemma no_nondeterminism_2: "\<forall>aa b ab ba. (2, (aa, b), ab, ba) |\<notin>| nondeterministic_pairs (merge_states 1 2 drinks2)"
  by (simp add: nondeterminisitic_pairs )

lemma no_nondeterminism_2_2: "\<forall>aa b ab ba. nondeterministic_transitions (merge_states 1 2 drinks2) \<noteq> Some (2, (aa, b), ab, ba)"
  by (simp add: nondeterministic_transitions_def nondeterminisitic_pairs max_def )

lemma no_nondeterminism_3: "\<forall>aa b ab ba. (3, (aa, b), ab, ba) |\<notin>| nondeterministic_pairs (merge_states 1 2 drinks2)"
  by (simp add: nondeterminisitic_pairs )

lemma no_nondeterminism_3_2: "\<forall>aa b ab ba. nondeterministic_transitions (merge_states 1 2 drinks2) \<noteq> Some (3, (aa, b), ab, ba)"
  by (simp add: nondeterministic_transitions_def nondeterminisitic_pairs max_def )

lemma only_nondeterminism_1: "nondeterministic_transitions (merge_states 1 2 drinks2) = Some (a, (aa, b), aaa, ba) \<Longrightarrow> a = 1"
  by (simp add: nondeterministic_transitions_def nondeterminisitic_pairs max_def )

lemma no_transitions_to_0: "aa = 0 \<or> b = 0 \<Longrightarrow> (a, (aa, b), ab, ba) |\<notin>| nondeterministic_pairs (merge_states 1 2 drinks2)"
  apply (simp add: nondeterministic_transitions_def nondeterminisitic_pairs max_def )
  by auto

lemma no_transitions_to_0_2: "aa = 0 \<or> b = 0 \<Longrightarrow> nondeterministic_transitions (merge_states 1 2 drinks2) \<noteq> Some (a, (aa, b), ab, ba)"
  apply (simp add: nondeterministic_transitions_def nondeterminisitic_pairs max_def )
  by auto

lemma q1_nondeterminism_options: "(1, (1, 1), ab, ba) |\<in>| nondeterministic_pairs (merge_states 1 2 drinks2) \<Longrightarrow> ab = vend_fail \<and> ba = vend_nothing \<or> ab = vend_nothing \<and> ba = vend_fail"
  by (simp add: nondeterministic_transitions_def nondeterminisitic_pairs max_def )

lemma q1_nondeterminism_options_2: "nondeterministic_transitions (merge_states 1 2 drinks2) = Some (1, (1, 1), ab, ba) \<Longrightarrow> ab = vend_fail \<and> ba = vend_nothing \<or> ab = vend_nothing \<and> ba = vend_fail"
  by (simp add: nondeterministic_transitions_def nondeterminisitic_pairs max_def )

lemma medial_vend_nothing: "(medial c (Guard vend_nothing)) = c"
  by (simp add: transitions)

lemma medial_vend_fail: "medial select_posterior (Guard vend_fail) = \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> And (Eq (Num 0)) (Lt (Num 100))\<rbrakk>"
  apply (rule ext)
  by (simp add: transitions select_posterior_def)

lemma vend_nothing_posterior: "posterior select_posterior vend_nothing = select_posterior"
  apply (simp only: posterior_def medial_vend_nothing)
  apply (simp add: consistent_select_posterior)
  apply (rule ext)
  by (simp add: transitions remove_input_constraints_def select_posterior_def)

lemma consistent_medial_vend_fail: "consistent \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> And (cexp.Eq (Num 0)) (cexp.Lt (Num 100))\<rbrakk>"
  apply (simp add: consistent_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num 0>" in exI)
  by (simp add: consistent_empty_4)

lemma vend_fail_posterior: "posterior select_posterior vend_fail = \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> And (Eq (Num 0)) (Lt (Num 100))\<rbrakk>"
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

lemma posterior_select: "length (snd e) = 1 \<Longrightarrow> (posterior \<lbrakk>\<rbrakk> (snd (fthe_elem (possible_steps drinks2 0 Map.empty ''select'' (snd e))))) =
     (\<lambda>a. if a = V (R 2) then cexp.Eq (Num 0) else if a = V (R (1)) then cexp.Bc True else \<lbrakk>\<rbrakk> a)"
  apply (simp add: posterior_def fthe_elem_def possible_steps_0 select_def Let_def remove_input_constraints_def)
  apply (rule ext)
  by simp

lemma apply_updates_vend_nothing_2: "(EFSM.apply_updates (Updates vend_nothing)
           (case_vname Map.empty (\<lambda>n. if n = 2 then Some (Num 0) else if R n = R 1 then Some (hd (snd e)) else None))
           (\<lambda>a. if a = R 2 then Some (Num 0) else if a = R 1 then Some (hd (snd e)) else None)) = <R 2 \<mapsto> Num 0, R 1 \<mapsto> (hd (snd e))>"
  apply (rule ext)
  by (simp add: transitions)

lemma register_simp: "(\<lambda>x. if x = R (1)
          then aval (snd (R (1), V (R (1)))) (case_vname Map.empty (\<lambda>n. if n = 2 then Some (Num 0) else <R (1) := hd (snd e)> (R n)))
          else EFSM.apply_updates [(R 2, V (R 2))] (case_vname Map.empty (\<lambda>n. if n = 2 then Some (Num 0) else <R (1) := hd (snd e)> (R n)))
                <R (1) := hd (snd e), R 2 := Num 0> x) =  <R (1) := hd (snd e), R 2 := Num 0>"
  apply (rule ext)
  by simp

lemma observe_vend_nothing: "a = (''vend'', []) \<Longrightarrow> (observe_all drinks2 1 <R (1) := hd (snd e), R 2 := Num 0> (a # t)) = (vend_nothing, 1, [], <R (1) := hd (snd e), R 2 := Num 0>)#(observe_all drinks2 1 <R (1) := hd (snd e), R 2 := Num 0> t)"
  apply (simp add: step_def drinks2_vend_insufficient fis_singleton_def updates_vend_nothing outputs_vend_nothing )
  apply safe
   apply (rule ext)
   apply simp
  by (simp only: register_simp)

lemma coin_updates: "(EFSM.apply_updates (Updates coin)
            (case_vname (\<lambda>n. input2state (snd a) (1) (I n)) (\<lambda>n. if n = 2 then Some (Num 0) else <R (1) := s> (R n)))
            <R (1) := s, R 2 := Num 0>) = (\<lambda>u. if u = R 1 then Some s else if u = R 2 then value_plus (Some (Num 0)) (input2state (snd a) 1 (I 1)) else None)"
  apply (rule ext)
  by (simp add: coin_def)

lemma equal_first_event: "observe_all drinks2 0 Map.empty t = x # list \<Longrightarrow>
       observe_all drinks2 0 Map.empty (t @ [e]) = y # lista \<Longrightarrow> x = y"
proof (induct t)
  case Nil
  then show ?case
    by simp
next
  case (Cons a t)
  then show ?case
    apply simp
    apply (case_tac "fst a = ''select'' \<and> length (snd a) = 1")
     apply (simp add: step_def possible_steps_0 select_posterior )
     apply (simp add: updates_select )
     apply auto[1]
    by (simp add: drinks2_0_invalid step_def)
qed

lemma drinks2_singleton_0: "fis_singleton (possible_steps drinks2 0 Map.empty (fst e) (snd e)) \<Longrightarrow> fst e = ''select'' \<and> length (snd e) = 1"
  apply (case_tac "fst e = ''select'' \<and> length (snd e) = 1 ")
   apply simp
  by (simp add: drinks2_0_invalid)

lemma drinks2_observe_all_fst_select: "observe_all drinks2 0 Map.empty (t @ [e]) = [(aaa, 1, c, d)] \<Longrightarrow> aaa = select"
proof (induct t)
  case Nil
  then show ?case
    apply simp
    apply (case_tac "fst e = ''select'' \<and> length (snd e) = 1 ")
     apply (simp add: possible_steps_0 step_def)
    by (simp add: drinks2_0_invalid step_def)
next
  case (Cons e t)
  then show ?case
    apply simp
    apply (case_tac "fst e = ''select'' \<and> length (snd e) = 1 ")
     apply (simp add: possible_steps_0 step_def)
    by (simp add: drinks2_0_invalid step_def)
qed

lemma drinks2_singleton_0_select: "fis_singleton (possible_steps drinks2 0 Map.empty (fst e) (snd e)) \<Longrightarrow>
       fthe_elem (possible_steps drinks2 0 Map.empty (fst e) (snd e)) = (1, aa) \<Longrightarrow> aa = select"
  using Drinks_Machine_2.possible_steps_0 drinks2_singleton_0 by auto

lemma coin_updates_2: "(EFSM.apply_updates (Updates coin)
       (case_vname (\<lambda>n. input2state (snd a) (1) (I n)) (\<lambda>n. if n = 2 then Some (Num 0) else if R n = R (1) then Some s else None))
       (\<lambda>a. if a = R 2 then Some (Num 0) else if a = R (1) then Some (hd (snd e)) else None)) =
       (\<lambda>u. if u = R 1 then Some s else if u = R 2 then value_plus (Some (Num 0)) (input2state (snd a) 1 (I 1)) else None)"
  apply (rule ext)
  by (simp add: coin_def)

lemma r_R2_none: "r (R 2) = None \<Longrightarrow> (possible_steps drinks2 2 r ''vend'' []) = {||}"
  apply (simp add: possible_steps_def drinks2_def transitions )
  by auto

lemma drinks2_vend_insufficient2: "r (R 2) = Some (Num x1) \<Longrightarrow> ab = Num x1 \<Longrightarrow> x1 < 100 \<Longrightarrow>
                possible_steps drinks2 2 r (''vend'') [] = {|(2, vend_fail)|}"
  apply (simp add: possible_steps_def drinks2_def transitions )
  apply safe
    apply (simp )
    apply auto[1]
    apply (simp )
   apply auto[1]
  apply (simp )
  by force

lemma drinks2_vend_sufficient: "r (R 2) = Some (Num x1) \<Longrightarrow>
                \<not> x1 < 100 \<Longrightarrow>
                possible_steps drinks2 2 r (''vend'') [] = {|(3, vend)|}"
  apply (simp add: possible_steps_def drinks2_def transitions )
  by force

lemma none_outputs_vend:  "r (R 1) = None \<Longrightarrow> apply_outputs (Outputs vend) r = [None]"
  by (simp add: vend_def)

lemma "choice vend_nothing vend"
  by (simp add: choice_symmetry choice_vend_vend_nothing)

lemma nondeterministic_transitions: "nondeterministic_transitions (merge_states 1 2 drinks2) = Some (1, (1, 3), vend_nothing, vend)"
  by (simp add: nondeterministic_transitions_def nondeterminisitic_pairs max_def )

lemma vend_doesnt_exit_1[simp]: "\<not>exits_state drinks2 vend 1"
  apply (simp add: exits_state_def drinks2_def transitions )
  by auto

lemma vend_nothing_exits_1[simp]: "exits_state drinks2 vend_nothing 1"
  apply (simp add: exits_state_def drinks2_def)
  by auto

lemma merge_1_3: "let t' = merge_states 1 2 drinks2
        in merge_states 1 3 t' = {|((0, 1), select),
                                   ((1,1), vend_nothing),
                                   ((1,1), coin),
                                   ((1,1), vend_fail),
                                   ((1,1), vend)|}"
  apply (simp add: merge_states_1_2 )
  by (simp add:  merge_states_def merge_states_aux_def )

lemma merge_1_3_2: "(merge_states 1 3 (merge_states 1 2 drinks2)) = {|((0, 1), select),
                      ((1,1),vend_nothing),
((1,1), coin),
((1,1), vend_fail),
((1,1), vend)|}"
  using merge_1_3 by auto


lemma vend_fail_leq_vend: "vend_fail \<le> vend"
  by (simp add: less_eq_transition_ext_def less_transition_ext_def transitions less_gexp_def)

lemma max_nondeterministic_transitions: "max (1::nat, (1::nat, 1::nat), vend_nothing, vend) (1, (1, 1), vend_nothing, vend_fail) = (1, (1, 1), vend_nothing, vend)"
  apply (simp add: max_def)
  by (simp add: eq_iff vend_fail_leq_vend)

lemma vend_neq_vend_fail: "vend \<noteq> vend_fail"
  by (simp add: transitions)

lemma vend_neq_coin: "vend \<noteq> coin"
  by (simp add: transitions)

lemma vend_fail_neq_vend_nothing: "vend_fail \<noteq> vend_nothing"
  by (simp add: transitions)

lemma filter_all_pairs_2:"Set.filter (\<lambda>(((origin1, dest1), t1), (origin2, dest2), t2). origin1 = origin2 \<and> t1 < t2 \<and> choice t1 t2)
       (fset (ffUnion ((\<lambda>x. Pair x |`| merge_states 1 3 (merge_states 1 2 drinks2)) |`| merge_states 1 3 (merge_states 1 2 drinks2)))) =
      {
      (((1, 1), vend_nothing), (1, 1), vend_fail),
      (((1, 1), vend_nothing), (1, 1), vend)
      }"
proof
  show "Set.filter (\<lambda>(((origin1, dest1), t1), (origin2, dest2), t2). origin1 = origin2 \<and> t1 < t2 \<and> choice t1 t2)
     (fset (ffUnion ((\<lambda>x. Pair x |`| merge_states 1 3 (merge_states 1 2 drinks2)) |`| merge_states 1 3 (merge_states 1 2 drinks2))))
    \<subseteq> {(((1, 1), vend_nothing), (1, 1), vend_fail), (((1, 1), vend_nothing), (1, 1), vend)}"
    apply (simp add: merge_1_3_2 Set.filter_def)
    apply clarify
    apply simp
    apply (case_tac "bb=1")
     apply (case_tac "aa=1")
      apply (case_tac "ba=vend_nothing")
       apply simp
    using Drinks_Machine.transitions(2) arity_vend_fail choice_def choice_vend_nothing_vend_fail apply fastforce
      apply simp
    using choice_def label_coin label_vend_fail label_vend_nothing no_choice_vend_coin no_choice_vend_vend_fail vend_nothing_lt_vend vend_nothing_lt_vend_fail apply fastforce
     apply simp
    by simp
  show "{(((1, 1), vend_nothing), (1, 1), vend_fail), (((1, 1), vend_nothing), (1, 1), vend)}
    \<subseteq> Set.filter (\<lambda>(((origin1, dest1), t1), (origin2, dest2), t2). origin1 = origin2 \<and> t1 < t2 \<and> choice t1 t2)
        (fset (ffUnion ((\<lambda>x. Pair x |`| merge_states 1 3 (merge_states 1 2 drinks2)) |`| merge_states 1 3 (merge_states 1 2 drinks2))))"
    apply (simp add: merge_1_3_2 Set.filter_def)
    using choice_symmetry choice_vend_nothing_vend_fail choice_vend_vend_nothing vend_nothing_lt_vend vend_nothing_lt_vend_fail by blast
qed

lemma ffilter_all_pairs_2: "ffilter (\<lambda>(((origin1, dest1), t1), (origin2, dest2), t2). origin1 = origin2 \<and> t1 < t2 \<and> choice t1 t2)
     (all_pairs (merge_states 1 3 (merge_states 1 2 drinks2))) = {|(((1, 1), vend_nothing), (1, 1), vend_fail), (((1, 1), vend_nothing), (1, 1), vend)|}"
  apply (simp add: all_pairs_def ffilter_def filter_all_pairs_2 )
  by (metis fset_inverse fset_simps(1) fset_simps(2))

lemma merge_states_2_nondeterminism: "nondeterministic_transitions (merge_states 1 3 (merge_states 1 2 drinks2)) = Some (1, (1, 1), vend_nothing, vend)"
  apply (simp add: nondeterministic_transitions_def nondeterministic_pairs_def )
  apply (simp add: ffilter_all_pairs_2 )
  by (metis max.commute max_nondeterministic_transitions)

lemma vend_exits_1: "exits_state (merge_states 1 2 drinks2) vend 1"
  apply (simp add: exits_state_def merge_states_1_2 )
  by auto

lemma vend_nothing_exits_1_2: "exits_state (merge_states 1 2 drinks2) vend_nothing 1"
  apply (simp add: exits_state_def merge_states_1_2 )
  by auto

lemma not_subset: "\<not>{(1, (1, 3), vend_nothing, vend), (1, (1, 1), vend_nothing, vend_fail)}
        \<subseteq> {Max {(1, (1, 3), vend_nothing, vend), (1, (1, 1), vend_nothing, vend_fail)}}"
  using vend_neq_vend_fail by auto

lemma not_subset_2: "\<not> {(1, (1, 1), vend_nothing, vend), (1, (1, 1), vend_nothing, vend_fail)}
     \<subseteq> {Max {(1, (1, 1), vend_nothing, vend), (1, (1, 1), vend_nothing, vend_fail)}}"
  using choice_def choice_vend_vend_nothing no_choice_vend_vend_fail by auto

lemma nondeterminism_merge_states_1_2: "nondeterminism (merge_states 1 2 drinks2)"
  by (simp add: nondeterminism_def vend_vend_nothing_nondeterminism )

lemma max_nondeterminism: "max (1::nat, (1::nat, 3::nat), vend_nothing, vend) (1, (1, 1), vend_nothing, vend_fail) = (1, (1, 3), vend_nothing, vend)"
  using nondeterminisitic_pairs nondeterministic_transitions nondeterministic_transitions_def by auto

lemma apply_guards_vend_nothing:  "\<forall>i r. apply_guards (Guard vend_nothing) (join_ir i r)"
  by (simp add: guard_vend_nothing)

lemma consistent_posterior_vend_nothing: "consistent c \<Longrightarrow> consistent (posterior c vend_nothing)"
proof-
  assume premise: "consistent c"
  have medial_vend_nothing: "medial c (Guard vend_nothing) = c"
    by (simp add: vend_nothing_def)
  have updates_vend_nothing: "Contexts.apply_updates c c (Updates vend_nothing) = c"
    apply (rule ext)
    by (simp add: vend_nothing_def)
  show ?thesis
    unfolding posterior_def Let_def
    apply (simp add: medial_vend_nothing premise)
    by (simp add: updates_vend_nothing premise)
qed

lemma consistent_posterior_vend_nothing_2: "\<not>consistent c \<Longrightarrow> \<not>consistent (posterior c vend_nothing)"
  apply (simp add: posterior_def guard_vend_nothing updates_vend_nothing)
  by (simp add: consistent_def)

lemma outputs_vend_neq_vend_nothing: "(\<exists>i r. [] \<noteq> apply_outputs (Outputs vend) (case_vname (\<lambda>n. input2state i (1) (I n)) (\<lambda>n. r (R n))))"
  apply (rule_tac x="[]" in exI)
  apply (rule_tac x="<R 1 := Str ''coke''>" in exI)
  by (simp add: vend_def)

lemma inconsistent_undef: "\<not> consistent
         (\<lambda>x. if constrains_an_input x then \<lbrakk>\<rbrakk> x
              else if x = V (R 2) then And Undef (Geq (Num 100)) else if x = V (R 1) then c (V (R 1)) else c x)"
  apply (simp add: consistent_def)
  apply clarify
  apply (rule_tac x="V (R 2)" in exI)
  apply simp
  apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some (Num 100)) (s (R 2))")
   apply simp
  by simp

lemma possible_steps_0_2: "length i = 1 \<Longrightarrow> (possible_steps (merge_states 1 2 drinks2) 0 Map.empty ''select'' i) = {|(1, select)|}"
proof-
  assume premise: "length i = 1"
  have set_filter: "(Set.filter
       (\<lambda>((origin, dest), t).
           origin = 0 \<and>
           Label t = ''select'' \<and> length i = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state i 1 (I n)) Map.empty))
       (fset (merge_states 1 2 drinks2))) = {((0, 1), select)}"
    using premise
    apply (simp add: Set.filter_def merge_states_1_2)
    apply safe
    by (simp_all add: transitions)
  show ?thesis
    by (simp add: possible_steps_def ffilter_def set_filter)
qed

lemma select_gets_us_to_1: "gets_us_to 1 (merge_states 1 2 drinks2) 0 Map.empty [(''select'', [Str ''coke''])]"
  apply (rule gets_us_to.step_some)
   apply (simp add: step_def possible_steps_0_2)
  apply (rule gets_us_to.base)
  by simp

lemma nondeterminsm_merge_1_3: "nondeterminism (merge_states 1 3 (merge_states 1 2 drinks2))"
  apply (simp add: nondeterminism_def merge_1_3_2 nondeterministic_pairs_def )
  using ffilter_all_pairs_2 merge_1_3 by auto

lemma good_max: "Max ({(1, (1, 3), vend_nothing, vend), (1, (1, 1), vend_nothing, vend_fail)} -
               {max (1, (1, 3), vend_nothing, vend) (1, (1, 1), vend_nothing, vend_fail)}) = (1::nat, (1::nat, 1::nat), vend_nothing, vend_fail)"
  by (simp add: max_def)

lemma vend_fail_doesnt_exit_1[simp]: "\<not>exits_state drinks2 vend_fail 1"
proof-
  have set_filter: "(Set.filter (\<lambda>((from', to), t'). from' = 1 \<and> t' = vend_fail) (fset drinks2)) = {}"
    unfolding drinks2_def apply safe
    apply (simp )
    using coin_not_vend_fail vend_fail_neq_vend_nothing by auto
  show "\<not> exits_state drinks2 vend_fail 1"
    by (simp add: exits_state_def ffilter_def set_filter )
qed

lemma medial_r1_r2_true_vend_fail: "medial r1_r2_true (Guard vend_fail) = \<lbrakk>V (R 2) \<mapsto> Lt (Num 100), V (R 1) \<mapsto> Bc True\<rbrakk>"
    apply (simp add: guard_vend_fail )
    apply (rule ext)
    by (simp add: transitions r1_r2_true_def)

lemma posterior_vend_fail: "posterior r1_r2_true vend_fail = \<lbrakk>V (R 2) \<mapsto> cexp.Lt (Num 100), V (R 1) \<mapsto> cexp.Bc True\<rbrakk>"
proof-
  have consistent_medial: "consistent \<lbrakk>V (R 2) \<mapsto> cexp.Lt (Num 100), V (R 1) \<mapsto> cexp.Bc True\<rbrakk>"
    unfolding consistent_def
    apply (rule_tac x="<R 2 := Num 0, R 1 := Str ''coke''>" in exI)
    apply (simp add: transitions)
    using consistent_empty_4 by auto
  show ?thesis
    unfolding posterior_def
    apply (simp add: medial_r1_r2_true_vend_fail Let_def consistent_medial )
    apply (rule ext)
    by (simp add: transitions remove_input_constraints_def r1_r2_true_def)
qed

lemma posterior_vend_nothing: "posterior r1_r2_true vend_nothing = r1_r2_true"
  apply (rule ext)
  unfolding posterior_def
  apply (simp add: guard_vend_nothing Let_def consistent_r1_r2_true updates_vend_nothing remove_input_constraints_def)
  by (simp add: r1_r2_true_def)

lemma finsert_vend_nothing: "finsert vend_nothing ({|vend_nothing, coin, vend_fail|} |-| {|vend_fail|}) = {|coin, vend_nothing|}"
  apply (simp add: transitions)
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

lemmas choices = choice_vend_nothing_vend no_choice_vend_vend_fail no_choice_vend_coin choice_vend_vend_nothing no_choice_coin_vend_nothing no_choice_vend_nothing_coin no_choice_vend_fail_coin choice_vend_fail_vend_nothing choice_vend_nothing_vend_fail choice_coin_coin choice_vend_nothing_vend_nothing no_choice_coin_vend_fail choice_vend_fail_vend_fail

lemma vend_nothing_vend_max: "(1::nat, (1::nat, 3::nat), vend_nothing, vend) = max (1, (1, 3), vend_nothing, vend) (1, (1, 1), vend_nothing, vend_fail)"
  using max_nondeterminism by auto

lemma vend_nothing_neq_vend: "vend_nothing \<noteq> vend"
  by (simp add: transitions)

lemma vend_nothing_neq_vend_fail: "vend_nothing \<noteq> vend_fail"
  by (simp add: transitions)

lemma vend_nothing_neq_coin: "vend_nothing \<noteq> coin"
  by (simp add: transitions)

lemma nondeterministic_pairs_1_3: "nondeterministic_pairs (merge_states 1 3 (merge_states 1 2 drinks2)) = {|(1, (1, 1), (vend_nothing, vend)), (1, (1, 1), vend_nothing, vend_fail)|}"
proof-
have filter: "(Set.filter (\<lambda>(((origin1, dest1), t1), (origin2, dest2), t2). origin1 = origin2 \<and> t1 < t2 \<and> choice t1 t2)
       (fset (all_pairs (merge_states 1 3 (merge_states 1 2 drinks2))))) =
    {(((1, 1), vend_nothing), ((1, 1), vend)), (((1, 1), vend_nothing), ((1, 1), vend_fail))}"
proof
  show "{(((1, 1), vend_nothing), (1, 1), vend), (((1, 1), vend_nothing), (1, 1), vend_fail)}
    \<subseteq> Set.filter (\<lambda>(((origin1, dest1), t1), (origin2, dest2), t2). origin1 = origin2 \<and> t1 < t2 \<and> choice t1 t2)
        (fset (all_pairs (merge_states 1 3 (merge_states 1 2 drinks2))))"
  proof
    show "\<And>x. x \<in> {(((1, 1), vend_nothing), (1, 1), vend), (((1, 1), vend_nothing), (1, 1), vend_fail)} \<Longrightarrow>
         x \<in> Set.filter (\<lambda>(((origin1, dest1), t1), (origin2, dest2), t2). origin1 = origin2 \<and> t1 < t2 \<and> choice t1 t2)
               (fset (all_pairs (merge_states 1 3 (merge_states 1 2 drinks2))))"
      by (metis (no_types, lifting) bot_fset.rep_eq doubleton_eq_iff ffilter.rep_eq ffilter_all_pairs_2 finsert.rep_eq)
  qed
  show "Set.filter (\<lambda>(((origin1, dest1), t1), (origin2, dest2), t2). origin1 = origin2 \<and> t1 < t2 \<and> choice t1 t2)
     (fset (all_pairs (merge_states 1 3 (merge_states 1 2 drinks2))))
    \<subseteq> {(((1, 1), vend_nothing), (1, 1), vend), (((1, 1), vend_nothing), (1, 1), vend_fail)}"
    by (metis (no_types, lifting) bot_fset.rep_eq doubleton_eq_iff ffilter.rep_eq ffilter_all_pairs_2 finsert.rep_eq set_eq_subset)
qed
  have abs_fset: "Abs_fset {(((1, 1), vend_nothing), (1, 1), vend), (((1, 1), vend_nothing), (1, 1), vend_fail)} = {|(((1, 1), vend_nothing), (1, 1), vend), (((1, 1), vend_nothing), (1, 1), vend_fail)|}"
    by (metis finsert.rep_eq fset_inverse fset_simps(1))
  show ?thesis
    by (simp add: nondeterministic_pairs_def ffilter_def filter abs_fset )
qed

lemma finsert_vend_nothing_1: "finsert ((1, 1), vend_nothing)
     (ffilter (\<lambda>x. x \<noteq> ((1, 1), vend_fail))
       {|((0, 1), select), ((1, 1), vend_nothing), ((1, 1), coin), ((1, 1), vend_fail), ((1, 3), vend)|}) =
 {|((0, 1), select), ((1, 1), vend_nothing), ((1, 1), coin), ((1, 1), vend_nothing), ((1, 3), vend)|}"
proof-
  have set_filter: "(Set.filter (\<lambda>x. x \<noteq> ((1, 1), vend_fail))
         {((0, 1), select), ((1, 1), vend_nothing), ((1, 1), coin), ((1, 1), vend_fail), ((1, 3), vend)}) =
    {((0, 1), select), ((1, 1), vend_nothing), ((1, 1), coin), ((1, 3), vend)}"
    apply (simp add: Set.filter_def)
    apply safe
    by (simp_all add: transitions)
  have abs_fset: "Abs_fset {((0, 1), select), ((1, 1), vend_nothing), ((1, 1), coin), ((1, 3), vend)} = {|((0, 1), select), ((1, 1), vend_nothing), ((1, 1), coin), ((1, 3), vend)|}"
    by (metis finsert.rep_eq fset_inverse fset_simps(1))
  show ?thesis
    apply (simp add: ffilter_def set_filter abs_fset)
    by auto
qed

lemma select_updates_general: "length (snd h) = 1 \<Longrightarrow> EFSM.apply_updates (Updates select) (case_vname (\<lambda>n. input2state (snd h) 1 (I n)) (\<lambda>n. r (R n))) r = (\<lambda>u. if u = R 1 then Some (hd (snd h)) else if u = R 2 then Some (Num 0) else r u)"
  apply (rule ext)
  apply (simp add: select_def)
  using hd_input2state by auto

lemma select_updates_simp: "(\<lambda>u. if u = R 1 then Some (hd (snd (aa, b))) else if u = R 2 then Some (Num 0) else None) =
(\<lambda>u. if u = R 1 then Some (hd b) else if u = R 2 then Some (Num 0) else None)"
  apply (rule ext)
  by simp

lemma coin_updates_1:  "(EFSM.apply_updates (Updates coin)
          (case_vname (\<lambda>n. input2state b 1 (I n)) (\<lambda>n. if n = 2 then Some (Num 0) else <R 1 := hd bb> (R n)))
          <R 1 := hd bb, R 2 := Num 0>) = (\<lambda>u. if u = R 1 then Some (hd bb)
     else if u = R 2 then value_plus (Some (Num 0)) (input2state b 1 (I 1)) else None)"
  apply (rule ext)
  by (simp add: coin_def)

lemma step_2_or_3: "step drinks2 2 r a b = Some (uw, s', ux, r') \<Longrightarrow> s' = 2 \<or> s' = 3"
  apply (simp add: step_def)
  apply (case_tac "a = ''coin'' \<and> length b = 1")
   apply simp
  using drinks2_2_coin
   apply auto[1]
  apply simp
  apply (case_tac "a = ''vend'' \<and> b = []")
   apply simp
   apply clarify
   apply (case_tac "r (R 2)")
    apply (simp add: r_R2_none)
   apply (case_tac aa)
    apply (case_tac "x1 \<ge> 100")
     apply (simp add: drinks2_vend_sufficient)
    apply (simp add: drinks2_vend_insufficient2)
   apply (simp add: drinks2_vend_r2_String)
  using drinks2_2_invalid
  by auto

lemma no_route_from_3_to_1: "\<forall>r. \<not> gets_us_to 1 drinks2 3 r lst"
proof (induct lst)
  case Nil
  then show ?case
    apply safe
    apply (rule gets_us_to.cases)
    by auto
next
  case (Cons a lst)
  then show ?case
    apply safe
    apply (rule gets_us_to.cases)
       apply simp
      apply simp
     apply simp
     apply clarify
     apply simp
     apply (simp add: step_def)
    using drinks2_end
     apply auto[1]
    by simp
qed

lemma no_route_from_2_to_1: "\<forall>r. \<not> gets_us_to 1 drinks2 2 r lst"
proof (induct lst)
  case Nil
  then show ?case
    apply safe
    apply (rule gets_us_to.cases)
    by auto
next
  case (Cons a lst)
  then show ?case
    apply safe
    apply (rule gets_us_to.cases)
       apply simp
      apply simp
    defer
     apply simp
    apply simp
    apply clarify
    apply simp
    apply (case_tac "s'=2")
    apply simp
    apply (case_tac "s'=3")
    defer
    using step_2_or_3
     apply blast
    apply simp
    using no_route_from_3_to_1
    by simp
qed

lemma coin_step:  "length b = 1 \<Longrightarrow>
   \<not> gets_us_to 1 drinks2 1 r ((''coin'', b) # list)"
  apply safe
  apply (rule gets_us_to.cases)
     apply simp
    apply simp
   apply simp
   apply clarify
   apply (simp add: step_def possible_steps_1)
   apply clarify
   apply simp
  using no_route_from_2_to_1
   apply simp
  apply simp
  apply clarify
  apply simp
  by (simp add: step_def possible_steps_1)

lemma no_more_coins: "length b = 1 \<Longrightarrow> \<not>gets_us_to 1 drinks2 1 r ((''coin'', b) # list)"
proof (induct list)
  case Nil
  then show ?case
    apply safe
    apply (rule gets_us_to.cases)
       apply simp
      apply simp
     apply clarify
     apply (simp add: step_def possible_steps_1)
     apply clarify
    using no_route_from_2_to_1
     apply simp
    apply simp
    apply clarify
    by (simp add: step_def possible_steps_1)
next
  case (Cons a list)
  then show ?case
    apply simp
    apply clarify
    apply (rule gets_us_to.cases)
       apply simp
      apply simp
     apply clarify
     apply simp
     apply (simp add: step_def possible_steps_1)
    apply clarify
     apply simp
     apply (simp add: coin_step)
    apply (simp add: coin_step)
    apply clarify
    by (simp add: coin_step)
qed

lemma posterior_vend_nothing_cons: "posterior_sequence select_posterior drinks2 1 <R 1 := hd bb, R 2 := Num 0> ((''vend'', []) # xs) =
posterior_sequence select_posterior drinks2 1 <R 1 := hd bb, R 2 := Num 0> xs"
proof-
  have updates: "(EFSM.apply_updates (Updates vend_nothing) (case_vname Map.empty (\<lambda>n. if n = 2 then Some (Num 0) else <R 1 := hd bb> (R n)))
       <R 1 := hd bb, R 2 := Num 0>) = <R 1 := hd bb, R 2 := Num 0>"
    apply (rule ext)
    by (simp add: vend_nothing_def)
  show ?thesis
  apply simp
  apply (simp add: step_def drinks2_vend_insufficient)
    by (simp add: vend_nothing_posterior updates)
qed

lemma vend_nothing_does_nothing: "gets_us_to 1 drinks2 1 <R 1 := hd bb, R 2 := Num 0> ((''vend'', []) # x) = gets_us_to 1 drinks2 1 <R 1 := hd bb, R 2 := Num 0> x"
proof
  have updates: "EFSM.apply_updates (Updates vend_nothing)
        (case_vname Map.empty (\<lambda>n. if n = 2 then Some (Num 0) else <R 1 := hd bb> (R n))) <R 1 := hd bb, R 2 := Num 0> = <R 1 := hd bb, R 2 := Num 0>"
    apply (rule ext)
    by (simp add: vend_nothing_def)
  show " gets_us_to 1 drinks2 1 <R 1 := hd bb, R 2 := Num 0> ((''vend'', []) # x) \<Longrightarrow>
    gets_us_to 1 drinks2 1 <R 1 := hd bb, R 2 := Num 0> x"
    apply (rule gets_us_to.cases)
       apply simp
      apply simp
     apply clarify
     apply (simp add: step_def drinks2_vend_insufficient outputs_vend_nothing updates)
    apply clarify
    by (simp add: step_def drinks2_vend_insufficient)
  show "gets_us_to 1 drinks2 1 <R 1 := hd bb, R 2 := Num 0> x \<Longrightarrow>
    gets_us_to 1 drinks2 1 <R 1 := hd bb, R 2 := Num 0> ((''vend'', []) # x)"
    apply (rule gets_us_to.step_some)
     apply (simp add: step_def drinks2_vend_insufficient outputs_vend_nothing updates)
    by simp
qed

lemma coin_takes_us_away: "gets_us_to 1 drinks2 1 <R 1 := hd bb, R 2 := Num 0> (x # xs) \<Longrightarrow> fst x = ''coin'' \<and> length (snd x) = 1 \<Longrightarrow> False"
  apply (rule gets_us_to.cases)
     apply simp
    apply simp
   apply clarify
   apply (simp add: step_def possible_steps_1)
  using no_route_from_2_to_1
   apply simp
  apply simp
  by (simp add: step_def possible_steps_1)

definition basically_drinks :: transition_matrix where
  "basically_drinks = {|((1, 1), vend_fail), ((0, 1), select), ((1, 1), coin), ((1, 1), vend_fail), ((1, 3), vend)|}"

lemma possible_steps_merge_coin: "length i = 1 \<Longrightarrow> possible_steps (merge_states 1 2 drinks2) 1 r ''coin'' i = {|(1, coin)|}"
proof-
  assume premise: "length i = 1"
  have set_filter: "Set.filter
       (\<lambda>((origin, dest), t).
           origin = 1 \<and>
           Label t = ''coin'' \<and>
           length i = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))))
       (fset (merge_states 1 2 drinks2)) = {((1, 1), coin)}"
    using premise
    apply (simp add: merge_states_1_2 Set.filter_def)
    apply safe
    by (simp_all add: transitions)
  show ?thesis
    by (simp add: possible_steps_def ffilter_def set_filter)
qed

lemma step_merge_1_2_select: "(aa = ''select'' \<and> length b = 1) \<Longrightarrow> step (merge_states 1 2 drinks2) 0 Map.empty aa b = Some (select, 1, [], <R 1 := hd b, R 2 := Num 0>)"
proof-
  assume premise: "(aa = ''select'' \<and> length b = 1)"
  show ?thesis
    using premise
    apply (simp add: step_def possible_steps_0_2)
    apply (simp add: select_def)
    apply (rule ext)
    by (simp add: hd_input2state)
qed

lemma step_merge_1_2_0_invalid: "\<not> (aa = ''select'' \<and> length b = 1) \<Longrightarrow> step (merge_states 1 2 drinks2) 0 Map.empty aa b = None"
proof-
  assume premise: "\<not> (aa = ''select'' \<and> length b = 1)"
  have set_filter: "Set.filter
         (\<lambda>((origin, dest), t).
             origin = 0 \<and> Label t = aa \<and> length b = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) Map.empty))
         (fset (merge_states 1 2 drinks2)) = {}"
    using premise
    apply (simp add: Set.filter_def merge_states_1_2)
    apply safe
    by (simp_all add: transitions)
  show ?thesis
    by (simp add: step_def possible_steps_def ffilter_def set_filter)
qed

lemma select_first: "\<not> (aa = ''select'' \<and> length b = 1) \<Longrightarrow> \<not>gets_us_to 1 drinks2 0 Map.empty ((aa, b) # p)"
proof-
  assume premise: "\<not> (aa = ''select'' \<and> length b = 1)"
  show ?thesis
    apply safe
    apply (rule gets_us_to.cases)
       apply simp
      apply simp
     apply clarify
    apply (simp add: step_def)
    using premise drinks2_0_invalid
    by auto
qed

lemma select_updates: "length b = 1 \<Longrightarrow> (EFSM.apply_updates (Updates select) (case_vname (\<lambda>n. input2state b 1 (I n)) Map.empty) Map.empty) = <R 1 := hd b, R 2 := Num 0>"
  apply (rule ext)
  by (simp add: select_def hd_input2state)

lemma step_drinks_2: "step drinks2 0 Map.empty aa ba = Some (uw, s', ux, r') \<Longrightarrow> (uw, s', ux, r') = (select, 1, [], <R 1 := hd ba, R 2 := Num 0>)"
  apply (simp add: step_def)
  apply (case_tac "aa = ''select'' \<and> length ba = 1")
   apply (simp add: possible_steps_0)
   apply clarify
   apply (simp add: select_def)
   apply (rule ext)
   apply (simp add: hd_input2state)
  by (simp add: drinks2_0_invalid)

lemma update_simp: "(\<lambda>x. if x = R 1
            then aval (snd (R 1, V (R 1))) (case_vname Map.empty (\<lambda>n. if n = 2 then Some (Num 0) else if R n = R 1 then Some d else None))
            else EFSM.apply_updates [(R 2, V (R 2))]
                  (case_vname Map.empty (\<lambda>n. if n = 2 then Some (Num 0) else if R n = R 1 then Some d else None))
                  (\<lambda>a. if a = R 2 then Some (Num 0) else if a = R 1 then Some d else None) x) = <R 1 := d, R 2 := Num 0>"
  apply (rule ext)
  by simp

lemma possible_steps_merge_1_2_vend: "possible_steps (merge_states 1 2 drinks2) 1 (\<lambda>a. if a = R 2 then Some (Num 0) else if a = R 1 then Some d else None) ''vend'' [] = {|(1, vend_fail), (1, vend_nothing)|}" 
proof-
  have set_filter: "(Set.filter
       (\<lambda>((origin, dest), t).
           origin = 1 \<and>
           Label t = ''vend'' \<and>
           Arity t = 0 \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state [] 1 (I n)) (\<lambda>n. (\<lambda>a. if a = R 2 then Some (Num 0) else if a = R 1 then Some d else None) (R n))))
       (fset (merge_states 1 2 drinks2))) = {((1, 1), vend_nothing), ((1, 1), vend_fail)}"
    apply (simp add: Set.filter_def merge_states_1_2)
    apply safe
    by (simp_all add: transitions)
  have abs_fset: "Abs_fset {((1, 1), vend_nothing), ((1, 1), vend_fail)} =  {|((1, 1), vend_nothing), ((1, 1), vend_fail)|}"
    by (metis finsert.rep_eq fset_inverse fset_simps(1))
  show ?thesis
    apply (simp add: possible_steps_def ffilter_def set_filter abs_fset)
    by auto
qed

lemma step_merge_1_2_vend_nothing: "\<nexists>n. ra (R 2) = Some (Num n) \<Longrightarrow>
       step (merge_states 1 2 drinks2) 1 ra ''vend'' [] = Some (vend_nothing, 1, [], ra)"
proof-
  assume premise: "\<nexists>n. ra (R 2) = Some (Num n)"
  have set_filter: "Set.filter
          (\<lambda>((origin, dest), t).
              origin = 1 \<and> Label t = ''vend'' \<and> Arity t = 0 \<and> apply_guards (Guard t) (case_vname Map.empty (\<lambda>n. ra (R n))))
          (fset (merge_states 1 2 drinks2)) = {((1, 1), vend_nothing)}"
    using premise
    apply (simp add: Set.filter_def merge_states_1_2)
    apply safe
           apply (simp_all add: transitions)
      apply (metis MaybeBoolInt.elims option.simps(3))
     apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some (Num 100)) (ra (R 2))")
      apply simp
     apply simp
     apply (metis MaybeBoolInt.elims option.simps(3))
    apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some (Num 100)) (ra (R 2))")
     apply simp
    apply simp
    by (metis MaybeBoolInt.elims option.simps(3))
  show ?thesis
    apply (simp add: step_def possible_steps_def ffilter_def set_filter)
    apply (simp add: set_filter)
    apply (simp add: vend_nothing_def)
    apply (rule ext)
    by simp
qed

lemma step_drinks2_vend_fail: "step drinks2 1 ra ''vend'' [] = Some (vend_nothing, 1, [], ra)"
  apply (simp add: step_def drinks2_vend_insufficient)
  apply (simp add: vend_nothing_def)
  apply (rule ext)
  by simp

lemma step_merge_1_2_vend: "d' (R 2) = Some (Num x1) \<Longrightarrow>
       x1 < 100 \<Longrightarrow>
       step (merge_states 1 2 drinks2) 1 d' ''vend'' [] = None"
proof-
  assume premise1: "d' (R 2) = Some (Num x1)"
  assume premise2: "x1 < 100"
  have set_filter: "Set.filter
               (\<lambda>((origin, dest), t).
                   origin = 1 \<and>
                   Label t = ''vend'' \<and> Arity t = 0 \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state [] 1 (I n)) (\<lambda>n. d' (R n))))
               (fset (merge_states 1 2 drinks2)) = {((1, 1), vend_fail), ((1, 1), vend_nothing)}"
    using premise1 premise2
    apply (simp add: Set.filter_def merge_states_1_2)
    apply safe
    by (simp_all add: transitions)
  have abs_fset: "Abs_fset {((1, 1), vend_fail), ((1, 1), vend_nothing)} = {|((1, 1), vend_fail), ((1, 1), vend_nothing)|}"
    by (metis finsert.rep_eq fset_inverse fset_simps(1))
  show ?thesis
    apply (simp add: step_def possible_steps_def ffilter_def set_filter abs_fset fis_singleton_def is_singleton_def)
    by (simp add: transitions)
qed

lemma step_merge_1_2_vend_2: "d' (R 2) = Some (Num n) \<Longrightarrow> n \<ge> 100 \<Longrightarrow> step (merge_states 1 2 drinks2) 1 d' ''vend'' [] = None"
proof-
  assume premise1: "d' (R 2) = Some (Num n)"
  assume premise2: "n \<ge> 100"
  have set_filter: "Set.filter
       (\<lambda>((origin, dest), t).
           origin = 1 \<and> Label t = ''vend'' \<and> Arity t = 0 \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state [] 1 (I n)) (\<lambda>n. d' (R n))))
       (fset (merge_states 1 2 drinks2)) = {((1, 3), vend), ((1, 1), vend_nothing)}"
    using premise1 premise2
    apply (simp add: Set.filter_def merge_states_1_2)
    apply safe
    by (simp_all add: transitions)
  have abs_fset: "Abs_fset {((1, 3), vend), ((1, 1), vend_nothing)} = {|((1, 3), vend), ((1, 1), vend_nothing)|}"
    by (metis finsert.rep_eq fset_inverse fset_simps(1))
  show ?thesis
    by (simp add: step_def possible_steps_def ffilter_def set_filter abs_fset fis_singleton_def is_singleton_def)
qed

lemma gets_us_to_aux: "\<forall>r. gets_us_to 1 drinks2 1 r p \<longrightarrow>
       accepts drinks2 1 r p \<longrightarrow>
       posterior_sequence select_posterior (merge_states 1 2 drinks2) 1 r p = select_posterior"
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

lemma directly_subsumes_aux: "accepts_trace drinks2 p \<Longrightarrow> gets_us_to 1 drinks2 0 Map.empty p \<Longrightarrow>
anterior_context (merge_states 1 2 drinks2) p = select_posterior"
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
     apply (case_tac "step drinks2 0 Map.empty aa ba = Some (select, 1, [], <R 1 := hd ba, R 2 := Num 0>)")
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

lemma vend_fail_directly_subsumes_vend_nothing: "directly_subsumes drinks2 (merge_states 1 2 drinks2) 1 vend_fail vend_nothing"
  by (simp add: directly_subsumes_def directly_subsumes_aux vend_fail_subsumes_vend_nothing)

lemma merge_transitions: "merge_transitions drinks2 (merge_states 1 2 drinks2) 1 2 1 1 1 vend_nothing vend_fail null_generator null_modifier a = Some basically_drinks"
proof-
  have set_filter: "Set.filter (\<lambda>x. x \<noteq> ((1, 1), vend_nothing))
         {((0, 1), select), ((1, 1), vend_nothing), ((1, 1), coin), ((1, 1), vend_fail), ((1, 3), vend)} =
 {((0, 1), select), ((1, 1), coin), ((1, 1), vend_fail), ((1, 3), vend)}"
    apply (simp add: Set.filter_def)
    apply safe
    by (simp_all add: transitions)
  have abs_fset: "Abs_fset {((0, 1), select), ((1, 1), coin), ((1, 1), vend_fail), ((1, 3), vend)} =
 {|((0, 1), select), ((1, 1), coin), ((1, 1), vend_fail), ((1, 3), vend)|}"
    by (metis finsert.rep_eq fset_inverse fset_simps(1))
  show ?thesis
    apply (simp add: merge_transitions_def easy_merge_def)
    apply (simp add: vend_fail_directly_subsumes_vend_nothing)
    apply (simp add: merge_states_1_2 replace_transition_def ffilter_def)
    by (simp add: set_filter abs_fset basically_drinks_def)
qed

lemma vend_fail_exits_1: "exits_state (merge_states 1 2 drinks2) vend_fail 1"
proof-
  show ?thesis
    apply (simp add: exits_state_def merge_states_1_2)
    by auto
qed

lemma step_merged_2_select: "step (merge_states 1 3 (merge_states 1 2 drinks2)) 0 Map.empty ''select'' [d] = Some (select, 1, [], <R 1 := d, R 2 := Num 0>)"
proof-
  have set_filter: "Set.filter
          (\<lambda>((origin, dest), t).
              origin = 0 \<and>
              Label t = ''select'' \<and>
              Suc 0 = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. if n = 1 then Some d else input2state [] (1 + 1) (I n)) Map.empty))
          (fset (merge_states 1 3 (merge_states 1 2 drinks2))) = {((0, 1), select)}"
    apply (simp add: Set.filter_def merge_1_3_2)
    apply safe
    by (simp_all add: transitions)
  show ?thesis
    apply (simp add: step_def possible_steps_def ffilter_def set_filter)
    apply (simp add: set_filter)
    apply (simp add: select_def)
    apply (rule ext)
    by simp
qed

lemma satisfies_must_have_r2_0: "satisfies_context d \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> \<Longrightarrow> d (R 2) = Some (Num 0)"
proof-
  have contrapositive: "\<not> d (R 2) = Some (Num 0) \<Longrightarrow> \<not>satisfies_context d \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk>"
    apply (simp add: satisfies_context_def datastate2context_def consistent_def)
    apply (rule allI)
    apply (rule_tac x="V (R 2)" in exI)
    apply simp
    apply (case_tac "d (R 2)")
     apply simp
    by simp
  show "satisfies_context d \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> \<Longrightarrow> d (R 2) = Some (Num 0)"
    using contrapositive
    by auto
qed

lemma inconsistent_medial_vend: "\<not>consistent \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> And (cexp.Eq (Num 0)) (Geq (Num 100))\<rbrakk>"
  apply (simp add: consistent_def)
  apply clarify
  apply (rule_tac x="V (R 2)" in exI)
  apply simp
  apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some (Num 100)) (s (R 2))")
   apply simp
  apply simp
  by auto

lemma posterior_vend_false: "posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> And (cexp.Eq (Num 0)) (Geq (Num 100))\<rbrakk> vend_nothing = (\<lambda>x. Bc False)"
  apply (simp add: posterior_def)
  by (simp add: vend_nothing_def Let_def inconsistent_medial_vend)

lemma no_subsumption_vend_nothing_vend: "\<not>subsumes c vend_nothing vend"
  by (simp add: subsumes_def transitions)

lemma vend_nothing_doesn_directly_subsume_vend: "\<not> directly_subsumes (merge_states 1 2 drinks2) (merge_states 1 3 (merge_states 1 2 drinks2)) 1 vend_nothing vend"
  apply (simp add: directly_subsumes_def subsumes_def transitions accepts_trace_def)
  apply (rule_tac x="[(''select'', [d])]" in exI)
  apply standard
   apply (rule accepts.step)
    apply (simp add: step_merge_1_2_select)
   apply (simp add: accepts.base)
  apply (rule gets_us_to.step_some)
    apply (simp add: step_merge_1_2_select)
  by (simp add: gets_us_to.base)

lemma vend_doesn_directly_subsume_vend_nothing: "\<not> directly_subsumes (merge_states 1 2 drinks2) (merge_states 1 3 (merge_states 1 2 drinks2)) 1 vend vend_nothing"
  apply (simp add: directly_subsumes_def subsumes_def transitions accepts_trace_def)
  apply (rule_tac x="[(''select'', [d])]" in exI)
  apply standard
   apply (rule accepts.step)
    apply (simp add: step_merge_1_2_select)
   apply (simp add: accepts.base)
  apply (rule gets_us_to.step_some)
    apply (simp add: step_merge_1_2_select)
  by (simp add: gets_us_to.base)

lemma merge_1_2: "merge drinks2 1 2 null_generator null_modifier = Some basically_drinks"
proof-
  have nondeterminism_merge_states_1_2: "nondeterminism (merge_states 1 2 drinks2)"
    unfolding nondeterminism_def
    using vend_vend_nothing_nondeterminism by auto
  have merge_vend_nothing_vend: "\<forall>a. merge_transitions (merge_states 1 2 drinks2) (merge_states 1 3 (merge_states 1 2 drinks2)) 1 1 1 1 1 vend_nothing
             vend null_generator null_modifier a = None"
    apply (simp add: merge_transitions_def null_generator_def null_modifier_def easy_merge_def)
    by (simp add: vend_nothing_doesn_directly_subsume_vend vend_doesn_directly_subsume_vend_nothing)
  have vend_fail_lt_vend: "vend_fail < vend"
    using vend_fail_leq_vend vend_neq_vend_fail by auto
  have vend_fail_lt_vend_2: "\<not>vend \<le> vend_fail"
    using vend_fail_lt_vend by auto
  have fmax: "fMax
           ({|(1::nat, (1::nat, 3::nat), vend_nothing, vend), (1, (1, 1), vend_nothing, vend_fail)|} |-|
            {|max (1, (1, 3), vend_nothing, vend) (1, (1, 1), vend_nothing, vend_fail)|}) = (1, (1, 1), vend_nothing, vend_fail)"
    apply (simp add: fMax_def max_def )
    by (simp add: fMax.semilattice_fset_axioms semilattice_fset.singleton)
  show ?thesis
    unfolding easy_merge_def
    apply (simp add: Let_def nondeterminisitic_pairs nondeterminism_def max_def)
    apply (simp add: nondeterministic_pairs_1_3 max_def)
    apply (simp add: vend_nothing_exits_1_2 vend_exits_1 nondeterminsm_merge_1_3 nondeterminism_merge_states_1_2 )
    apply (simp add: merge_vend_nothing_vend max_def vend_fail_exits_1 vend_fail_lt_vend_2)
    by (simp add: merge_transitions)
qed

lemma make_pta_test: "make_pta [[(''select'', [Str ''coke''], [])]] {||} = {|((0, 1), \<lparr>Label=''select'', Arity=1, Guard=[gexp.Eq (V (I 1)) (L (Str ''coke''))], Outputs=[], Updates=[]\<rparr>)|}"
  by simp

lemma scoring: "rev (sorted_list_of_fset (score drinks2 naive_score)) = [(3, 1, 2), (0, 2, 3), (0, 1, 3), (0, 0, 3), (0, 0, 2), (0, 0, 1)]"
proof-
  have set_filter: "(Set.filter (\<lambda>(x, y). x < y)
       {(2::nat, 1::nat), (2, 2), (2, 3), (2, 0), (2, 1), (2, 2), (1, 1), (1, 2), (1, 3), (1, 0), (1, 1), (1, 2), (0, 1), (0, 2), (0, 3),
        (0, 0), (0, 1), (0, 2), (3, 1), (3, 2), (3, 3), (3, 0), (3, 1), (3, 2), (2, 1), (2, 2), (2, 3), (2, 0), (2, 1), (2, 2),
        (1, 1), (1, 2), (1, 3), (1, 0), (1, 1), (1, 2)}) =
    {(2, 3), (1, 3), (1, 2), (0, 3), (0, 2), (0, 1)}"
    apply (simp add: Set.filter_def)
    by auto
  have ffilter: "ffilter (\<lambda>(x, y). x < y) (all_pairs (S drinks2)) = {|(2, 3), (1, 3), (1, 2), (0, 3), (0, 2), (0, 1)|}"
    apply (simp add: drinks2_def all_pairs_def S_def)
    apply (simp add: ffilter_def set_filter)
    by (metis finsert.rep_eq fset_inverse fset_simps(1))

  have outgoing_transitions_0: "(outgoing_transitions 0 drinks2) = {|select|}"
  proof-
    have set_filter: "(Set.filter (\<lambda>((origin, dest), t). origin = 0)
       {((0::nat, 1::nat), select), ((1, 1), vend_nothing), ((1, 2), coin), ((2, 2), coin), ((2, 2), vend_fail), ((2, 3), vend)}) =
       {((0, 1), select)}"
      apply (simp add: Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    have abs_fset: "Abs_fset {((0, 1), select)} = {|((0, 1), select)|}"
      by (metis finsert.rep_eq fset_inverse fset_simps(1))
    show ?thesis
      by (simp add: outgoing_transitions_def drinks2_def ffilter_def set_filter abs_fset)
  qed
  have outgoing_transitions_1: "(outgoing_transitions 1 drinks2) = {|coin, vend_nothing|}"
  proof-
    have set_filter: "(Set.filter (\<lambda>((origin, dest), t). origin = 1)
       {((0::nat, 1::nat), select), ((1, 1), vend_nothing), ((1, 2), coin), ((2, 2), coin), ((2, 2), vend_fail), ((2, 3), vend)}) =
       {((1, 1), vend_nothing), ((1, 2), coin)}"
      apply (simp add: Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    have abs_fset: "Abs_fset {((1, 1), vend_nothing), ((1, 2), coin)} = {|((1, 1), vend_nothing), ((1, 2), coin)|}"
      by (metis finsert.rep_eq fset_inverse fset_simps(1))
    show ?thesis
      apply (simp add: outgoing_transitions_def drinks2_def ffilter_def set_filter abs_fset)
      by auto
  qed
  have outgoing_transitions_2: "(outgoing_transitions 2 drinks2) = {|coin, vend_fail, vend|}"
  proof-
    have set_filter: "(Set.filter (\<lambda>((origin, dest), t). origin = 2)
       {((0::nat, 1::nat), select), ((1, 1), vend_nothing), ((1, 2), coin), ((2, 2), coin), ((2, 2), vend_fail), ((2, 3), vend)}) =
       {((2, 2), coin), ((2, 2), vend_fail), ((2, 3), vend)}"
      apply (simp add: Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    have abs_fset: "Abs_fset {((2, 2), coin), ((2, 2), vend_fail), ((2, 3), vend)} = {|((2, 2), coin), ((2, 2), vend_fail), ((2, 3), vend)|}"
      by (metis finsert.rep_eq fset_inverse fset_simps(1))
    show ?thesis
      by (simp add: outgoing_transitions_def drinks2_def ffilter_def set_filter abs_fset)
  qed
  have outgoing_transitions_3: "(outgoing_transitions 3 drinks2) = {||}"
  proof-
    have set_filter: "(Set.filter (\<lambda>((origin, dest), t). origin = 3)
       {((0::nat, 1::nat), select), ((1, 1), vend_nothing), ((1, 2), coin), ((2, 2), coin), ((2, 2), vend_fail), ((2, 3), vend)}) = {}"
      apply (simp add: Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: outgoing_transitions_def drinks2_def ffilter_def set_filter)
  qed
  have naive_score_1_2: "naive_score {|coin, vend_nothing|} {|coin, vend_fail, vend|} = 3"
  proof-
    have abs_fset: "Abs_fset
         {(coin, coin), (coin, vend_fail), (coin, vend), (vend_nothing, vend), (vend_nothing, vend_fail), (vend_nothing, vend),
          (vend_nothing, coin), (vend_nothing, vend_fail), (vend_nothing, vend)} = {|(coin, coin), (coin, vend_fail), (coin, vend), (vend_nothing, vend), (vend_nothing, vend_fail), (vend_nothing, vend),
          (vend_nothing, coin), (vend_nothing, vend_fail), (vend_nothing, vend)|}"
      by (metis finsert.rep_eq fset_inverse fset_simps(1))
    have fprod: "(fprod {|coin, vend_nothing|} {|coin, vend_fail, vend|}) = {|(coin, coin), (coin, vend_fail), (coin, vend), (vend_nothing, vend), (vend_nothing, vend_fail), (vend_nothing, vend),
      (vend_nothing, coin), (vend_nothing, vend_fail), (vend_nothing, vend)|}"
      by (simp add: fprod_def abs_fset)
    have set_filter: "(Set.filter (\<lambda>(x, y). Label x = Label y \<and> Arity x = Arity y)
       {(coin, coin), (coin, vend_fail), (coin, vend), (vend_nothing, vend), (vend_nothing, vend_fail), (vend_nothing, vend),
        (vend_nothing, coin), (vend_nothing, vend_fail), (vend_nothing, vend)}) =
    {(coin, coin), (vend_nothing, vend), (vend_nothing, vend_fail), (vend_nothing, vend), (vend_nothing, vend_fail),
      (vend_nothing, vend)}"
      apply (simp add: Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    have ffilter: "(ffilter (\<lambda>(x, y). Label x = Label y \<and> Arity x = Arity y)
       {|(coin, coin), (coin, vend_fail), (coin, vend), (vend_nothing, vend), (vend_nothing, vend_fail), (vend_nothing, vend),
         (vend_nothing, coin), (vend_nothing, vend_fail), (vend_nothing, vend)|}) =
        {|(coin, coin), (vend_nothing, vend), (vend_nothing, vend_fail), (vend_nothing, vend), (vend_nothing, vend_fail), (vend_nothing, vend)|}"
      apply (simp add: ffilter_def set_filter)
      by (metis finsert.rep_eq fset_inverse fset_simps(1))
    have smaller: "{|(coin, coin), (vend_nothing, vend), (vend_nothing, vend_fail), (vend_nothing, vend), (vend_nothing, vend_fail),
       (vend_nothing, vend)|} = {|(coin, coin), (vend_nothing, vend), (vend_nothing, vend_fail)|}"
      by auto
    show ?thesis
      apply (simp only: naive_score_def fprod ffilter smaller)
      by (simp add: transitions)
  qed
  have naive_score_0_2: "naive_score {|select|} {|coin, vend_fail, vend|} = 0"
  proof-
    have abs_fset: "Abs_fset {(select, coin), (select, vend_fail), (select, vend)} = {|(select, coin), (select, vend_fail), (select, vend)|}"
      by (metis finsert.rep_eq fset_inverse fset_simps(1))
    show ?thesis
      unfolding naive_score_def
      apply (simp add: fprod_def abs_fset)
      by (simp add: transitions)
  qed
  have naive_score_0_1: "naive_score {|select|} {|coin, vend_nothing|} = 0"
  proof-
    have abs_fset: "Abs_fset {(select, coin), (select, vend_nothing)} = {|(select, coin), (select, vend_nothing)|}"
      by (metis finsert.rep_eq fset_inverse fset_simps(1))
    show ?thesis
      unfolding naive_score_def
      apply (simp add: fprod_def abs_fset)
      by (simp add: transitions)
  qed
  have scoring: "(score drinks2 naive_score) = {|(0, 2, 3), (0, 1, 3), (3, 1, 2), (0, 0, 3), (0, 0, 2), (0, 0, 1)|}"
    apply (simp add: score_def ffilter)
    apply (simp only: outgoing_transitions_0 outgoing_transitions_1 outgoing_transitions_2 outgoing_transitions_3)
    by (simp add: naive_score_empty naive_score_empty_2 naive_score_1_2 naive_score_0_2 naive_score_0_1)
  show ?thesis
    by (simp add: scoring sorted_list_of_fset_def)
qed

lemma scoring_2: "(rev (sorted_list_of_fset (score basically_drinks naive_score))) = [ (0, 1, 3), (0, 0, 3), (0, 0, 1)]"
proof-
  have set_filter: "(Set.filter (\<lambda>(x, y). x < y)
       {(1::nat, 1::nat), (1, 3), (1, 1), (1, 0), (1, 1), (0, 1), (0, 3), (0, 1), (0, 0), (0, 1), (1, 1), (1, 3), (1, 1), (1, 0), (1, 1),
        (3, 1), (3, 3), (3, 1), (3, 0), (3, 1), (1, 1), (1, 3), (1, 1), (1, 0), (1, 1)}) =
    {(0, 3), (0, 1), (1, 3)}"
    apply (simp add: Set.filter_def)
    by auto
  have ffilter: "ffilter (\<lambda>(x, y). x < y)
     {|(1::nat, 1::nat), (1, 3), (1, 1), (1, 0), (1, 1), (0, 1), (0, 3), (0, 1), (0, 0), (0, 1), (1, 1), (1, 3), (1, 1), (1, 0), (1, 1),
       (3, 1), (3, 3), (3, 1), (3, 0), (3, 1), (1, 1), (1, 3), (1, 1), (1, 0), (1, 1)|} = {|(0, 3), (0, 1), (1, 3)|}"
    apply (simp add: ffilter_def set_filter)
    by (metis finsert.rep_eq fset_inverse fset_simps(1))
  have all_pairs: "ffilter (\<lambda>(x, y). x < y) (all_pairs (S basically_drinks)) = {|(0, 3), (0, 1), (1, 3)|}"
    by (simp add: S_def basically_drinks_def all_pairs_def ffilter)
  have outgoing_transitions_3: "outgoing_transitions 3 basically_drinks = {||}"
  proof-
    have set_filter: "(Set.filter (\<lambda>((origin, dest), t). origin = 3)
       {((1::nat, 1::nat), vend_fail), ((0, 1), select), ((1, 1), coin), ((1, 1), vend_fail), ((1, 3), vend)}) = {}"
      apply (simp add: Set.filter_def)
      by auto
    show ?thesis
      by (simp add: outgoing_transitions_def basically_drinks_def ffilter_def set_filter)
  qed
  have outgoing_transitions_0: "outgoing_transitions 0 basically_drinks = {|select|}"
  proof-
    have set_filter: "Set.filter (\<lambda>((origin, dest), t). origin = 0) (fset basically_drinks) = {((0, 1), select)}"
      apply (simp add: basically_drinks_def Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: outgoing_transitions_def ffilter_def set_filter)
  qed
  have outgoing_transitions_1: "outgoing_transitions 1 basically_drinks = {|coin, vend_fail, vend|}"
  proof-
    have set_filter: "Set.filter (\<lambda>((origin, dest), t). origin = 1) (fset basically_drinks) =
    {((1, 1), coin), ((1, 1), vend_fail), ((1, 3), vend)}"
      apply (simp add: Set.filter_def basically_drinks_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      apply (simp add: outgoing_transitions_def ffilter_def set_filter)
      by (metis (no_types, lifting) fimage_fempty fimage_finsert finsert.rep_eq fset_inverse fset_simps(1) prod.simps(2))
  qed
  have naive_score_0_1: "naive_score {|select|} {|coin, vend_fail, vend|} = 0"
  proof-
    have abs_fset: "Abs_fset {(select, coin), (select, vend_fail), (select, vend)} = {|(select, coin), (select, vend_fail), (select, vend)|}"
      by (metis finsert.rep_eq fset_inverse fset_simps(1))
    show ?thesis
      apply (simp add: naive_score_def fprod_def abs_fset)
      by (simp add: transitions)
  qed
  have scoring: "score basically_drinks naive_score = {|(0, 0, 3), (0, 0, 1), (0, 1, 3)|}"
    apply (simp add: score_def all_pairs)
    by (simp add: outgoing_transitions_3 naive_score_empty outgoing_transitions_0 outgoing_transitions_1 naive_score_0_1)
  show ?thesis
    apply simp
    by (simp add: scoring sorted_list_of_fset_def)
qed

lemma "infer drinks2 naive_score null_generator null_modifier = basically_drinks"
proof-
  have first_step: "inference_step drinks2 (rev (sorted_list_of_fset (score drinks2 naive_score))) null_generator null_modifier = Some basically_drinks"
    by (simp add: scoring merge_1_2 del: merge.simps)
  have next_step: "inference_step basically_drinks (rev (sorted_list_of_fset (score basically_drinks naive_score))) null_generator null_modifier = None"
    by (simp add: scoring_2)
  show ?thesis
    apply (simp add: first_step)
    by (simp add: next_step)
qed
end
