theory DM_Inference
imports Inference "../examples/Drinks_Machine_2"
begin

lemma "max coin vend = vend"
  by (simp add: max_def coin_def vend_def less_eq_transition_ext_def less_transition_ext_def)

lemma merge_1_2: "merge_states 1 2 drinks2 = {|
              ((0,1), select),
              ((1,1), vend_nothing),
              ((1,1), coin),
              ((1,1), vend_fail),
              ((1,3), vend)
         |}"
  by (simp add: merge_states_def merge_states_aux_def drinks2_def del: One_nat_def)

lemma defined_drinks2: "(defined drinks2) = {|(0,1), (1,1), (1,2), (2,2), (2,3)|}"
  by (simp add: defined_def drinks2_def)

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
  apply (simp add: merge_1_2 all_pairs_def del: One_nat_def)
  apply safe
                      apply auto[1]
                      apply simp
                      apply auto[1]
                      apply (simp del: One_nat_def)
  using no_choice_vend_coin no_choice_vend_vend_fail vend_nothing_lt_vend apply auto[1]
                      apply auto[1]
                      apply (simp del: One_nat_def)
  using less_imp_le no_choice_vend_coin no_choice_vend_vend_fail vend_nothing_lt_vend apply auto[1]
                      apply auto[1]
                      apply (simp del: One_nat_def)
  using no_choice_vend_coin no_choice_vend_vend_fail vend_nothing_lt_vend apply auto[1]
                      apply (simp del: One_nat_def)
                      defer
                      apply auto[1]
                      apply auto[1]
                      apply auto[1]
                      apply (simp del: One_nat_def)
  using no_choice_vend_coin no_choice_vend_vend_fail vend_nothing_lt_vend apply auto[1]
                      apply auto[1]
                      apply (simp del: One_nat_def)
  using no_choice_vend_coin no_choice_vend_vend_fail vend_nothing_lt_vend apply auto[1]
                      apply auto[1]
                      apply (simp del: One_nat_def)
  using choice_def label_coin label_vend_fail label_vend_nothing no_choice_vend_coin no_choice_vend_vend_fail vend_nothing_lt_vend vend_nothing_lt_vend_fail apply fastforce
                      apply (simp del: One_nat_def)
  using choice_def label_coin label_vend_fail label_vend_nothing no_choice_vend_coin no_choice_vend_vend_fail vend_nothing_lt_vend vend_nothing_lt_vend_fail apply fastforce
                      apply auto[1]
                     apply auto[1]
                    apply auto[1]
                   apply auto[1]
                  apply auto[1]
                 apply (simp del: One_nat_def)
  using choice_symmetry no_choice_vend_coin no_choice_vend_vend_fail zero_neq_one apply blast
                apply auto[1]
               apply (simp del: One_nat_def)
  using less_imp_le no_choice_vend_coin vend_nothing_lt_vend apply auto[1]
              apply (simp del: One_nat_def)
  defer
              apply auto[1]
             apply auto[1]
            apply auto[1]
           apply auto[1]
          apply auto[1]
         apply auto[1]
        apply auto[1]
       apply (simp del: One_nat_def)
  using choice_def label_coin label_vend_fail label_vend_nothing no_choice_vend_coin vend_nothing_lt_vend vend_nothing_lt_vend_fail apply auto[1]
      apply (simp del: One_nat_def)
  using choice_def label_coin label_vend_fail label_vend_nothing no_choice_vend_coin vend_nothing_lt_vend vend_nothing_lt_vend_fail apply auto[1]
     apply (simp add: choice_vend_nothing_vend_fail vend_nothing_lt_vend_fail)
      apply (simp del: One_nat_def)
    apply (simp add: choice_symmetry choice_vend_vend_nothing vend_nothing_lt_vend)
   apply (case_tac "a=1")
    apply (case_tac "b=3")
     apply (simp del: One_nat_def)
  using no_choice_vend_coin no_choice_vend_vend_fail vend_nothing_lt_vend apply auto[1]
    apply (case_tac "b=1")
     apply (simp del: One_nat_def)
  apply (metis (mono_tags, hide_lams) choice_def choice_symmetry label_vend label_vend_fail label_vend_not_coin label_vend_nothing no_choice_vend_vend_fail not_less_iff_gr_or_eq vend_nothing_lt_vend_fail zero_neq_one)
     apply (simp del: One_nat_def)
     apply (simp del: One_nat_def)
   apply auto[1]
  apply (case_tac "a=1")
   apply (case_tac "b=3")
    apply (simp del: One_nat_def)
  using no_choice_vend_coin vend_nothing_lt_vend apply auto[1]
   apply (simp del: One_nat_def)
  apply (case_tac "b=1")
    apply (simp del: One_nat_def)
  using choice_def label_coin label_vend_fail label_vend_nothing no_choice_vend_coin no_choice_vend_vend_fail vend_nothing_lt_vend_fail apply fastforce
    apply (simp del: One_nat_def)
    apply (simp del: One_nat_def)
  by auto

lemma ffilter_all_pairs: "ffilter (\<lambda>(((origin1, dest1), t1), (origin2, dest2), t2). origin1 = origin2 \<and> t1 < t2 \<and> choice t1 t2) (all_pairs (merge_states 1 2 drinks2)) = 
{|
(((1, 1), vend_nothing), (1, 1), vend_fail), 
(((1, 1), vend_nothing), (1, 3), vend)
|}"
  apply (simp add: ffilter_def del: One_nat_def)
  using filter_all_pairs
  by (metis (no_types, lifting) bot_fset.rep_eq finsert.rep_eq fset_inverse)

lemma nondeterminisitic_pairs: "(nondeterministic_pairs (merge_states 1 2 drinks2)) = {|(1, (1, 3), (vend_nothing, vend)), (1, (1, 1), vend_nothing, vend_fail)|}"
  apply (simp add: nondeterministic_pairs_def ffilter_all_pairs del: One_nat_def)
  by auto

lemma vend_nothing_vend_nondeterminism: "(1, (1, 3), (vend_nothing, vend)) |\<in>| nondeterministic_pairs (merge_states 1 2 drinks2)"
  by (simp add: nondeterminisitic_pairs del: One_nat_def)

lemma vend_vend_nothing_nondeterminism: "nondeterministic_pairs (merge_states 1 2 drinks2) \<noteq> {||}"
  by (simp add: nondeterminisitic_pairs del: One_nat_def)

lemma vend_nothing_vend_fail_nondeterminism: "(1, (1, 1), vend_nothing, vend_fail) |\<in>| nondeterministic_pairs (merge_states 1 2 drinks2)"
  by (simp add: nondeterminisitic_pairs del: One_nat_def)

lemma nond_transitions_not_none: "nondeterministic_transitions (merge_states 1 2 drinks2) \<noteq> None"
  by (simp add: nondeterminisitic_pairs nondeterministic_transitions_def del: One_nat_def)

lemma nondeterministic_pairs_members: "x |\<in>| nondeterministic_pairs (merge_states 1 2 drinks2) \<Longrightarrow> x = (1, (1, 3), (vend_nothing, vend)) \<or> x = (1, (1, 1), vend_nothing, vend_fail)"
  by (simp add: nondeterminisitic_pairs del: One_nat_def)

lemma no_nondeterminism_0: "\<forall>aa b ab ba. nondeterministic_transitions (merge_states 1 2 drinks2) \<noteq> Some (0, (aa, b), ab, ba)"
  by (simp add: nondeterminisitic_pairs nondeterministic_transitions_def max_def del: One_nat_def)

lemma no_nondeterminism_2: "\<forall>aa b ab ba. (2, (aa, b), ab, ba) |\<notin>| nondeterministic_pairs (merge_states 1 2 drinks2)"
  by (simp add: nondeterminisitic_pairs del: One_nat_def)

lemma no_nondeterminism_2_2: "\<forall>aa b ab ba. nondeterministic_transitions (merge_states 1 2 drinks2) \<noteq> Some (2, (aa, b), ab, ba)"
  by (simp add: nondeterministic_transitions_def nondeterminisitic_pairs max_def del: One_nat_def)

lemma no_nondeterminism_3: "\<forall>aa b ab ba. (3, (aa, b), ab, ba) |\<notin>| nondeterministic_pairs (merge_states 1 2 drinks2)"
  by (simp add: nondeterminisitic_pairs del: One_nat_def)

lemma no_nondeterminism_3_2: "\<forall>aa b ab ba. nondeterministic_transitions (merge_states 1 2 drinks2) \<noteq> Some (3, (aa, b), ab, ba)"
  by (simp add: nondeterministic_transitions_def nondeterminisitic_pairs max_def del: One_nat_def)

lemma only_nondeterminism_1: "nondeterministic_transitions (merge_states 1 2 drinks2) = Some (a, (aa, b), aaa, ba) \<Longrightarrow> a = 1"
  by (simp add: nondeterministic_transitions_def nondeterminisitic_pairs max_def del: One_nat_def)

lemma no_transitions_to_0: "aa = 0 \<or> b = 0 \<Longrightarrow> (a, (aa, b), ab, ba) |\<notin>| nondeterministic_pairs (merge_states 1 2 drinks2)"
  apply (simp add: nondeterministic_transitions_def nondeterminisitic_pairs max_def del: One_nat_def)
  by auto

lemma no_transitions_to_0_2: "aa = 0 \<or> b = 0 \<Longrightarrow> nondeterministic_transitions (merge_states 1 2 drinks2) \<noteq> Some (a, (aa, b), ab, ba)"
  apply (simp add: nondeterministic_transitions_def nondeterminisitic_pairs max_def del: One_nat_def)
  by auto

lemma q1_nondeterminism_options: "(1, (1, 1), ab, ba) |\<in>| nondeterministic_pairs (merge_states 1 2 drinks2) \<Longrightarrow> ab = vend_fail \<and> ba = vend_nothing \<or> ab = vend_nothing \<and> ba = vend_fail"
  by (simp add: nondeterministic_transitions_def nondeterminisitic_pairs max_def del: One_nat_def)

lemma q1_nondeterminism_options_2: "nondeterministic_transitions (merge_states 1 2 drinks2) = Some (1, (1, 1), ab, ba) \<Longrightarrow> ab = vend_fail \<and> ba = vend_nothing \<or> ab = vend_nothing \<and> ba = vend_fail"
  by (simp add: nondeterministic_transitions_def nondeterminisitic_pairs max_def del: One_nat_def)

lemma medial_vend_nothing: "(medial c (Guard vend_nothing)) = c"
  by (simp add: transitions)

lemma medial_vend_fail: "medial select_posterior (Guard vend_fail) = \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> And (Eq (Num 0)) (Lt (Num 100))\<rbrakk>"
  apply (rule ext)
  by (simp add: transitions)

lemma vend_nothing_posterior: "posterior select_posterior vend_nothing = select_posterior"
  apply (simp only: posterior_def medial_vend_nothing)
  apply (simp add: consistent_select_posterior del: One_nat_def)
  apply (rule ext)
  apply (simp add: Let_def)
  by (simp add: transitions)

lemma consistent_medial_vend_fail: "consistent \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> And (cexp.Eq (Num 0)) (cexp.Lt (Num 100))\<rbrakk>"
  apply (simp add: consistent_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num 0>" in exI)
  by (simp add: connectives consistent_empty_4)

lemma vend_fail_posterior: "posterior select_posterior vend_fail = \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> And (Eq (Num 0)) (Lt (Num 100))\<rbrakk>"
  apply (simp only: posterior_def medial_vend_fail)
  apply (simp add: consistent_medial_vend_fail del: One_nat_def)
  apply (rule ext)
  by (simp add: transitions)

lemma vend_fail_subsumes_vend_nothing: "subsumes select_posterior vend_fail vend_nothing"
  apply (simp add: subsumes_def del: One_nat_def)
  apply safe
  using guard_vend_nothing medial_vend_fail apply auto[1]
    apply (simp add: transitions)
   apply (simp add: medial_vend_nothing del: One_nat_def)
   apply (simp add: vend_nothing_posterior del: One_nat_def)
   apply (simp only: vend_fail_posterior)
   apply (simp del: One_nat_def)
   apply (case_tac "r = V (R 2)")
    apply simp
    apply (case_tac "ValueLt (Some i) (Some (Num 100))")
     apply simp
    apply simp
   apply (case_tac "r = V (R 1)")
    apply simp
   apply simp
   apply (simp only: vend_fail_posterior)
  apply (simp add: consistent_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num 0>" in exI)
  by (simp add: connectives consistent_empty_4)

lemma posterior_select: "length (snd e) = 1 \<Longrightarrow> (posterior \<lbrakk>\<rbrakk> (snd (fthe_elem (possible_steps drinks2 0 Map.empty ''select'' (snd e))))) =
     (\<lambda>a. if a = V (R 2) then cexp.Eq (Num 0) else if a = V (R (1)) then cexp.Bc True else \<lbrakk>\<rbrakk> a)"
  by (simp add: posterior_def fthe_elem_def possible_steps_0 select_def Let_def  del: One_nat_def)

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
  apply (simp add: step_def drinks2_vend_insufficient fis_singleton_def updates_vend_nothing outputs_vend_nothing del: One_nat_def)
  apply safe
   apply (rule ext)
   apply simp
  by (simp only: register_simp)

lemma error_trace: "t \<noteq> [] \<Longrightarrow> observe_all drinks2 0 Map.empty t = [] \<Longrightarrow> observe_all drinks2 0 Map.empty (t @ [e]) = []"
  apply (cases t)
   apply simp
  apply (simp add: step_def)
  apply (case_tac "fis_singleton (possible_steps drinks2 0 Map.empty (fst a) (snd a))")
   apply simp
   apply (case_tac "fthe_elem (possible_steps drinks2 0 Map.empty (fst a) (snd a))")
   apply simp
  by simp

lemma reg_simp_3: "(\<lambda>a. if a = R 2 then Some (Num 0) else if a = R (1) then Some (hd (snd e)) else None) = <R (1) := hd (snd e), R 2 := Num 0>"
  apply (rule ext)
  by simp

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
     apply (simp add: step_def possible_steps_0 select_posterior del: One_nat_def)
     apply (simp add: updates_select del: One_nat_def)
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
  apply (simp add: possible_steps_def drinks2_def transitions del: One_nat_def)
  by auto

lemma drinks2_vend_insufficient2: "r (R 2) = Some (Num x1) \<Longrightarrow> ab = Num x1 \<Longrightarrow> x1 < 100 \<Longrightarrow>
                possible_steps drinks2 2 r (''vend'') [] = {|(2, vend_fail)|}"
  apply (simp add: possible_steps_def drinks2_def transitions del: One_nat_def)
  apply safe
    apply (simp del: One_nat_def)
    apply auto[1]
    apply (simp del: One_nat_def)
   apply auto[1]
  apply (simp del: One_nat_def)
  by force

lemma drinks2_vend_sufficient: "r (R 2) = Some (Num x1) \<Longrightarrow>
                \<not> x1 < 100 \<Longrightarrow>
                possible_steps drinks2 2 r (''vend'') [] = {|(3, vend)|}"
  apply (simp add: possible_steps_def drinks2_def transitions del: One_nat_def)
  by force

lemma none_outputs_vend:  "r (R 1) = None \<Longrightarrow> apply_outputs (Outputs vend) r = []"
  by (simp add: vend_def)

lemma "\<forall>r. \<not> gets_us_to 1 drinks2 2 r t"
proof (induct t)
  case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case
    apply clarify
    apply simp
    apply (case_tac "step drinks2 2 r (fst a) (snd a)")
     apply simp
    apply simp
    apply (case_tac aa)
    apply simp

    apply (case_tac "a = (''vend'', [])")
     apply simp
     apply (case_tac "r (R 2)")
    oops

lemma " gets_us_to 1 drinks2 1 <R (1) := hd (snd e), R 2 := Num 0> (xs @ [x]) \<Longrightarrow>
    \<not> gets_us_to 1 drinks2 1 <R (1) := hd (snd e), R 2 := Num 0> xs \<Longrightarrow> False"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    apply simp
    apply (case_tac "a=(''vend'', [])")
     apply simp
    oops



lemma "gets_us_to 1 drinks2 0 Map.empty (xs @ [x]) \<Longrightarrow>
    EFSM.valid drinks2 0 Map.empty (xs @ [x]) \<Longrightarrow>
     \<not> gets_us_to 1 drinks2 0 Map.empty xs \<Longrightarrow> xs = []"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons e xs)
  then show ?case
    apply simp
    apply (case_tac "fst e = ''select'' \<and> length (snd e) = 1 ")
     apply (simp add: possible_steps_0 updates_select)
    oops

lemma "gets_us_to 1 drinks2 0 Map.empty (xs @ [e]) \<Longrightarrow>
    gets_us_to 1 drinks2 0 Map.empty xs \<Longrightarrow>
    EFSM.valid drinks2 0 Map.empty xs \<Longrightarrow> e = (''vend'', [])"
proof (induct xs rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  then show ?case
    apply (case_tac "gets_us_to 1 drinks2 0 Map.empty (xs @ [e])")
     apply simp
     apply (case_tac "gets_us_to 1 drinks2 0 Map.empty xs")
      apply simp
      apply (case_tac "EFSM.valid drinks2 0 Map.empty xs")
       apply simp
      apply (simp add: prefix_closure)
    apply simp
    oops


lemma gets_us_to_1_anterior_context: "gets_us_to 1 drinks2 0 <> p \<Longrightarrow> anterior_context drinks2 p = \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> Eq (Num 0)\<rbrakk>"
proof (induct p rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc e xs)
  then show ?case
    apply simp
    apply (simp add: anterior_context_def)
    apply (case_tac "gets_us_to 1 drinks2 0 Map.empty xs")
     apply (case_tac "valid_trace drinks2 xs")
    apply simp
    oops

  

lemma "directly_subsumes drinks2 1 vend_fail vend_nothing"
  oops

lemma "choice vend_nothing vend"
  by (simp add: choice_symmetry choice_vend_vend_nothing)

lemma nondeterministic_transitions: "nondeterministic_transitions (merge_states 1 2 drinks2) = Some (1, (1, 3), vend_nothing, vend)"
  by (simp add: nondeterministic_transitions_def nondeterminisitic_pairs max_def del: One_nat_def)

lemma vend_doesnt_exit_1: "\<not>exits_state drinks2 vend 1"
  apply (simp add: exits_state_def drinks2_def transitions del: One_nat_def)
  by auto

lemma vend_nothing_exits_1: "exits_state drinks2 vend_nothing 1"
  apply (simp add: exits_state_def drinks2_def)
  by auto

lemma merge_1_3: "let t' = merge_states 1 2 drinks2
        in merge_states 1 3 t' = {|((0, 1), select),
                                   ((1,1), vend_nothing),
                                   ((1,1), coin),
                                   ((1,1), vend_fail),
                                   ((1,1), vend)|}"
  apply (simp add: merge_1_2 del: One_nat_def)
  by (simp add:  merge_states_def merge_states_aux_def del: One_nat_def)

lemma merge_1_3_2: "(merge_states 1 3 (merge_states 1 2 drinks2)) = {|((0, 1), select), 
                      ((1,1),vend_nothing),
((1,1), coin),
((1,1), vend_fail),
((1,1), vend)|}"
  using merge_1_3 by auto


lemma vend_fail_leq_vend: "vend_fail \<le> vend"
  by (simp add: less_eq_transition_ext_def less_transition_ext_def transitions less_gexp_def)

lemma max_nondeterministic_transitions: "max (1, (1, 1), vend_nothing, vend) (1, (1, 1), vend_nothing, vend_fail) = (1, (1, 1), vend_nothing, vend)"
  apply (simp add: max_def)
  by (simp add: antisym vend_fail_leq_vend)

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
  apply (simp add: merge_1_3_2 del: One_nat_def)
  apply safe
                      apply (simp_all del: One_nat_def)
                      apply auto[1]
                      apply auto[1]
                      apply auto[1]
                      apply auto[1]
                      apply auto[1]
                      apply (case_tac "a=1")
                      apply (case_tac "b=1")
                      apply (case_tac "ba=vend")
                      apply (case_tac "bb=1")
                      apply (case_tac "aa=0")
                      apply (simp add: vend_neq_vend_fail vend_neq_coin del: One_nat_def)
                      apply (case_tac "aa=1")
                      apply (simp add: vend_neq_vend_fail vend_neq_coin del: One_nat_def)
                      apply (case_tac "bc=vend_nothing")
                      apply (simp add: choice_vend_vend_nothing del: One_nat_def)
  using not_less_iff_gr_or_eq vend_nothing_lt_vend apply blast
                      apply (case_tac "bc=coin")
                      apply simp
  using no_choice_vend_coin apply blast
                      apply (case_tac "bc=vend_fail")
                      apply simp
  using no_choice_vend_vend_fail apply blast
                      apply simp
                      apply auto[1]
                      apply simp
                      apply simp
  using choice_def label_coin label_vend_fail label_vend_nothing no_choice_vend_coin no_choice_vend_vend_fail vend_nothing_lt_vend_fail apply fastforce
                      apply simp
                      apply auto[1]
                      apply auto[1]
                      apply auto[1]
                     apply auto[1]
                    apply auto[1]
                   apply auto[1]
                  apply (case_tac "a=1")
                   apply (case_tac "b=1")
                    apply (case_tac "ba=vend")
                     apply (simp del: One_nat_def)
  using no_choice_vend_coin no_choice_vend_vend_fail not_less_iff_gr_or_eq vend_nothing_lt_vend zero_neq_one apply blast
                    apply (case_tac "ba=vend_fail")
                     apply (simp del: One_nat_def)
  using Drinks_Machine.transitions(2) arity_vend_fail choice_def vend_nothing_lt_vend_fail zero_neq_one apply force
                     apply (simp del: One_nat_def)
  using Drinks_Machine.transitions(2) arity_vend_fail choice_def choice_vend_nothing_vend_fail apply fastforce
                   apply simp
                  apply auto[1]
                 apply auto[1]
                apply auto[1]
               apply auto[1]
              apply auto[1]
             apply auto[1]
            apply auto[1]
           apply (case_tac "b=1")
            apply (case_tac "bb=1")
             apply (case_tac "a=1")
              apply (case_tac "aa=1")
               apply (case_tac "ba=vend")
               apply (simp del: One_nat_def)
  using no_choice_vend_coin order.asym vend_nothing_lt_vend apply blast
               apply (case_tac "ba=vend_fail")
               apply (simp add: vend_fail_neq_vend_nothing del: One_nat_def)
  using Drinks_Machine.transitions(2) arity_vend_fail choice_def no_choice_vend_vend_fail vend_nothing_lt_vend_fail apply fastforce
               apply (case_tac "ba=coin")
  using choice_def label_coin label_vend_nothing no_choice_vend_coin apply auto[1]
               apply auto[1]
  apply simp
             apply auto[1]
            apply simp
           apply simp
          apply auto[1]
         apply auto[1]
        apply auto[1]
       apply auto[1]
      apply auto[1]
     apply auto[1]
    apply (case_tac "a=1")
     apply (case_tac "b=1")
      apply (case_tac "bb=1")
       apply (case_tac "aa=1")
        apply (case_tac "ba=vend")
        apply (simp del: One_nat_def)
  using no_choice_vend_coin not_less_iff_gr_or_eq vend_nothing_lt_vend apply blast
        apply (case_tac "ba=vend_fail")
        apply (simp del: One_nat_def)
  using Drinks_Machine.transitions(2) arity_vend_fail choice_def vend_nothing_lt_vend_fail apply fastforce
        apply (case_tac "ba=coin")
         apply (case_tac "bc=vend_nothing")
          apply (simp del: One_nat_def)
          apply (simp add: Drinks_Machine.transitions(2) Drinks_Machine_2.transitions(12) choice_def)
         apply auto[1]
        apply (case_tac "ba=vend_nothing")
        apply (simp del: One_nat_def)
  using choice_def label_coin label_vend_nothing apply auto[1]
        apply simp
       apply simp
      apply simp
     apply simp
    apply auto[1]
  apply (simp add: choice_vend_nothing_vend_fail vend_nothing_lt_vend_fail)
  by (simp add: choice_symmetry choice_vend_vend_nothing vend_nothing_lt_vend)

lemma ffilter_all_pairs_2: "ffilter (\<lambda>(((origin1, dest1), t1), (origin2, dest2), t2). origin1 = origin2 \<and> t1 < t2 \<and> choice t1 t2)
     (all_pairs (merge_states 1 3 (merge_states 1 2 drinks2))) = {|(((1, 1), vend_nothing), (1, 1), vend_fail), (((1, 1), vend_nothing), (1, 1), vend)|}"
  apply (simp add: all_pairs_def ffilter_def filter_all_pairs_2 del: One_nat_def)
  by (metis fset_inverse fset_simps(1) fset_simps(2))

lemma merge_states_2_nondeterminism: "nondeterministic_transitions (merge_states 1 3 (merge_states 1 2 drinks2)) = Some (1, (1, 1), vend_nothing, vend)"
  apply (simp add: nondeterministic_transitions_def nondeterministic_pairs_def del: One_nat_def)
  apply (simp add: ffilter_all_pairs_2 del: One_nat_def)
  by (metis max.commute max_nondeterministic_transitions)

lemma vend_exits_1: "exits_state (merge_states 1 2 drinks2) vend 1"
  apply (simp add: exits_state_def merge_1_2 del: One_nat_def)
  by auto

lemma vend_nothing_exits_1_2: "exits_state (merge_states 1 2 drinks2) vend_nothing 1"
  apply (simp add: exits_state_def merge_1_2 del: One_nat_def)
  by auto

lemma not_subset: "\<not>{(1, (1, 3), vend_nothing, vend), (1, (1, 1), vend_nothing, vend_fail)}
        \<subseteq> {Max {(1, (1, 3), vend_nothing, vend), (1, (1, 1), vend_nothing, vend_fail)}}"
  using vend_neq_vend_fail by auto

lemma not_subset_2: "\<not> {(1, (1, 1), vend_nothing, vend), (1, (1, 1), vend_nothing, vend_fail)}
     \<subseteq> {Max {(1, (1, 1), vend_nothing, vend), (1, (1, 1), vend_nothing, vend_fail)}}"
  using choice_def choice_vend_vend_nothing no_choice_vend_vend_fail by auto

lemma nondeterminism_merge_1_2: "nondeterminism (merge_states 1 2 drinks2)"
  by (simp add: nondeterminism_def vend_vend_nothing_nondeterminism del: One_nat_def)

lemma max_nondeterminism: "max (1::nat, (1::nat, 3::nat), vend_nothing, vend) (1, (1, 1), vend_nothing, vend_fail) = (1, (1, 3), vend_nothing, vend)"
  using nondeterminisitic_pairs nondeterministic_transitions nondeterministic_transitions_def by auto

lemma apply_guards_vend_nothing:  "\<forall>i r. apply_guards (Guard vend_nothing) (join_ir i r)"
  by (simp add: guard_vend_nothing)

lemma consistent_posterior_vend_nothing: "consistent c \<Longrightarrow> consistent (posterior c vend_nothing)"
  apply (simp add: posterior_def guard_vend_nothing updates_vend_nothing)
  apply (simp add: consistent_def)
  by auto

lemma consistent_posterior_vend_nothing_2: "\<not>consistent c \<Longrightarrow> \<not>consistent (posterior c vend_nothing)"
  apply (simp add: posterior_def guard_vend_nothing updates_vend_nothing)
  by (simp add: consistent_def)

lemma outputs_vend_neq_vend_nothing: "(\<exists>i r. [] \<noteq> apply_outputs (Outputs vend) (case_vname (\<lambda>n. input2state i (1) (I n)) (\<lambda>n. r (R n))))"
  apply (rule_tac x="[]" in exI)
  apply (rule_tac x="<R 1 := Str ''coke''>" in exI)
  by (simp add: vend_def)

lemma vend_doesnt_subsume_vend_nothing: "\<not> subsumes c vend vend_nothing"
  apply (simp add: subsumes_def apply_guards_vend_nothing)
  apply (simp add: guard_vend_nothing outputs_vend_nothing)
  using outputs_vend_neq_vend_nothing
  by simp

lemma vend_doesnt_directly_subsume_vend_nothing: "\<not>directly_subsumes drinks2 2 vend vend_nothing"
  apply (simp add: directly_subsumes_def vend_doesnt_subsume_vend_nothing)
  apply (simp add: gets_us_to_def)
  apply (rule_tac x="[(''select'', [Str ''coke'']), (''coin'', [Num 100])]" in exI)
  apply simp
  apply (simp add: possible_steps_0 step_def del: One_nat_def)
  by (simp add: possible_steps_1 del: One_nat_def)

lemma vend_doesnt_subsume_vend_nothing_2: "\<not> subsumes c vend_nothing vend"
proof-
  have outputs_vend_neq_vend_nothing_2: "(\<exists>i r. apply_guards (Guard vend) (case_vname (\<lambda>n. input2state i (1) (I n)) (\<lambda>n. r (R n))) \<and>
           apply_outputs (Outputs vend) (case_vname (\<lambda>n. input2state i (1) (I n)) (\<lambda>n. r (R n))) \<noteq> [])"
    apply (rule_tac x="[]" in exI)
    apply (rule_tac x="<R 1 := Str ''coke'', R 2 := Num 100>" in exI)
    by (simp add: transitions)
  show "\<not> subsumes c vend_nothing vend"
    apply (simp add: subsumes_def apply_guards_vend_nothing)
    apply (simp add: guard_vend_nothing outputs_vend_nothing)
    using outputs_vend_neq_vend_nothing_2
    by simp
qed

lemma vend_nothing_doesnt_directly_subsume_vend: "\<not>directly_subsumes drinks2 1 vend_nothing vend"
  apply (simp add: directly_subsumes_def vend_doesnt_subsume_vend_nothing_2 del: One_nat_def)
  apply (rule_tac x="[(''select'', [Str ''coke''])]" in exI)
  by (simp add: gets_us_to_def step_def possible_steps_0)

lemma nondeterminsm_merge_1_3: "nondeterminism (merge_states 1 3 (merge_states 1 2 drinks2))"
  apply (simp add: nondeterminism_def merge_1_3_2 nondeterministic_pairs_def del: One_nat_def)
  using ffilter_all_pairs_2 merge_1_3 by auto

lemma possible_steps_0_2: "(possible_steps (merge_states 1 2 drinks2) 0 Map.empty ''select'' [Str ''coke'']) = {|(1, select)|}"
proof
  have set_filter: "(Set.filter
       (\<lambda>((origin, dest), t).
           origin = 0 \<and>
           Label t = ''select'' \<and> Suc 0 = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state [Str ''coke''] 1 (I n)) Map.empty))
       {((0, 1), select), ((1, 1), vend_nothing), ((1, 1), coin), ((1, 1), vend_fail), ((1, 3), vend)}) =  {((0, 1), select)}"
    apply (simp del: One_nat_def)
    apply safe
       apply simp
      apply (simp del: One_nat_def)
    using arity_vend apply fastforce
      apply (simp add: transitions del: One_nat_def)
     apply auto[1]
    by (simp add: transitions del: One_nat_def)                                                                                   
  have abs_fset: "Abs_fset {((0, 1), select)} = {|((0, 1), select)|}"
    by (metis fset_inverse fset_simps(1) fset_simps(2))
  show "possible_steps (merge_states 1 2 drinks2) 0 Map.empty ''select'' [Str ''coke''] |\<subseteq>| {|(1, select)|}"                     
    by (simp add: merge_1_2 possible_steps_def ffilter_def set_filter abs_fset del: One_nat_def)
  show "{|(1, select)|} |\<subseteq>| possible_steps (merge_states 1 2 drinks2) 0 Map.empty ''select'' [Str ''coke'']"
    by (simp add: merge_1_2 possible_steps_def ffilter_def set_filter abs_fset del: One_nat_def)             
qed
                                                                                
lemma vend_doesnt_directly_subsume_vend_nothing_2: "\<not>directly_subsumes (merge_states 1 2 drinks2) 1 vend_nothing vend"
  apply (simp add: directly_subsumes_def vend_doesnt_subsume_vend_nothing_2 del: One_nat_def)
  apply (rule_tac x="[(''select'', [Str ''coke''])]" in exI)
  by (simp add: gets_us_to_def possible_steps_0_2 step_def del: One_nat_def)                                            
                                                                                                                            
lemma vend_nothing_doesnt_directly_subsume_vend_nothing_2: "\<not>directly_subsumes drinks2 1 vend_nothing vend"
  apply (simp add: directly_subsumes_def vend_doesnt_subsume_vend_nothing_2)
  apply (rule_tac x="[(''select'', [Str ''coke''])]" in exI)
  by (simp add: gets_us_to_def possible_steps_0 step_def)

lemma vend_doesnt_directly_subsume_vend_nothing_3: "\<not> directly_subsumes (merge_states 1 2 drinks2) 1 vend vend_nothing"
  using vend_nothing_doesnt_directly_subsume_vend vend_nothing_doesnt_directly_subsume_vend_nothing_2 by auto

lemma good_max: "Max ({(1, (1, 3), vend_nothing, vend), (1, (1, 1), vend_nothing, vend_fail)} -
               {max (1, (1, 3), vend_nothing, vend) (1, (1, 1), vend_nothing, vend_fail)}) = (1::nat, (1::nat, 1::nat), vend_nothing, vend_fail)"
  by (simp add: max_def)

lemma vend_fail_doesnt_exit_1: "\<not>exits_state drinks2 vend_fail 1"
proof-
  have set_filter: "(Set.filter (\<lambda>((from', to), t'). from' = 1 \<and> t' = vend_fail) (fset drinks2)) = {}"
    unfolding drinks2_def apply safe
    apply (simp del: One_nat_def)
    using coin_not_vend_fail vend_fail_neq_vend_nothing by auto
  show "\<not> exits_state drinks2 vend_fail 1"
    apply (simp add: exits_state_def ffilter_def set_filter del: One_nat_def)
    by (simp add: bot_fset_def)
qed

lemma posterior_vend_fail: "posterior r1_r2_true vend_fail = \<lbrakk>V (R 2) \<mapsto> cexp.Lt (Num 100), V (R 1) \<mapsto> cexp.Bc True\<rbrakk>"
proof-
  have medial_vend_fail: "medial r1_r2_true (Guard vend_fail) = \<lbrakk>V (R 2) \<mapsto> Lt (Num 100), V (R 1) \<mapsto> Bc True\<rbrakk>"
    apply (simp add: guard_vend_fail del: One_nat_def)
    apply (rule ext)
    by (simp add: transitions)
  have consistent_medial: "consistent \<lbrakk>V (R 2) \<mapsto> cexp.Lt (Num 100), V (R 1) \<mapsto> cexp.Bc True\<rbrakk>"
    unfolding consistent_def
    apply (rule_tac x="<R 2 := Num 0, R 1 := Str ''coke''>" in exI)
    apply (simp add: transitions)
    using consistent_empty_4 by auto
  show ?thesis
    unfolding posterior_def
    apply (simp add: medial_vend_fail Let_def consistent_medial del: One_nat_def)
    apply (rule ext)
    by (simp add: transitions del: One_nat_def)
qed

lemma posterior_vend_nothing: "posterior r1_r2_true vend_nothing = r1_r2_true"
  apply (rule ext)
  unfolding posterior_def
  by (simp add: guard_vend_nothing Let_def consistent_r1_r2_true updates_vend_nothing del: One_nat_def)

lemma vend_nothing_doesnt_directly_subsume_vend_2: "\<not>directly_subsumes drinks2 2 vend_fail vend_nothing"
proof-
  show "\<not> directly_subsumes drinks2 2 vend_fail vend_nothing"
    apply (simp add: directly_subsumes_def)
    apply (rule_tac x="[(''select'', [Str ''coke'']), (''coin'', [Num n])]" in exI)
  proof
    have consistent_lt_100: "consistent \<lbrakk>V (R 2) \<mapsto> cexp.Lt (Num 100), V (R 1) \<mapsto> cexp.Bc True\<rbrakk>"
      unfolding consistent_def
      apply (rule_tac x="<R 2 := Num 0, R 1 := Str ''coke''>" in exI)
      apply simp
      using consistent_empty_4 by blast
    have contra: "\<not>(\<exists>i. cval (\<lbrakk>\<rbrakk> r) i = Some True \<and> cval (\<lbrakk>\<rbrakk> r) i \<noteq> Some True)"
      by simp
    show "gets_us_to 2 drinks2 0 Map.empty [(''select'', [Str ''coke'']), (''coin'', [Num n])]"
      by (simp add: gets_us_to_def possible_steps_0 possible_steps_1 step_def del: One_nat_def)
    show "\<not> subsumes (anterior_context drinks2 [(''select'', [Str ''coke'']), (''coin'', [Num n])]) vend_fail vend_nothing"
      apply (simp add: anterior_context_def step_def possible_steps_0 del: One_nat_def)
      apply (simp add: subsumes_def guard_vend_nothing guard_vend_fail del: One_nat_def)
      apply (simp add: possible_steps_1 del: One_nat_def)
      apply (simp add: outputs_vend_nothing outputs_vend_fail)
      apply (simp only: select_posterior posterior_coin_first)
      apply (simp add: posterior_vend_fail del: One_nat_def)
      apply (simp add: connectives relations posterior_vend_nothing consistent_r1_r2_true del: One_nat_def)
      apply (simp add: consistent_lt_100 del: One_nat_def)
      apply clarify
      apply (simp add: contra del: One_nat_def)
      apply (rule_tac x="V (R 2)" in exI)
      apply simp
      apply (rule_tac x="Num 100" in exI)
      by simp
  qed
qed

lemma vend_nothing_directly_subsumes_vend_fail: "directly_subsumes drinks2 1 vend_nothing vend_fail"
proof-
  have "subsumes c vend_nothing vend_fail"
    unfolding subsumes_def
    apply safe
  proof-
    show "\<And>r i. cval (medial c (Guard vend_fail) r) i = Some True \<Longrightarrow> cval (medial c (Guard vend_nothing) r) i = Some True"
      apply (simp add: guard_vend_fail guard_vend_nothing)
      apply (case_tac "cval (c r) i")
       apply simp
      apply simp
      apply (case_tac "cval (pairs2context (guard2pairs c (GExp.Lt (V (R 2)) (L (Num 100)))) r) i")
       apply simp
      by simp
    show "\<And>i r. apply_guards (Guard vend_fail) (join_ir i r) \<Longrightarrow>
           apply_outputs (Outputs vend_fail) (join_ir i r) = apply_outputs (Outputs vend_nothing) (join_ir i r)"
      by (simp add: transitions)
    show "\<And>r i. cval (posterior (medial c (Guard vend_fail)) vend_nothing r) i = Some True \<Longrightarrow>
           posterior c vend_fail r \<noteq> Undef \<Longrightarrow> cval (posterior c vend_fail r) i = Some True"
      apply (simp add: guard_vend_fail)
      apply (simp add: posterior_def guard_vend_nothing Let_def)
      apply (case_tac "consistent (\<lambda>r. and (c r) (pairs2context (guard2pairs c (GExp.Lt (V (R 2)) (L (Num 100)))) r))")
       apply (simp add: vend_nothing_def vend_fail_def del: One_nat_def)
       apply safe
          apply (simp del: One_nat_def)
         apply simp
        apply (simp del: One_nat_def)
        apply (case_tac "cval (c r) i")
         apply simp
        apply (simp del: One_nat_def)
        apply (simp add: Drinks_Machine_2.transitions(8))
       apply simp
      by simp
    have posterior_c_vend_nothing: "consistent c \<Longrightarrow> posterior c vend_nothing = c"
      apply (rule ext)
      by (simp add: posterior_def vend_nothing_def)
    have inconsistent_c_posterior_vend_nothing: "\<not> consistent c \<Longrightarrow> \<not> consistent (posterior c vend_nothing)"
      unfolding posterior_def
      apply (simp add: vend_nothing_def)
      by (simp add: consistent_def)
    have "\<not> consistent c \<Longrightarrow> \<not> consistent (\<lambda>r. and (c r) (if r = V (R 2) then snd (V (R 2), cexp.Lt (Num 100)) else cexp.Bc True))"
      unfolding consistent_def
      apply simp
      apply (rule allI)
      apply (rule_tac x="V (R 2)" in exI)
      apply simp
      apply safe

    show "consistent (posterior c vend_fail) \<Longrightarrow> consistent (posterior c vend_nothing)"
      apply (case_tac "consistent c")
      apply (simp add: posterior_c_vend_nothing)
      apply (simp add: inconsistent_c_posterior_vend_nothing)
      apply (simp add: posterior_def guard_vend_fail Let_def)
      apply (case_tac "consistent (\<lambda>r. and (c r) (pairs2context (guard2pairs c (GExp.Lt (V (R 2)) (L (Num 100)))) r))")
       apply (simp add: vend_fail_def relations del: One_nat_def)
      
      sorry
  qed
  show ?thesis
    unfolding directly_subsumes_def
    apply clarify
    

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

lemma vend_nothing_vend_max: "(1, (1, 3), vend_nothing, vend) = max (1, (1, 3), vend_nothing, vend) (1, (1, 1), vend_nothing, vend_fail)"
  by (simp add: max_nondeterminism)

value "merge_states 1 3 (merge_states 1 2 drinks2)"

lemma "merge_states 1 3 (merge_states 1 2 drinks2) = (\<lambda> (a,b) .
  if (a, b) = (0, 1) then {|select|} else
  if (a, b) = (1,1) then {|vend_fail, coin|} else
  if (a, b) = (1, 3) then {|vend|} else {||})"


lemma "merge_2 drinks2 1 2 = Some (\<lambda> (a,b) .
  if (a, b) = (0, 1) then {|select|} else
  if (a, b) = (1,1) then {|vend_fail, coin|} else
  if (a, b) = (1, 3) then {|vend|} else {||})"
  apply simp
  apply (case_tac "nondeterministic_transitions (merge_states 1 2 drinks2)")
   apply (simp add: nondeterministic_transitions)
  apply (simp add: nondeterministic_transitions)
  apply (simp only: Let_def)
  apply clarify
  apply (simp add: nondeterminism_merge_1_2 nondeterminisitic_pairs del: resolve_nondeterminism.simps)
  apply (simp add: vend_nothing_exits_1)
  apply (simp add: vend_doesnt_exit_1)
  apply safe
   apply simp
  apply (case_tac "max (1, (1, 3), vend_nothing, vend) (1, (1, 1), vend_nothing, vend_fail) = (1, (1, 3), vend_nothing, vend)")
   defer
  using vend_nothing_vend_max apply simp
  apply simp
  apply (simp add: vend_nothing_exits_1 vend_doesnt_exit_1)



  (* apply simp *)
  (* apply clarify *)
  (* apply (simp only: nondeterminisitic_pairs not_subset) *)
  (* apply simp *)
  (* apply (simp add: nondeterminism_merge_1_2) *)
  (* apply (simp only: max_nondeterminism) *)
  (* apply simp *)
  (* apply (simp add: vend_doesnt_exit_1 vend_nothing_exits_1) *)
  (* apply (simp add: nondeterminsm_merge_1_3 nondet_pairs_simpler) *)
  (* apply (simp add: max_nondeterministic_transitions) *)
  (* apply (simp add: vend_exits_1 vend_nothing_exits_1_2) *)
  (* apply (simp add: merge_transitions.simps) *)
  (* apply (simp add: subset_nondet) *)
  (* apply (simp add: vend_doesnt_directly_subsume_vend_nothing_2) *)
  (* apply (simp add: vend_doesnt_directly_subsume_vend_nothing) *)
  (* apply (simp add: vend_nothing_doesnt_directly_subsume_vend_nothing_2) *)
  (* apply (simp add: vend_doesnt_directly_subsume_vend_nothing_3) *)
  (* apply (simp add: good_max) *)

  (* apply (simp add: vend_nothing_directly_subsumes_vend_fail) *)
  (* apply (simp add: replace_transition_def merge_1_2) *)
  (* apply (simp add: vend_nothing_exits_1) *)

  (* apply (rule ext) *)
  (* apply (simp add: finsert_vend_nothing) *)
  

end