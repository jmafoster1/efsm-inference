theory DM_Inference
imports Inference SelectionStrategies "../examples/Drinks_Machine_2"
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

lemma vend_neq_coin: "vend \<noteq> coin"
  by (simp add: transitions)

lemma vend_nothing_lt_vend: "vend_nothing < vend"
  by (simp add: less_transition_ext_def transitions)

lemma no_choice_vend_coin: "\<not> choice vend coin"
  by (simp add: choice_def transitions)

lemma coin_neq_vend_fail: "coin \<noteq> vend_fail"
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

lemma vend_not_lt_vend_nothing: "\<not>vend < vend_nothing"
  by (simp add: not_less_iff_gr_or_eq vend_nothing_lt_vend)

lemma vend_neq_vend_nothing: "vend \<noteq> vend_nothing"
  by (simp add: transitions)

lemma coin_neq_vend: "coin \<noteq> vend"
  by (simp add: transitions)

lemma vend_fail_neq_vend: "vend_fail \<noteq> vend"
  by (simp add: transitions)

lemma vend_neq_vend_fail: "vend \<noteq> vend_fail"
  by (simp add: transitions)

lemma vend_not_lt_vend_fail: "\<not>vend < vend_fail"
  by (simp add: less_transition_ext_def transitions less_gexp_def)

lemma vend_fail_neq_coin: "vend_fail \<noteq> coin"
  by (simp add: transitions)

lemma vend_fail_neq_vend_nothing: "vend_fail \<noteq> vend_nothing"
  by (simp add: transitions)

lemma vend_fail_not_lt_vend_nothing: "\<not>vend_fail < vend_nothing"
  by (simp add: transitions less_transition_ext_def)

lemma vend_fail_not_lt_coin:"\<not>vend_fail < coin"
  by (simp add: transitions less_transition_ext_def)

lemma coin_neq_vend_nothing: "coin \<noteq> vend_nothing"
  by (simp add: transitions)

lemma vend_nothing_neq_vend_fail: "vend_nothing \<noteq> vend_fail"
  by (simp add: transitions)

lemma vend_nothing_neq_coin: "vend_nothing \<noteq> coin"
  by (simp add: transitions)

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

lemma posterior_select: "length (snd e) = 1 \<Longrightarrow> (posterior \<lbrakk>\<rbrakk> (snd (fthe_elem (possible_steps Drinks_Machine_2.drinks2 0 Map.empty ''select'' (snd e))))) =
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

lemma observe_vend_nothing: "a = (''vend'', []) \<Longrightarrow> (observe_all Drinks_Machine_2.drinks2 1 <R (1) := hd (snd e), R 2 := Num 0> (a # t)) = (vend_nothing, 1, [], <R (1) := hd (snd e), R 2 := Num 0>)#(observe_all Drinks_Machine_2.drinks2 1 <R (1) := hd (snd e), R 2 := Num 0> t)"
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

lemma equal_first_event: "observe_all Drinks_Machine_2.drinks2 0 Map.empty t = x # list \<Longrightarrow>
       observe_all Drinks_Machine_2.drinks2 0 Map.empty (t @ [e]) = y # lista \<Longrightarrow> x = y"
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

lemma drinks2_singleton_0: "fis_singleton (possible_steps Drinks_Machine_2.drinks2 0 Map.empty (fst e) (snd e)) \<Longrightarrow> fst e = ''select'' \<and> length (snd e) = 1"
  apply (case_tac "fst e = ''select'' \<and> length (snd e) = 1 ")
   apply simp
  by (simp add: drinks2_0_invalid)

lemma drinks2_observe_all_fst_select: "observe_all Drinks_Machine_2.drinks2 0 Map.empty (t @ [e]) = [(aaa, 1, c, d)] \<Longrightarrow> aaa = select"
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

lemma drinks2_singleton_0_select: "fis_singleton (possible_steps Drinks_Machine_2.drinks2 0 Map.empty (fst e) (snd e)) \<Longrightarrow>
       fthe_elem (possible_steps Drinks_Machine_2.drinks2 0 Map.empty (fst e) (snd e)) = (1, aa) \<Longrightarrow> aa = select"
  using Drinks_Machine_2.possible_steps_0 drinks2_singleton_0 by auto

lemma coin_updates_2: "(EFSM.apply_updates (Updates coin)
       (case_vname (\<lambda>n. input2state (snd a) (1) (I n)) (\<lambda>n. if n = 2 then Some (Num 0) else if R n = R (1) then Some s else None))
       (\<lambda>a. if a = R 2 then Some (Num 0) else if a = R (1) then Some (hd (snd e)) else None)) =
       (\<lambda>u. if u = R 1 then Some s else if u = R 2 then value_plus (Some (Num 0)) (input2state (snd a) 1 (I 1)) else None)"
  apply (rule ext)
  by (simp add: coin_def)

lemma drinks2_vend_insufficient2: "r (R 2) = Some (Num x1) \<Longrightarrow> ab = Num x1 \<Longrightarrow> x1 < 100 \<Longrightarrow>
                possible_steps Drinks_Machine_2.drinks2 2 r (''vend'') [] = {|(2, vend_fail)|}"
  apply (simp add: possible_steps_def Drinks_Machine_2.drinks2_def transitions )
  apply safe
    apply (simp)
    apply auto[1]
    apply (simp )
   apply auto[1]
  apply (simp )
  by force

lemma drinks2_vend_sufficient: "r (R 2) = Some (Num x1) \<Longrightarrow>
                \<not> x1 < 100 \<Longrightarrow>
                possible_steps Drinks_Machine_2.drinks2 2 r (''vend'') [] = {|(3, vend)|}"
  apply (simp add: possible_steps_def Drinks_Machine_2.drinks2_def transitions )
  by force

lemma none_outputs_vend:  "r (R 1) = None \<Longrightarrow> apply_outputs (Outputs vend) r = [None]"
  by (simp add: vend_def)

lemma vend_doesnt_exit_1[simp]: "\<not>exits_state drinks2 vend 1"
  by (simp add: exits_state_def drinks2_def transitions )

lemma vend_nothing_exits_1[simp]: "exits_state drinks2 vend_nothing 1"
  apply (simp add: exits_state_def drinks2_def)
  by auto

lemma vend_fail_leq_vend: "vend_fail \<le> vend"
  by (simp add: less_eq_transition_ext_def less_transition_ext_def transitions less_gexp_def)

lemma vend_nothing_neq_vend: "vend_nothing \<noteq> vend"
  by (simp add: transitions)

lemma not_subset: "\<not>{(1, (1, 3), vend_nothing, vend), (1, (1, 1), vend_nothing, vend_fail)}
        \<subseteq> {Max {(1, (1, 3), vend_nothing, vend), (1, (1, 1), vend_nothing, vend_fail)}}"
  using vend_neq_vend_fail by auto

lemma not_subset_2: "\<not> {(1, (1, 1), vend_nothing, vend), (1, (1, 1), vend_nothing, vend_fail)}
     \<subseteq> {Max {(1, (1, 1), vend_nothing, vend), (1, (1, 1), vend_nothing, vend_fail)}}"
  using choice_def choice_vend_vend_nothing no_choice_vend_vend_fail by auto

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

lemma good_max: "Max ({(1, (1, 3), vend_nothing, vend), (1, (1, 1), vend_nothing, vend_fail)} -
               {max (1, (1, 3), vend_nothing, vend) (1, (1, 1), vend_nothing, vend_fail)}) = (1::nat, (1::nat, 1::nat), vend_nothing, vend_fail)"
  by (simp add: max_def)

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

definition basically_drinks :: iEFSM where
  "basically_drinks = {|(2, (1, 1), coin), (1, (1, 1), vend_fail), (0, (0, 1), select), (5, (1, 3), vend)|}"

lemma select_updates: "length b = 1 \<Longrightarrow> (EFSM.apply_updates (Updates select) (case_vname (\<lambda>n. input2state b 1 (I n)) Map.empty) Map.empty) = <R 1 := hd b, R 2 := Num 0>"
  apply (rule ext)
  by (simp add: select_def hd_input2state)

lemma update_simp: "(\<lambda>x. if x = R 1
            then aval (snd (R 1, V (R 1))) (case_vname Map.empty (\<lambda>n. if n = 2 then Some (Num 0) else if R n = R 1 then Some d else None))
            else EFSM.apply_updates [(R 2, V (R 2))]
                  (case_vname Map.empty (\<lambda>n. if n = 2 then Some (Num 0) else if R n = R 1 then Some d else None))
                  (\<lambda>a. if a = R 2 then Some (Num 0) else if a = R 1 then Some d else None) x) = <R 1 := d, R 2 := Num 0>"
  apply (rule ext)
  by simp

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

lemma no_subsumption_vend_vend_nothing: "\<not>subsumes c vend vend_nothing"
  by (simp add: subsumes_def transitions)

lemma scoring: "rev (sorted_list_of_fset (score drinks2 naive_score)) = [(3, 1, 2), (0, 2, 3), (0, 1, 3), (0, 0, 3), (0, 0, 2), (0, 0, 1)]"
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
  have score: "score DM_Inference.drinks2 naive_score = {|(0, 0, 1), (0, 0, 2), (0, 0, 3), (0, 1, 3), (0, 2, 3), (3, 1, 2)|}"
    apply (simp add: score_def ffilter)
    apply (simp add: outgoing_transitions_def drinks2_def fimage_def)
    apply (simp add: naive_score_empty set_equiv)
    apply (simp add: naive_score_def fprod_def)
    apply (simp add: transitions Abs_fset_inverse)
    by auto
  show ?thesis
    by (simp add: score sorted_list_of_fset_def)
qed

lemma nondeterministic_pairs_merged_1_2: "nondeterministic_pairs merged_1_2 = {|
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
    (1, (1, 3), (vend_fail, 4),vend, 5),
    (1, (1, 1), (vend_fail, 4),coin, 3),
    (1, (1, 1), (vend_fail, 4),coin, 2),
    (1, (1, 1), (vend_fail, 4),vend_nothing, 1),
    (1, (1, 3),(coin, 3),vend, 5),
    (1, (1, 1),(coin, 3),vend_fail, 4),
    (1, (1, 1),(coin, 3),coin, 2),
    (1, (1, 1),(coin, 3),vend_nothing, 1),
    (1, (1, 3),(coin, 3),vend, 5),
    (1, (1, 3),(coin, 2),vend, 5),
    (1, (1, 1),(coin, 2),vend_fail, 4),
    (1, (1, 1),(coin, 2),coin, 3),
    (1, (1, 1),(coin, 2),vend_nothing, 1),
    (1, (1, 3), (vend_nothing, 1),vend, 5),
    (1, (1, 1), (vend_nothing, 1),vend_fail, 4),
    (1, (1, 1), (vend_nothing, 1),coin, 3),
    (1, (1, 1), (vend_nothing, 1),coin, 2)
  |}"
    apply (simp add: state_nondeterminism_def fimage_def fset_both_sides Abs_fset_inverse)
    apply (simp add: minus_1 minus_2 minus_3 minus_4)
    by auto
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_1_2_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_1)
    apply (simp add: ffilter_def Set.filter_def fset_both_sides Abs_fset_inverse)
    apply safe
    by (simp_all add: choices vend_fail_not_lt_vend_nothing vend_nothing_lt_vend vend_nothing_lt_vend_fail)
qed

definition merged_1_3 :: iEFSM where
  "merged_1_3 = {|(0, (0, 1), select),
        (1, (1, 1), vend_nothing),
        (2, (1, 1), coin),
        (3, (1, 1), coin), 
        (4, (1, 1), vend_fail),
        (5, (1, 1), vend)|}"

lemma merge_states_1_3: "merge_states 1 3 merged_1_2 = merged_1_3"
  by (simp add: merge_states_def merge_states_aux_def merged_1_2_def merged_1_3_def)

lemma nondeterministic_pairs_merged_1_3: "nondeterministic_pairs merged_1_3 = {|
  (1, (1, 1),(coin,2),coin,3),
  (1, (1, 1), (vend_nothing, 1),vend, 5),
  (1, (1, 1), (vend_nothing, 1),vend_fail, 4)
|}"
proof-
  have minus_1: "{(1, vend_nothing, 1), (1, coin, 2), (1, coin, 3), (1, vend_fail, 4), (1, vend, 5)} - {(1, vend, 5)} = {(1, vend_nothing, 1), (1, coin, 2), (1, coin, 3), (1, vend_fail, 4)}"
    apply (simp add: transitions)
    by auto
  have minus_2: "{(1, vend_nothing, 1), (1, coin, 2), (1, coin, 3), (1, vend_fail, 4), (1, vend, 5)} - {(1, vend_fail, 4)} = {(1, vend_nothing, 1), (1, coin, 2), (1, coin, 3), (1, vend, 5)}"
    apply (simp add: transitions)
    by auto
  have minus_3: "{(1, vend_nothing, 1::nat), (1, coin, 2), (1, coin, 3), (1, vend_fail, 4), (1, vend, 5)} - {(1, coin, 3)} = {(1, vend_nothing, 1), (1, coin, 2), (1, vend_fail, 4), (1, vend, 5)}"
    apply (simp add: transitions)
    by auto
  have minus_4: "{(1, vend_nothing, 1::nat), (1, coin, 2), (1, coin, 3), (1, vend_fail, 4), (1, vend, 5)} -
                                     {(1, coin, 2)} = {(1, vend_nothing, 1), (1, coin, 3), (1, vend_fail, 4), (1, vend, 5)}"
    apply (simp add: transitions)
    by auto
  have state_nondeterminism_1: "state_nondeterminism 1 {|(1, vend_nothing, 1), (1, coin, 2), (1, coin, 3), (1, vend_fail, 4), (1, vend, 5)|} = {|
      (1, (1, 1), (vend, 5), vend_fail, 4),
      (1, (1, 1), (vend, 5), coin, 3),
      (1, (1, 1), (vend, 5), coin, 2),
      (1, (1, 1), (vend, 5), vend_nothing, 1),
      (1, (1, 1), (vend_fail, 4), vend, 5),
      (1, (1, 1), (vend_fail, 4), coin, 3),
      (1, (1, 1), (vend_fail, 4), coin, 2),
      (1, (1, 1), (vend_fail, 4), vend_nothing, 1),
      (1, (1, 1),(coin, 3), vend, 5),
      (1, (1, 1),(coin, 3), vend_fail, 4),
      (1, (1, 1),(coin, 3), coin, 2),
      (1, (1, 1),(coin, 3), vend_nothing, 1),
      (1, (1, 1),(coin, 2), vend, 5),
      (1, (1, 1),(coin, 2), vend_fail, 4),
      (1, (1, 1),(coin, 2), coin, 3),
      (1, (1, 1),(coin, 2), vend_nothing, 1),
      (1, (1, 1), (vend_nothing, 1), vend, 5),
      (1, (1, 1), (vend_nothing, 1), vend_fail, 4),
      (1, (1, 1), (vend_nothing, 1), coin, 3),
      (1, (1, 1), (vend_nothing, 1), coin, 2)
    |}"
    apply (simp add: state_nondeterminism_def fimage_def fset_both_sides Abs_fset_inverse)
    apply (simp add: minus_1 minus_2 minus_3 minus_4)
    by auto
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_1_3_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_1)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply safe
    by (simp_all add: choices vend_not_lt_vend_nothing vend_fail_not_lt_vend_nothing vend_nothing_lt_vend vend_nothing_lt_vend_fail)
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

lemma merge_vend_nothing_vend: "merge_transitions DM_Inference.drinks2 merged_1_2 1 2 1 1 3 vend_nothing 1 vend 5 null_generator null_modifier True = None"
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

lemma nondeterministic_pairs_two_coins: "nondeterministic_pairs two_coins = {|(1, (1, 1), (coin, 2), (coin, 3))|}"
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
    (1, (1, 3),(coin, 3),vend, 5),
    (1, (1, 1),(coin, 3),coin, 2),
    (1, (1, 1),(coin, 3),vend_fail, 1),
    (1, (1, 3),(coin, 2),vend, 5),
    (1, (1, 1),(coin, 2),coin, 3),
    (1, (1, 1),(coin, 2),vend_fail, 1),
    (1, (1, 3), (vend_fail, 1),vend, 5),
    (1, (1, 1), (vend_fail, 1),coin, 3),
    (1, (1, 1), (vend_fail, 1),coin, 2)
  |}"
    apply (simp add: state_nondeterminism_def fimage_def)
    apply (simp add: minus_1 minus_2 minus_4)
    apply (simp add: fset_both_sides Abs_fset_inverse)
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
  have state_nondetermininism: "state_nondeterminism 1 {|(1, coin, 2), (1, vend_fail, 1), (3, vend, 5)|} = {|
    (1, (1, 3), (vend_fail, 1),vend, 5),
    (1, (1, 3),(coin, 2),vend, 5),
    (1, (1, 1), (vend_fail, 1),coin, 2),
    (1, (1, 3),(coin, 2),vend, 5),
    (1, (1, 1),(coin, 2),vend_fail, 1)
  |}"
    apply (simp add: state_nondeterminism_def fimage_def)
    apply (simp add: minus_1 minus_2)
    by auto
  show ?thesis
    apply (simp add: nondeterministic_pairs_def fimage_def S_def basically_drinks_def outgoing_transitions_def state_nondetermininism)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply clarify
    apply simp
    apply (case_tac "a = 1 \<and> aa = 1")
    defer
     apply simp
    apply simp
    using choice_symmetry no_choice_coin_vend no_choice_vend_fail_coin no_choice_vend_vend_fail by blast
qed

lemma score_2: "sorted_list_of_fset (score basically_drinks naive_score) = [(0, 0, 1), (0, 0, 3), (0, 1, 3)]"
proof-
  have ffilter: "ffilter (\<lambda>(x, y). x < y) (Inference.S basically_drinks |\<times>| Inference.S basically_drinks) =
    {|(0, 1), (0, 3), (1, 3)|}"
    apply (simp add: S_def basically_drinks_def)
    apply (simp add: fprod_def ffilter_def Abs_fset_inverse fset_both_sides)
    apply (simp add: Set.filter_def)
    by auto
  have score: "score basically_drinks naive_score = {|(0, 0, 1), (0, 0, 3), (0, 1, 3)|}"
    apply (simp add: score_def ffilter)
    apply (simp add: outgoing_transitions_def basically_drinks_def fimage_def)
    apply (simp add: naive_score_empty set_equiv)
    apply (simp add: naive_score_def fprod_def)
    by (simp add: transitions Abs_fset_inverse)
  show ?thesis
    by (simp add: score sorted_list_of_fset_def)
qed

lemma "infer drinks2 naive_score null_generator null_modifier = basically_drinks"
proof-
  have leaves_1_merged_1_2: "leaves 1 merged_1_2 = 1"
  proof-
    have set_filter: "Set.filter (\<lambda>x. \<exists>a b ba. x = (1, (a, b), ba)) (fset merged_1_2) = {(1, (1, 1), vend_nothing)}"
      apply (simp add: Set.filter_def merged_1_2_def)
      by auto
    show ?thesis
      by (simp add: leaves_def ffilter_def fthe_elem_def Abs_fset_inverse set_filter)
  qed
  have leaves_5_merged_1_2: "leaves 5 merged_1_2 = 1"
  proof-
    have set_filter: "Set.filter (\<lambda>x. \<exists>a b ba. x = (5, (a, b), ba)) (fset merged_1_2) = {(5, (1, 3), vend)}"
      apply (simp add: Set.filter_def merged_1_2_def)
      by auto
    show ?thesis
      by (simp add: leaves_def ffilter_def fthe_elem_def Abs_fset_inverse set_filter)
  qed
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
  have next_nondet: "{|(1, (1, 1), (coin, 2), coin, 3), (1, (1, 3), (vend_nothing, 1), vend, 5), (1, (1, 1), (vend_nothing, 1), vend_fail, 4)|} |-|
                      {|(1, (1, 3), (vend_nothing, 1), vend, 5)|} = {|(1, (1, 1), (coin, 2), coin, 3), (1, (1, 1), (vend_nothing, 1), vend_fail, 4)|}"
    apply (simp add: transitions)
    by auto
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
  show ?thesis
    apply (simp add: scoring merge_def)
    apply (simp add: merge_states_1_2 nondeterminism_def nondeterministic_pairs_merged_1_2 max_def)
    apply (simp add: leaves_1_drinks2 leaves_5_drinks2 merge_vend_nothing_vend)
    apply (simp add: nondeterminism_def nondeterministic_pairs_merged_1_2 max_def minus_1 coin_lt_vend_nothing)
    apply (simp add: leaves_1_drinks2 leaves_4_drinks2 merge_vend_nothing_vend_fail)
    apply (simp add: nondeterminism_def nondeterministic_pairs_two_coins max_def coin_lt_vend_fail)
    apply (simp add: leaves_2_drinks2 leaves_3_drinks2 merge_coin_coin)
    apply (simp add: nondeterminism_def nondetermnistic_pairs_basically_drinks)
    by (simp add: score_2)
qed
end