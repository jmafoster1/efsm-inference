subsection{*An Observationally Equivalent Model*}
text{*This theory defines a second formalisation of the drinks machine example which produces
identical output to the first model. This property is called \emph{observational equivalence} and is
discussed in more detail in \cite{foster2018}.*}
theory Drinks_Machine_2
  imports Drinks_Machine "../Contexts"
begin

definition vend_nothing :: "transition" where
"vend_nothing \<equiv> \<lparr>
        Label = (STR ''vend''),
        Arity = 0,
        Guard = [],
        Outputs =  [],
        Updates = [(1, V (R 1)), (2, V (R 2))]
      \<rparr>"

lemma guard_vend_nothing: "Guard vend_nothing = []"
  by (simp add: vend_nothing_def)

lemma updates_vend_nothing: "Updates vend_nothing = [(1, V (R 1)), (2, V (R 2))]"
  by (simp add: vend_nothing_def)

lemmas transitions = Drinks_Machine.transitions vend_nothing_def

lemma outputs_vend_nothing: "Outputs vend_nothing = []"
  by (simp add: vend_nothing_def)

lemma label_vend_nothing: "Label vend_nothing = (STR ''vend'')"
  by (simp add: vend_nothing_def)

definition drinks2 :: transition_matrix where
"drinks2 = {|
              ((0,1), select),
              ((1,1), vend_nothing),
              ((1,2), coin),
              ((2,2), coin),
              ((2,2), vend_fail),
              ((2,3), vend)
         |}"

lemma empty_not_singleton [simp]: "\<not> is_singleton {}"
  by (simp add: is_singleton_def)

lemma possible_steps_0:  "length i = 1 \<Longrightarrow> possible_steps drinks2 0 r ((STR ''select'')) i = {|(1, select)|}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma possible_steps_1: "length i = 1 \<Longrightarrow> possible_steps drinks2 1 r ((STR ''coin'')) i = {|(2, coin)|}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma possible_steps_2_coin: "length i = 1 \<Longrightarrow> possible_steps drinks2 2 r ((STR ''coin'')) i = {|(2, coin)|}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma possible_steps_2_vend: "r $ 2 = Some (Num n) \<Longrightarrow> n \<ge> 100 \<Longrightarrow> possible_steps drinks2 2 r ((STR ''vend'')) [] = {|(3, vend)|}"
  apply (simp add: possible_steps_singleton drinks2_def)
  apply safe
  by (simp_all add: transitions apply_guards_def ValueGt_def join_ir_def)

lemma purchase_coke: "observe_trace drinks2 0 <> [((STR ''select''), [Str ''coke'']), ((STR ''coin''), [Num 50]), ((STR ''coin''), [Num 50]), ((STR ''vend''), [])] =
                       [[], [Some (Num 50)], [Some (Num 100)], [Some (Str ''coke'')]]"
  apply (rule observe_trace_possible_step)
     apply (simp add: possible_steps_0)
    apply (simp add: select_def)
   apply simp
  apply (rule observe_trace_possible_step)
     apply (simp add: possible_steps_1)
    apply (simp add: coin_def apply_outputs select_def value_plus_def)
   apply simp
  apply (rule observe_trace_possible_step)
     apply (simp add: possible_steps_2_coin)
    apply (simp add: coin_def apply_outputs select_def value_plus_def)
   apply simp
  apply (rule observe_trace_possible_step)
     apply simp
     apply (rule possible_steps_2_vend)
      apply (simp add: coin_def select_def join_ir_def input2state_def value_plus_def)
     apply simp
    apply (simp add: vend_def apply_outputs)
    apply (simp add: coin_def select_def)
   apply simp
  by simp

lemma drinks2_0_invalid: "\<not> (aa = (STR ''select'') \<and> length (b) = 1) \<Longrightarrow>
    (possible_steps drinks2 0 <> aa b) = {||}"
  apply (simp add: drinks2_def possible_steps_def transitions)
  by force

lemma step_0: "length i = 1 \<Longrightarrow> step drinks2 0 <> (STR ''select'') i = Some (select, 1, [], <>(1 := hd i, 2 := Num 0))"
  apply (simp add: step_def possible_steps_0 select_def)
  apply (simp add: join_ir_def input2state_nth)
  by (metis One_nat_def add_left_cancel finfun_update_twist hd_conv_nth list.size(3) one_add_one one_neq_zero plus_1_eq_Suc)

lemma drinks2_vend_empty: "possible_steps drinks2 0 <> ((STR ''vend'')) [] = {||}"
  using drinks2_0_invalid by auto

lemma drinks2_vend_insufficient: "possible_steps drinks2 1 r ((STR ''vend'')) [] = {|(1, vend_nothing)|}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma drinks2_2_coin: "fst a = (STR ''coin'') \<and> length (snd a) = 1 \<Longrightarrow> possible_steps drinks2 2 r ((STR ''coin'')) (snd a) = {|(2, coin)|}"
  unfolding possible_steps_def
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma drinks2_vend_r2_none: "r $ 2 = None \<Longrightarrow> possible_steps drinks2 2 r ((STR ''vend'')) [] = {||}"
  apply (simp add: possible_steps_empty drinks2_def)
  apply safe
  by (simp_all add: transitions apply_guards_def ValueGt_def join_ir_def)

lemma label_vend_not_coin: "Label b = ((STR ''vend'')) \<Longrightarrow> b \<noteq> coin"
  using label_coin by auto

lemma drinks2_vend_insufficient2: "r $ 2 = Some (Num x1) \<and> x1 < 100 \<Longrightarrow> possible_steps drinks2 2 r ((STR ''vend'')) [] = {|(2, vend_fail)|}"
  apply (simp add: possible_steps_singleton drinks2_def)
  apply safe
  by (simp_all add: transitions apply_guards_def ValueGt_def join_ir_def)

lemma drinks2_vend_sufficient: "r $ 2 = Some (Num x1) \<Longrightarrow>
                \<not> x1 < 100 \<Longrightarrow>
                possible_steps drinks2 2 r ((STR ''vend'')) [] = {|(3, vend)|}"
  apply (simp add: possible_steps_singleton drinks2_def)
  apply safe
  by (simp_all add: transitions apply_guards_def ValueGt_def join_ir_def)

lemma drinks2_end: "possible_steps drinks2 3 r a b = {||}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma equal_2_3: "observe_trace drinks 2 r t = observe_trace drinks2 3 r t"
proof (induction t)
  case Nil
  then show ?case by (simp add: observations)
next
  case (Cons a t)
  then show ?case
    by (simp add: observe_trace_def step_def drinks2_end drinks_end )
qed

lemma drinks2_vend_r2_String: "r $ 2 = Some (value.Str x2) \<Longrightarrow>
                possible_steps drinks2 2 r ((STR ''vend'')) [] = {||}"
  apply (simp add: possible_steps_empty drinks2_def)
  apply safe
  by (simp_all add: transitions apply_guards_def ValueGt_def join_ir_def)

lemma drinks2_2_invalid: "fst a = (STR ''coin'') \<longrightarrow> length (snd a) \<noteq> 1 \<Longrightarrow>
          a \<noteq> ((STR ''vend''), []) \<Longrightarrow>
          possible_steps drinks2 2 r (fst a) (snd a) = {||}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  apply safe
   apply simp
   apply (metis length_0_conv prod.collapse select_convs(1) select_convs(2) zero_neq_numeral)
  apply simp
  by (metis length_0_conv prod.collapse select_convs(1) select_convs(2))

lemma drinks2_1_invalid: "\<not>(a = (STR ''coin'') \<and> length b = 1) \<Longrightarrow>
      \<not>(a = (STR ''vend'') \<and> b = []) \<Longrightarrow>
    possible_steps drinks2 1 r a b = {||}"
  apply (simp add: possible_steps_empty drinks2_def)
  apply safe
  by (simp_all add: transitions apply_guards_def ValueGt_def join_ir_def)

lemma apply_updates_select: "length (snd a) = 1 \<Longrightarrow> apply_updates (Updates select) (join_ir (snd a) <>) <> = <>(1 := hd (snd a), 2 := Num 0)"
  apply (simp add: apply_updates_def select_def join_ir_def input2state_nth)
  by (metis One_nat_def finfun_update_twist hd_conv_nth length_greater_0_conv lessI numeral_eq_one_iff semiring_norm(85))

lemma apply_updates_vend_fail: "apply_updates (Updates vend_fail) (join_ir i r) r = r"
  by (simp add: transitions join_ir_def)

lemma apply_updates_vend_nothing: "apply_updates (Updates vend_nothing) (join_ir i r) r = r"
  by (simp add: transitions join_ir_def)

lemma drinks2_vend_invalid: "\<nexists>n. r $ 2 = Some (Num n) \<Longrightarrow> possible_steps drinks2 2 r (STR ''vend'') [] = {||}"
  apply (simp add: possible_steps_empty drinks2_def)
  apply safe
  by (simp_all add: transitions apply_guards_def join_ir_def ValueGt_def MaybeBoolInt_not_num_1)

lemma equal_1_2: "\<forall>r. observe_trace drinks 1 r t = observe_trace drinks2 2 r t"
  apply clarify
proof(induct t)
  case Nil
  then show ?case
    by simp
next
  case (Cons a t)
  then show ?case
    apply (case_tac "fst a = (STR ''coin'') \<and> length (snd a) = 1")
     defer
     apply (case_tac "a = (STR ''vend'', [])")
      prefer 2
      apply (rule efsm_equiv_no_possible_step)
       apply (simp add: drinks_1_inaccepts)
    using drinks2_2_invalid apply blast
     apply (case_tac "r $ 2")
      apply (rule efsm_equiv_no_possible_step)
       apply (simp add: drinks_vend_invalid)
      apply (simp add: drinks2_vend_invalid)
     apply (case_tac aa)
      prefer 2
      apply (rule efsm_equiv_no_possible_step)
       apply (simp add: drinks_vend_invalid)
      apply (simp add: drinks2_vend_invalid)
     apply (case_tac "x1 \<ge> 100")
      apply (rule efsm_equiv_possible_step)
           apply (simp add: Drinks_Machine.possible_steps_2_vend)
          apply (simp add: possible_steps_2_vend)
         apply simp
        apply simp
       apply simp
      apply (simp add: equal_2_3)
     apply (rule efsm_equiv_possible_step)
          apply (simp add: drinks_vend_insufficient)
         apply (simp add: not_le drinks2_vend_insufficient2)
        apply simp+
    apply (rule efsm_equiv_possible_step)
         apply (simp add: Drinks_Machine.possible_steps_1_coin)
        apply (simp add: possible_steps_2_coin)
    by auto
qed

lemma eq_1_1: "observe_trace drinks 1 (<>(1 := d, 2 := Num 0)) t = observe_trace drinks2 1 (<>(1 := d, 2 := Num 0)) t"
proof(induct t)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a1 t1)
    then show ?case
      apply (case_tac "fst a1 = (STR ''coin'') \<and> length (snd a1) = 1")
       defer
       apply (case_tac "a1 = (STR ''vend'', [])")
        prefer 2
        apply (rule efsm_equiv_no_possible_step)
         apply (simp add: drinks_1_inaccepts)
        apply (metis drinks2_1_invalid prod.collapse)
       apply (rule efsm_equiv_possible_step)
            apply (simp add: drinks_vend_insufficient)
           apply (simp add: drinks2_vend_insufficient)
          apply (simp add: transitions)
         apply simp
        apply simp
       apply (simp add: apply_updates_vend_fail apply_updates_vend_nothing)
      apply (rule efsm_equiv_possible_step)
           apply (simp add:possible_steps_1_coin)
          apply (simp add: possible_steps_1)
         apply simp
        apply simp
       apply simp
      by (simp add: equal_1_2)
  qed

(* Corresponds to Example 3 in Foster et. al. *)
lemma observational_equivalence: "efsm_equiv drinks drinks2 t"
proof (induct t)
  case Nil
    then show ?case by (simp add: efsm_equiv_def observe_trace_def)
  next
  case (Cons a t)
  then show ?case
    apply (simp only: efsm_equiv_def)
    apply (case_tac "fst a = (STR ''select'') \<and> length (snd a) = 1")
     prefer 2
     apply (rule efsm_equiv_no_possible_step)
    using drinks_0_inaccepts apply blast
    using drinks2_0_invalid apply simp
    apply (rule efsm_equiv_possible_step)
         apply (simp add: Drinks_Machine.possible_steps_0)
        apply (simp add: possible_steps_0)
       apply simp+
    by (simp only: apply_updates_select eq_1_1)
qed
end
