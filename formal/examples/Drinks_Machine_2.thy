subsection\<open>An Observationally Equivalent Model\<close>
text\<open>This theory defines a second formalisation of the drinks machine example which produces
identical output to the first model. This property is called \emph{observational equivalence} and is
discussed in more detail in \cite{foster2018}.\<close>
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

lemmas transitions = Drinks_Machine.transitions vend_nothing_def

definition drinks2 :: transition_matrix where
"drinks2 = {|
              ((0,1), select),
              ((1,1), vend_nothing),
              ((1,2), coin),
              ((2,2), coin),
              ((2,2), vend_fail),
              ((2,3), vend)
         |}"

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
  by (simp_all add: transitions apply_guards_def value_gt_def join_ir_def connectives)

lemma first_step_select: "(s', T) |\<in>| possible_steps drinks 0 r aa b \<Longrightarrow> s' = 1 \<and> T = select"
  apply (simp add: possible_steps_def fimage_def ffilter_def fmember_def Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
  by (simp_all add: transitions)

lemma accepts_first_select: "accepts drinks 0 r ((aa, b) # as) \<Longrightarrow> aa = STR ''select'' \<and> length b = 1"
  using accepts_must_be_possible_step[of drinks 0 r "(aa, b)" as]
  apply simp
  apply clarify
  by (metis first_step_select accepts_possible_steps_not_empty drinks_0_rejects fst_conv snd_conv)

lemma drinks2_vend_insufficient: "possible_steps drinks2 1 r ((STR ''vend'')) [] = {|(1, vend_nothing)|}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma drinks2_vend_insufficient2: "r $ 2 = Some (Num x1) \<Longrightarrow> x1 < 100 \<Longrightarrow> possible_steps drinks2 2 r ((STR ''vend'')) [] = {|(2, vend_fail)|}"
  apply (simp add: possible_steps_singleton drinks2_def)
  apply safe
  by (simp_all add: transitions apply_guards_def value_gt_def join_ir_def connectives)

lemma drinks2_vend_sufficient: "r $ 2 = Some (Num x1) \<Longrightarrow>
                \<not> x1 < 100 \<Longrightarrow>
                possible_steps drinks2 2 r ((STR ''vend'')) [] = {|(3, vend)|}"
  apply (simp add: possible_steps_singleton drinks2_def)
  apply safe
  by (simp_all add: transitions apply_guards_def value_gt_def join_ir_def connectives)

lemma accepts_1_2: "\<forall>r. accepts drinks 1 r t \<longrightarrow> accepts drinks2 2 r t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: accepts.base)
next
  case (Cons a as)
  then show ?case
    apply (cases a)
    apply clarify
    apply (case_tac "aa = STR ''coin'' \<and> length b = 1")
     apply (simp add: accepts_cons)
     apply (simp add: possible_steps_1_coin possible_steps_2_coin)
    apply (case_tac "aa = STR ''vend'' \<and> b = []")
     defer
     apply (simp add: drinks_1_rejects_trace)
    apply (case_tac "r $ 2")
     apply (simp add: drinks_vend_r2_rejects step_none_rejects)
    apply clarify
    apply (case_tac aaa)
    defer
     apply (simp add: drinks_vend_r2_String trace_reject_no_possible_steps)
    apply (case_tac "x1 \<ge> 100")
     defer
     apply (simp add: accepts_cons drinks_vend_insufficient drinks2_vend_insufficient2)
    apply simp
    apply (simp add: accepts_cons drinks_vend_sufficient drinks2_vend_sufficient)
    apply (cases as)
     apply (simp add: accepts.base)
    using drinks_rejects_future by blast
qed

lemma accepts_quantified: "\<forall>s r. accepts drinks s r t \<longrightarrow> accepts drinks2 s r t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: accepts.base)
next
  case (Cons a as)
  then show ?case
    apply (cases a)
    apply clarify
    apply (case_tac "s=0")
     apply simp
     apply (case_tac "aa = STR ''select'' \<and> length b = 1")
      apply (rule accepts.step)
      apply (simp add: possible_steps_0)
    using accepts_cons first_step_select apply fastforce
    using accepts_first_select apply auto[1]
    apply (case_tac "s=1")
     apply (case_tac "aa = STR ''coin'' \<and> length b = 1")
      apply (simp add: accepts_cons possible_steps_1_coin possible_steps_1 accepts_1_2)
     apply (case_tac "aa = STR ''vend'' \<and> b = []")
      defer
      apply (simp add: drinks_1_rejects_trace)
     apply (case_tac "s=2")
      apply (simp add: drinks_end trace_reject_no_possible_steps)
     apply (simp add: invalid_other_states)
    apply (case_tac "r $ 2")
     apply (simp add: drinks_vend_r2_rejects step_none_rejects)
    apply clarify
    apply (case_tac aaa)
    defer
     apply (simp add: drinks_vend_r2_String trace_reject_no_possible_steps)
    apply (case_tac "x1 \<ge> 100")
     defer
     apply (simp add: accepts_cons drinks_vend_insufficient drinks2_vend_insufficient vend_nothing_def vend_fail_def)
    apply simp
    apply (simp add: accepts_cons drinks_vend_sufficient drinks2_vend_insufficient)
    by (metis accepts.simps drinks_rejects_future)
qed

lemma acceptance: "accepts drinks s r t \<Longrightarrow> accepts drinks2 s r t"
  using accepts_quantified by blast

lemma purchase_coke: "observe_trace drinks2 0 <> [((STR ''select''), [Str ''coke'']), ((STR ''coin''), [Num 50]), ((STR ''coin''), [Num 50]), ((STR ''vend''), [])] =
                       [[], [Some (Num 50)], [Some (Num 100)], [Some (Str ''coke'')]]"
  apply (rule observe_trace_possible_step)
     apply (simp add: possible_steps_0)
     apply (simp add: select_def join_ir_def input2state_def accepts_from_1 acceptance)
    apply (simp add: select_def)
   apply (simp add: select_def join_ir_def input2state_def)
  apply (rule observe_trace_possible_step)
      apply (simp add: possible_steps_1)
     apply (simp add: coin_def value_plus_def join_ir_def input2state_def regsimp)
  using accepts_1_2 accepts_from_1a
    apply (simp add: coin_def value_plus_def join_ir_def input2state_def regsimp apply_outputs_def)
   apply (simp add: coin_def value_plus_def join_ir_def input2state_def regsimp)
  apply (rule observe_trace_possible_step)
      apply (simp add: possible_steps_2_coin)
     apply (simp add: coin_def value_plus_def join_ir_def input2state_def regsimp accepts_from_2 accepts_1_2)
    apply (simp add: coin_def value_plus_def join_ir_def input2state_def regsimp apply_outputs_def)
   apply (simp add: coin_def value_plus_def join_ir_def input2state_def regsimp)
  apply (rule observe_trace_possible_step)
      apply (simp add: possible_steps_2_vend)
     apply (simp add: accepts.base)
    apply (simp add: vend_def join_ir_def apply_outputs_def)
   apply simp
  by simp

lemma drinks2_0_invalid: "\<not> (aa = (STR ''select'') \<and> length (b) = 1) \<Longrightarrow>
    (possible_steps drinks2 0 <> aa b) = {||}"
  apply (simp add: drinks2_def possible_steps_def transitions)
  by force

lemma drinks2_vend_r2_none: "r $ 2 = None \<Longrightarrow> possible_steps drinks2 2 r ((STR ''vend'')) [] = {||}"
  apply (simp add: possible_steps_empty drinks2_def)
  apply safe
  by (simp_all add: transitions apply_guards_def value_gt_def join_ir_def connectives)

lemma drinks2_end: "possible_steps drinks2 3 r a b = {||}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma drinks2_vend_r2_String: "r $ 2 = Some (value.Str x2) \<Longrightarrow>
                possible_steps drinks2 2 r ((STR ''vend'')) [] = {||}"
  apply (simp add: possible_steps_empty drinks2_def)
  apply safe
  by (simp_all add: transitions apply_guards_def value_gt_def join_ir_def connectives)

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
  by (simp_all add: transitions apply_guards_def value_gt_def join_ir_def)

lemma drinks2_vend_invalid: "\<nexists>n. r $ 2 = Some (Num n) \<Longrightarrow> possible_steps drinks2 2 r (STR ''vend'') [] = {||}"
  apply (simp add: possible_steps_empty drinks2_def)
  apply safe
  by (simp_all add: transitions apply_guards_def join_ir_def value_gt_def MaybeBoolInt_not_num_1 connectives)

lemma rejects_1_2: "\<forall>r. \<not> accepts drinks 1 r t \<longrightarrow> \<not> accepts drinks2 2 r t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: accepts.base)
next
  case (Cons a t)
  then show ?case
    apply (cases a)
    apply (case_tac "aa = STR ''coin'' \<and> length b = 1")
     apply (simp add: accepts_cons possible_steps_1_coin possible_steps_2_coin)
    apply (case_tac "aa = STR ''vend'' \<and> b = []")
     defer
    using accepts_possible_steps_not_empty drinks2_2_invalid apply fastforce
    apply (rule allI)
    apply (case_tac "r $ 2")
     apply (simp add: drinks2_vend_r2_none trace_reject_no_possible_steps)
    apply (case_tac aaa)
    defer
     apply (simp add: drinks2_vend_invalid trace_reject_no_possible_steps)
    apply (case_tac "x1 \<ge> 100")
     apply (simp add: trace_reject_2 drinks_vend_sufficient drinks2_vend_sufficient)
     apply (case_tac t)
      apply (simp add: accepts.base)
     apply simp
     apply standard
    using accepts_possible_steps_not_empty drinks2_end apply blast
    by (simp add: trace_reject_2 drinks_vend_insufficient drinks2_vend_insufficient2)
qed


lemma accepts_1_1: "\<not> accepts drinks 1 (<>(1 := d, 2 := Num 0)) t \<Longrightarrow> \<not> accepts drinks2 1 (<>(1 := d, 2 := Num 0)) t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: accepts.base)
next
  case (Cons a t)
  then show ?case
    apply (case_tac "a = (STR ''vend'', [])")
     apply (simp add: trace_reject_2 drinks_vend_insufficient drinks2_vend_insufficient vend_fail_def vend_nothing_def join_ir_def)
     apply (simp add: finfun_update_twist)
    apply (cases a)
    apply (case_tac "aa = STR ''coin'' \<and> length b = 1")
     apply (simp add: trace_reject_2 possible_steps_1_coin possible_steps_1)
    using rejects_1_2 apply blast
    by (simp add: drinks2_1_invalid trace_reject_no_possible_steps)
qed

lemma equiv_1_2: "\<forall>r. observe_trace drinks 1 r t = observe_trace drinks2 2 r t"
proof(induct t)
  case Nil
  then show ?case
    by simp
next
  case (Cons a t)
  then show ?case
    apply clarify
    apply (case_tac "fst a = STR ''coin'' \<and> length (snd a) = 1")
     defer
     apply (case_tac "a = (STR ''vend'', [])")
      defer
      apply (rule observe_trace_no_possible_steps)
       apply (simp add: drinks_1_rejects)
      apply (simp add: drinks2_2_invalid)
     apply (rule observe_trace_one_possible_step)
          apply (simp add: possible_steps_1_coin)
         apply (simp add: possible_steps_2_coin)
        apply simp+
    apply (case_tac "\<exists>n. r $ 2 = Some (Num n)")
     defer
     apply (rule observe_trace_no_possible_steps)
      apply (simp add: drinks_vend_invalid)
     apply (simp add: drinks2_vend_invalid)
    apply clarify
    apply (case_tac "n < 100")
     apply (rule observe_trace_one_possible_step)
          apply (simp add: Drinks_Machine.drinks_vend_insufficient)
         apply (simp add: drinks2_vend_insufficient2)
        apply simp+
    apply (rule observe_trace_one_possible_step)
         apply (simp add: Drinks_Machine.drinks_vend_sufficient)
        apply (simp add: drinks2_vend_sufficient)
       apply simp+
    apply (induct t)
     apply simp
    apply (rule observe_trace_no_possible_steps)
     apply (simp add: drinks_end)
    by (simp add: drinks2_end)
qed

lemma equiv_1_1: "observe_trace drinks 1 (<>(2 := Num 0, 1 := snd a ! 0)) t = observe_trace drinks2 1 (<>(2 := Num 0, 1 := snd a ! 0)) t"
proof(induct t)
  case Nil
  then show ?case
    by simp
next
  case (Cons a t)
  then show ?case
    apply (case_tac "fst a = STR ''coin'' \<and> length (snd a) = 1")
     defer
     apply (case_tac "a = (STR ''vend'', [])")
      defer
      apply (rule observe_trace_no_possible_steps)
       apply (simp add: drinks_1_rejects)
      apply (metis drinks2_1_invalid prod.collapse)
     apply (rule observe_trace_one_possible_step)
          apply (simp add: possible_steps_1_coin)
         apply (simp add: possible_steps_1)
        apply simp+
     apply (simp add: equiv_1_2)
    apply (rule observe_trace_one_possible_step)
         apply (simp add: drinks_vend_insufficient)
        apply (simp add: drinks2_vend_insufficient)
       apply (simp add: vend_fail_def vend_nothing_def)+
    by (simp add: datastate(1) finfun_update_twist)
qed


(* Corresponds to Example 3 in Foster et. al. *)
lemma observational_equivalence: "observably_equivalent drinks drinks2 t"
proof (induct t)
  case Nil
  then show ?case
    by (simp add: observably_equivalent_def)
  next
  case (Cons a t)
  then show ?case
    apply (simp add: observably_equivalent_def)
    apply (case_tac "fst a = STR ''select'' \<and> length (snd a) = 1")
     defer
     apply (rule observe_trace_no_possible_steps)
    using drinks_0_rejects apply blast
    using drinks2_0_invalid apply blast
     apply (rule observe_trace_one_possible_step)
          apply (simp add: Drinks_Machine.possible_steps_0)
         apply (simp add: possible_steps_0)
       apply simp+
    by (simp add: select_def join_ir_def input2state_nth equiv_1_1)
qed

lemma "\<not>same_structure vend vend_nothing"
  apply (simp add: same_structure_def)
  by (simp add: vend_def vend_nothing_def)

end
