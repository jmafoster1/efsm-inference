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
        Updates = [(R 1, V (R 1)), (R 2, V (R 2))]
      \<rparr>"

lemma guard_vend_nothing: "Guard vend_nothing = []"
  by (simp add: vend_nothing_def)

lemma updates_vend_nothing: "Updates vend_nothing = [(R 1, V (R 1)), (R 2, V (R 2))]"
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

lemma possible_steps_2_vend: "r (R 2) = Some (Num n) \<Longrightarrow> n \<ge> 100 \<Longrightarrow> possible_steps drinks2 2 r ((STR ''vend'')) [] = {|(3, vend)|}"
proof-
  assume prem1: "r (R 2) = Some (Num n)"
  assume prem2: "n \<ge> 100"
  have filter: "ffilter
     (\<lambda>((origin, dest), t).
         origin = 2 \<and>
         Label t = STR ''vend'' \<and> Arity t = 0 \<and> apply_guards (Guard t) (\<lambda>x. case x of I n \<Rightarrow> input2state [] 1 (I n) | R n \<Rightarrow> r (R n)))
     drinks2 =
    {|((2, 3), vend)|}"
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse drinks2_def Set.filter_def)
    apply safe
    using prem1 prem2
    by (simp_all add: transitions gval.simps ValueGt_def)
  show ?thesis
    by (simp add: possible_steps_def filter)
qed

lemma purchase_coke: "observe_trace drinks2 0 <> [((STR ''select''), [Str ''coke'']), ((STR ''coin''), [Num 50]), ((STR ''coin''), [Num 50]), ((STR ''vend''), [])] =
                       [[], [Some (Num 50)], [Some (Num 100)], [Some (Str ''coke'')]]"
  apply (simp add: observe_trace_def step_def possible_steps_0 updates_select)
  apply (simp add: possible_steps_1 step_def updates_coin)
  apply (simp add: possible_steps_2_coin step_def updates_coin)
  using possible_steps_2_vend
  apply simp
  by (simp add: transitions )

lemma "consistent (medial empty (Guard select))"
  by (simp add: select_def medial_empty)

definition r1_r2_true :: "context" where
"r1_r2_true \<equiv> \<lbrakk>(V (R 1)) \<mapsto> {|Bc True|}, (V (R 2)) \<mapsto> {|Bc True|}\<rbrakk>"

lemma posterior_coin_first: "posterior select_posterior coin = r1_r2_true"
  apply (simp add: posterior_def posterior_separate_def coin_def medial_empty consistent_select_posterior)
  apply (simp add: remove_obsolete_constraints_def r1_r2_true_def)
  apply (rule ext)
  by (simp add: select_posterior_def fprod_singletons)

lemma consistent_r1_r2_true: "consistent r1_r2_true"
  apply (simp add: consistent_def r1_r2_true_def cval_true)
  using consistent_def consistent_empty by blast

lemma posterior_coin_subsequent: "posterior r1_r2_true coin = r1_r2_true"
  apply (simp add: posterior_def coin_def posterior_separate_def medial_empty consistent_r1_r2_true)
  apply (simp add: remove_obsolete_constraints_def r1_r2_true_def)
  apply (rule ext)
  by (simp add: fprod_singletons r1_r2_true_def)

lemma can_take_coin: "consistent c \<longrightarrow> Contexts.can_take coin c"
  by (simp add: can_take_def coin_def medial_empty)

lemma posterior_n_coin_true_true: "(posterior_n n coin r1_r2_true) = r1_r2_true"
  proof (induct n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    then show ?case
      by (simp add: posterior_coin_subsequent)
  qed

lemma consistent_posterior_n_coin: "consistent (posterior_n n coin select_posterior)" (* We can go round coin as many times as we like *)
  proof(induct n)
    case 0
    then show ?case
      apply (simp add: consistent_def)
      apply (simp add: select_posterior_def)
      apply (rule_tac x="<R 2 := Num 0>" in exI)
      apply (simp add: cval_def gval.simps ValueEq_def)
      apply (rule allI)
      apply (case_tac r)
         apply (simp add: gval.simps)
        apply (case_tac x2)
         apply (simp add: gval.simps)
        apply (simp add: gval.simps ValueEq_def)
      by (simp_all add: gval.simps)
  next
    case (Suc n)
    then show ?case
      apply (simp add: posterior_coin_first posterior_n_coin_true_true)
      using consistent_r1_r2_true r1_r2_true_def posterior_n_coin_true_true by auto
  qed

lemma posterior_n_coin_true_2: "(posterior_n (Suc n) coin select_posterior) = r1_r2_true"
  proof (induction n)
    case 0
    then show ?case
      apply (simp )
      by (simp only: posterior_coin_first)
  next
    case (Suc n)
    then show ?case
      apply simp
      apply (simp add: posterior_coin_first)
      by (simp only: posterior_coin_subsequent)
  qed

lemma can_take_vend: "0 < Suc n \<longrightarrow> Contexts.can_take vend r1_r2_true"
  apply (simp add: can_take_def vend_def medial_def r1_r2_true_def List.maps_def pairs2context_def consistent_def)
  apply (rule_tac x="<R 2 := Num 100>" in exI)
  apply (simp add: cval_def gval.simps ValueGt_def)
  apply (rule allI)
  apply (case_tac r)
     apply (simp add: gval.simps)
    apply (case_tac x2)
     apply (simp add: gval.simps)
    apply (simp add: gval.simps ValueEq_def)
  by (simp_all add: gval.simps)

lemma medial_vend: "medial r1_r2_true (Guard vend) = \<lbrakk>(V (R 1)) \<mapsto> {|Bc True|}, (V (R 2)) \<mapsto> {|Geq (Num 100), Bc True|}\<rbrakk>"
  apply (rule ext)
  by (simp add: vend_def r1_r2_true_def medial_def List.maps_def pairs2context_def)

lemma consistent_medial_vend: "consistent (medial r1_r2_true (Guard vend))"
  apply (simp add: consistent_def medial_vend)
  apply (rule_tac x="<R 2 := Num 100>" in exI)
  apply (simp add: cval_def gval.simps ValueGt_def)
  apply (rule allI)
  apply (case_tac r)
     apply (simp add: gval.simps)
    apply (case_tac x2)
  by (simp_all add: gval.simps ValueEq_def)

lemma drinks2_0_invalid: "\<not> (aa = (STR ''select'') \<and> length (b) = 1) \<Longrightarrow>
    (possible_steps drinks2 0 Map.empty aa b) = {||}"
  apply (simp add: drinks2_def possible_steps_def transitions)
  by force

lemma step_0: "length i = 1 \<Longrightarrow> step drinks2 0 Map.empty (STR ''select'') i = Some (select, 1, [], <R 1 := hd i, R 2 := Num 0>)"
  apply (simp add: step_def possible_steps_0 select_def)
  apply (rule ext)
  apply (simp)
  using hd_input2state by auto

lemma updates_select: "length (snd a) = 1 \<Longrightarrow> (EFSM.apply_updates (Updates select) (case_vname (\<lambda>n. input2state (snd a) 1 (I n)) Map.empty) Map.empty) = <R 1:=hd (snd a), R 2 := Num 0>"
  apply (simp add: select_def)
  apply (rule ext)
  by (simp add: hd_input2state)

lemma drinks2_vend_empty: "possible_steps drinks2 0 Map.empty ((STR ''vend'')) [] = {||}"
  using drinks2_0_invalid by auto

lemma drinks2_vend_insufficient: "possible_steps drinks2 1 r ((STR ''vend'')) [] = {|(1, vend_nothing)|}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma apply_updates_vend_fail: "(EFSM.apply_updates (Updates vend_fail) (case_vname Map.empty (\<lambda>n. if n = 2 then Some (Num n') else <R 1 := s> (R n)))
         <R 1 := s, R 2 := Num 0>) = <R 1 := s, R 2 := Num n'>"
  apply (rule ext)
  by (simp add: vend_fail_def)

lemma apply_updates_vend_nothing: "(EFSM.apply_updates (Updates vend_nothing) (case_vname Map.empty (\<lambda>n. if n = 2 then Some (Num n') else <R 1 := s> (R n)))
         <R 1 := s, R 2 := Num 0>) = <R 1 := s, R 2 := Num n'>"
  apply (rule ext)
  by (simp add: vend_nothing_def)

lemma coin_updates: "(EFSM.apply_updates (Updates coin) (case_vname (\<lambda>n. input2state (snd a) 1 (I n)) (\<lambda>n. if n = 2 then Some v else if R n = R 1 then Some s else None))
       (\<lambda>a. if a = R 2 then Some v else if a = R 1 then Some s else None)) = (\<lambda>u. if u = R 1 then Some s else if u = R 2 then value_plus (Some v) (input2state (snd a) 1 (I 1)) else None)"
  apply (rule ext)
  by (simp add: coin_def)

lemma drinks2_2_coin: "fst a = (STR ''coin'') \<and> length (snd a) = 1 \<Longrightarrow> possible_steps drinks2 2 r ((STR ''coin'')) (snd a) = {|(2, coin)|}"
  unfolding possible_steps_def
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma updates_coin_2: "(EFSM.apply_updates (Updates coin) (case_vname (\<lambda>n. input2state (snd a) 1 (I n)) (\<lambda>n. if n = 1 then Some s else if R n = R 2 then r2 else None))
             (\<lambda>u. if u = R 1 then Some s else if u = R 2 then r2 else None)) = (\<lambda>u. if u = R 1 then Some s else if u = R 2 then value_plus r2  (input2state (snd a) 1 (I 1)) else None)"
  apply (rule ext)
  by (simp add: coin_def)

lemma drinks2_vend_r2_none: "r (R 2) = None \<Longrightarrow> possible_steps drinks2 2 r ((STR ''vend'')) [] = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse drinks2_def Set.filter_def)
  apply (rule allI)+
  apply (case_tac "ba = coin")
   apply (simp add: coin_def)
  apply (case_tac "ba = vend_fail")
   apply (simp add: transitions gval.simps ValueGt_def)
  by (simp add: transitions gval.simps ValueGt_def)

lemma label_vend_not_coin: "Label b = ((STR ''vend'')) \<Longrightarrow> b \<noteq> coin"
  using label_coin by auto

lemma drinks2_vend_insufficient2: "r (R 2) = Some (Num x1) \<and> x1 < 100 \<Longrightarrow> possible_steps drinks2 2 r ((STR ''vend'')) [] = {|(2, vend_fail)|}"
proof-
  assume premise: "r (R 2) = Some (Num x1) \<and> x1 < 100"
  have filter: "ffilter
     (\<lambda>((origin, dest), t).
         origin = 2 \<and>
         Label t = STR ''vend'' \<and> Arity t = 0 \<and> apply_guards (Guard t) (\<lambda>x. case x of I n \<Rightarrow> input2state [] 1 (I n) | R n \<Rightarrow> r (R n)))
     drinks2 =
    {|((2, 2), vend_fail)|}"
    using premise
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks2_def)
    apply safe
    by (simp_all add: transitions gval.simps ValueGt_def)
  show ?thesis
    by (simp add: possible_steps_def filter)
qed

lemma updates_vend_fail: "(EFSM.apply_updates (Updates vend_fail) (case_vname Map.empty (\<lambda>n. if n = 1 then Some s else if R n = R 2 then r2 else None))
                   (\<lambda>u. if u = R 1 then Some s else if u = R 2 then r2 else None)) = (\<lambda>u. if u = R 1 then Some s else if u = R 2 then r2 else None)"
  apply (rule ext)
  by (simp add: vend_fail_def)

lemma drinks2_vend_sufficient: "r (R 2) = Some (Num x1) \<Longrightarrow>
                \<not> x1 < 100 \<Longrightarrow>
                possible_steps drinks2 2 r ((STR ''vend'')) [] = {|(3, vend)|}"
proof-
  assume premise1: "r (R 2) = Some (Num x1)"
  assume premise2 : "\<not> x1 < 100"
  have filter: "ffilter
     (\<lambda>((origin, dest), t).
         origin = 2 \<and>
         Label t = STR ''vend'' \<and> Arity t = 0 \<and> apply_guards (Guard t) (\<lambda>x. case x of I n \<Rightarrow> input2state [] 1 (I n) | R n \<Rightarrow> r (R n)))
     drinks2 =
    {|((2, 3), vend)|}"
    using premise1 premise2
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks2_def)
    apply safe
    by (simp_all add: transitions gval.simps ValueGt_def)
  show ?thesis
    by (simp add: possible_steps_def filter)
qed

lemma vend_updates: "(EFSM.apply_updates (Updates vend) (case_vname Map.empty (\<lambda>n. if n = 1 then Some s else if R n = R 2 then r2 else None))
                   (\<lambda>u. if u = R 1 then Some s else if u = R 2 then r2 else None)) = (\<lambda>u. if u = R 1 then Some s else if u = R 2 then r2 else None)"
  apply (rule ext)
  by (simp add: vend_def)

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

lemma drinks2_vend_r2_String: "r (R 2) = Some (value.Str x2) \<Longrightarrow>
                possible_steps drinks2 2 r ((STR ''vend'')) [] = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks2_def)
  apply (rule allI)+
  apply (case_tac "ba = coin")
   apply (simp add: coin_def)
  apply (case_tac "ba = vend_fail")
   apply (simp add: vend_fail_def gval.simps ValueGt_def)
  by (simp add: vend_def gval.simps ValueGt_def)

lemma drinks2_2_invalid: "fst a = (STR ''coin'') \<longrightarrow> length (snd a) \<noteq> 1 \<Longrightarrow>
          a \<noteq> ((STR ''vend''), []) \<Longrightarrow>
          possible_steps drinks2 2 r (fst a) (snd a) = {||}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  apply safe
   apply simp
   apply (metis length_0_conv prod.collapse select_convs(1) select_convs(2) zero_neq_numeral)
  apply simp
  by (metis length_0_conv prod.collapse select_convs(1) select_convs(2))

lemma equal_1_2: "\<forall>r2. observe_trace drinks 1 (\<lambda>u. if u = R 1 then Some s else if u = R 2 then r2 else None) t =
    observe_trace drinks2 2 (\<lambda>u. if u = R 1 then Some s else if u = R 2 then r2 else None) t"
proof (induction t)
  case Nil
  then show ?case
    by (simp add: observe_trace_def)
next
  case (Cons a t)
  then show ?case
    apply clarify
    apply (case_tac "fst a = (STR ''coin'') \<and> length (snd a) = 1")
    unfolding observe_trace_def
    apply (simp add: step_def)
     apply (simp add: drinks_1_coin coin_updates drinks2_2_coin updates_coin_2)
     apply (simp)

    apply (simp add: step_def)
    apply (case_tac "a = ((STR ''vend''), [])")
     apply (case_tac r2)
      apply (simp add: step_def)
    apply (simp add: drinks_vend_r2_none drinks2_vend_r2_none )
     apply (case_tac aa)
      apply (case_tac "x1 < 100")
    apply (simp add: step_def)
    apply (simp add: drinks_vend_insufficient drinks2_vend_insufficient2 updates_vend_fail )
    apply (simp add: step_def)
      apply (simp add: drinks_vend_sufficient drinks2_vend_sufficient vend_updates )
    using equal_2_3 observe_trace_def apply auto[1]
     apply (simp add: step_def)
     apply (simp add: drinks_vend_r2_String drinks2_vend_r2_String )
    by (simp add: drinks_1_inaccepts drinks2_2_invalid )
qed

lemma drinks2_1_invalid: "\<not>(a = (STR ''coin'') \<and> length b = 1) \<Longrightarrow>
      \<not>(a = (STR ''vend'') \<and> b = []) \<Longrightarrow>
    possible_steps drinks2 1 r a b = {||}"
proof-
  assume premise1: "\<not>(a = (STR ''coin'') \<and> length b = 1)"
  assume premise2: "\<not>(a = (STR ''vend'') \<and> b = [])"
  have set_filter: "Set.filter
       (\<lambda>((origin, dest), t).
           origin = 1 \<and> Label t = a \<and> length b = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state b 1 (I n)) (\<lambda>n. r (R n))))
       (fset drinks2) = {}"
    using premise1 premise2
    apply (simp add: Set.filter_def drinks2_def)
    apply safe
    by (simp_all add: transitions)
  show ?thesis
    by (simp add: possible_steps_def ffilter_def set_filter)
qed

lemma coin_updates_equiv: "(EFSM.apply_updates (Updates coin)
         (case_vname (\<lambda>n. input2state (snd a) 1 (I n)) (\<lambda>n. if n = 2 then Some (Num 0) else <R 1 := s> (R n)))
         <R 1 := s, R 2 := Num 0>) = (\<lambda>u. if u = R 1 then Some s else if u = R 2 then value_plus (Some (Num 0)) (input2state (snd a) 1 (I 1))
 else None)"
  apply (simp add: coin_def)
  apply (rule ext)
  by simp

lemma equal_1_1: "observe_trace drinks 1 <R 1 := s, R 2 := Num 0> t = observe_trace drinks2 1 <R 1 := s, R 2 := Num 0> t"
proof (induction t)
  case Nil
  then show ?case
    unfolding observe_trace_def
    by simp
next
  case (Cons a t)
  then show ?case
    unfolding observe_trace_def
    apply (case_tac "fst a = (STR ''coin'') \<and> length (snd a) = 1")
     apply (simp add: step_def)
     apply (simp only: drinks_1_coin possible_steps_1)
     apply (simp add: )
    apply (simp only: coin_updates_equiv)
    using equal_1_2 observe_trace_def
    apply simp
    apply (case_tac "a = ((STR ''vend''), [])")
      apply (simp)
      apply (simp add: step_def drinks_vend_insufficient drinks2_vend_insufficient)
     apply (simp add: outputs_vend_fail outputs_vend_nothing )
     apply (simp add: apply_updates_vend_fail apply_updates_vend_nothing)

    apply (case_tac a)
    apply (simp add: step_def)
    using drinks_1_inaccepts drinks2_1_invalid step_def
    by auto
qed

lemma observational_equivalence: "efsm_equiv drinks drinks2 t" (* Corresponds to Example 3 in Foster et. al. *)
proof (induct t)
  case Nil
    then show ?case by (simp add: efsm_equiv_def observe_trace_def)
  next
  case (Cons a t)
  then show ?case
    apply (simp only: efsm_equiv_def observe_trace_def)
    apply (case_tac "fst a = (STR ''select'') \<and> length (snd a) = 1")
     prefer 2
     apply (simp add: drinks2_0_invalid drinks_0_inaccepts is_singleton_def step_def )
    apply (simp)
    apply (simp add: possible_steps_0 Drinks_Machine.possible_steps_0 updates_select step_def)
    apply (case_tac t)
     apply simp
    using equal_1_1
    by (metis observe_trace_def)
qed

lemma step_drinks_2: "step drinks2 0 Map.empty aa ba = Some (uw, s', ux, r') \<Longrightarrow> (uw, s', ux, r') = (select, 1, [], <R 1 := hd ba, R 2 := Num 0>)"
  apply (simp add: step_def)
  apply (case_tac "aa = (STR ''select'') \<and> length ba = 1")
   apply (simp add: possible_steps_0)
   apply clarify
   apply (simp add: select_def)
   apply (rule ext)
   apply (simp add: hd_input2state)
  by (simp add: drinks2_0_invalid)

lemma step_drinks2_vend_fail: "step drinks2 1 ra (STR ''vend'') [] = Some (vend_nothing, 1, [], ra)"
  apply (simp add: step_def drinks2_vend_insufficient)
  apply (simp add: vend_nothing_def)
  apply (rule ext)
  by simp

lemma step_2_or_3: "step drinks2 2 r a b = Some (uw, s', ux, r') \<Longrightarrow> s' = 2 \<or> s' = 3"
  apply (simp add: step_def)
  apply (case_tac "a = (STR ''coin'') \<and> length b = 1")
   apply simp
  using drinks2_2_coin
   apply auto[1]
  apply simp
  apply (case_tac "a = (STR ''vend'') \<and> b = []")
   apply simp
   apply clarify
   apply (case_tac "r (R 2)")
    apply (simp add: drinks2_vend_r2_none)
   apply (case_tac aa)
    prefer 2
    apply (simp add: drinks2_vend_r2_String)
   apply simp
   apply (case_tac "x1 < 100")
    apply (simp add: drinks2_vend_insufficient2)
    apply (simp add: drinks2_vend_sufficient)
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
end
