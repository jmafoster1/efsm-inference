subsection{*An Observationally Equivalent Model*}
text{*This theory defines a second formalisation of the drinks machine example which produces
identical output to the first model. This property is called \emph{observational equivalence} and is
discussed in more detail in \cite{foster2018}.*}
theory Drinks_Machine_2
  imports Drinks_Machine "../Contexts"
begin

declare One_nat_def [simp del]

definition vend_nothing :: "transition" where
"vend_nothing \<equiv> \<lparr>
        Label = ''vend'',
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

lemma label_vend_nothing: "Label vend_nothing = ''vend''"
  by (simp add: vend_nothing_def)

definition drinks2 :: transition_matrix where
"drinks2 = {|
              ((0,1), select),
              ((1,1), vend_nothing),
              ((1,2), coin),
              ((2,2), coin),
              ((2, 2), vend_fail),
              ((2,3), vend)
         |}"

lemma empty_not_singleton [simp]: "\<not> is_singleton {}"
  by (simp add: is_singleton_def)

lemma possible_steps_0:  "length i = 1 \<Longrightarrow> possible_steps drinks2 0 r (''select'') i = {|(1, select)|}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma possible_steps_1: "length i = 1 \<Longrightarrow> possible_steps drinks2 1 r (''coin'') i = {|(2, coin)|}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma possible_steps_2_coin: "length i = 1 \<Longrightarrow> possible_steps drinks2 2 r (''coin'') i = {|(2, coin)|}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma possible_steps_2_vend: "\<exists>n. r (R 2) = Some (Num n) \<and> n \<ge> 100 \<Longrightarrow> possible_steps drinks2 2 r (''vend'') [] = {|(3, vend)|}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma purchase_coke: "observe_trace drinks2 0 <> [(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 50]), (''vend'', [])] = [[], [Num 50], [Num 100], [Str ''coke'']]"
  apply (simp add: observe_trace_def step_def possible_steps_0 updates_select)
  apply (simp add: possible_steps_1 step_def updates_coin)
  apply (simp add: possible_steps_2_coin step_def updates_coin)
  using possible_steps_2_vend
  apply simp
  by (simp add: transitions )

lemma "consistent (medial empty (Guard select))"
  by (simp add: select_def)

lemma empty_not_undef: "empty r \<noteq> Undef \<longrightarrow> empty r = Bc True"
  apply (insert consistent_empty_1)
  by auto

lemma empty_never_false: "cexp.Bc False \<noteq> Contexts.empty x"
  apply (cases x)
     prefer 2
    apply (case_tac x2)
  by simp_all

lemma posterior_coin_first: "posterior select_posterior coin = \<lbrakk>(V (R 1)) \<mapsto> Bc True, (V (R 2)) \<mapsto> Bc True\<rbrakk>"
  unfolding posterior_def Let_def
  apply (simp add: guard_coin consistent_select_posterior)
  apply (simp add: transitions valid_def satisfiable_def remove_input_constraints_def)
  apply (rule ext)
  by simp

abbreviation r1_r2_true :: "context" where
"r1_r2_true \<equiv> \<lbrakk>(V (R 1)) \<mapsto> Bc True, (V (R 2)) \<mapsto> Bc True\<rbrakk>"

lemma consistent_r1_r2_true: "consistent r1_r2_true"
  apply (simp add: consistent_def)
  apply (rule_tac x="<>" in exI)
  apply (simp del: Nat.One_nat_def)
  using consistent_empty_1
  by fastforce

lemma posterior_coin_subsequent: "posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Bc True\<rbrakk> coin = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Bc True\<rbrakk>"
  unfolding posterior_def Let_def
  apply (simp add: guard_coin consistent_r1_r2_true remove_input_constraints_def)
  apply (rule ext)
  by (simp add: transitions satisfiable_def)

lemma value_lt_aval: "aval x r = Some a \<Longrightarrow> aval y r = Some aa \<Longrightarrow> ValueLt (Some a) (Some aa) = Some ab \<Longrightarrow> \<exists>n n'. a = Num n \<and> aa = Num n'"
  by (metis MaybeBoolInt.elims option.sel option.simps(3))

lemma ge_equiv: "gval (Ge x y) r = gval (gOr (gexp.Gt x y) (gexp.Eq x y)) r"
  apply simp
  apply (cases "aval x r")
   apply (cases "aval y r")
    apply simp
   apply simp
   apply (cases "aval y r")
   apply simp
  apply simp
  apply (case_tac aa)
  apply (case_tac a)
  by auto

lemma apply_guard_ge_100: "(apply_guard \<lbrakk>V (R 1) \<mapsto> cexp.Bc True\<rbrakk> (Ge (V (R 1)) (L (Num 100)))) = \<lbrakk>V (R 1) \<mapsto> Geq (Num 100)\<rbrakk>"
  apply (rule ext)
  by simp

lemma apply_gt_100_eq_100: "(apply_guard \<lbrakk>V (R 1) \<mapsto> cexp.Bc True\<rbrakk> (gOr (GExp.Lt (L (Num 100)) (V (R 1))) (gexp.Eq (V (R 1)) (L (Num 100))))) = \<lbrakk>V (R 1) \<mapsto> cexp.Not (And (Neq (Num 100)) (Leq (Num 100)))\<rbrakk>"
  apply (rule ext)
  by simp

lemma "cexp_equiv (cexp.Not (And (Neq (Num 100)) (Leq (Num 100)))) (Geq (Num 100))"
  apply (simp add: cexp_equiv_def)
  apply (rule allI)
  apply (case_tac i)
   apply auto[1]
  by simp

lemma "context_equiv (apply_guard \<lbrakk>(V (R 1)) \<mapsto> Bc True\<rbrakk> (Ge (V (R 1)) (L (Num 100))))
                      (apply_guard \<lbrakk>(V (R 1)) \<mapsto> Bc True\<rbrakk> (gOr (gexp.Gt (V (R 1)) (L (Num 100))) (gexp.Eq (V (R 1)) (L (Num 100)))))"
  apply (simp only: apply_guard_ge_100 apply_gt_100_eq_100)
  apply (simp only: context_equiv_def cexp_equiv_def)
  apply safe
    apply (case_tac r)
       apply simp
      apply simp
      apply (case_tac i)
       apply auto[1]
      apply auto[1]
     apply (case_tac r)
        apply simp
       apply simp
      apply simp
     apply simp
    apply simp
   apply (case_tac r)
      apply simp
     apply (case_tac "x2=R 1")
      apply simp
     apply simp
    apply simp
   apply simp
  apply (case_tac r)
     apply simp
    apply (case_tac "x2=R 1")
     apply simp
    apply simp
   apply simp
  by simp

lemma not_eq_0_and_ge_100:"\<not> GExp.satisfiable (gAnd (gexp.Eq (V (R 2)) (L (Num 0))) (Ge (V (R 2)) (L (Num 100))))"
  apply (simp add: GExp.satisfiable_def)
  apply (rule allI)
  apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some (Num 100)) (s (R 2))")
   apply simp
  apply simp
  apply (case_tac "s (R 2) = Some (Num 0)")
   apply simp
  by simp

lemma can_take_coin: "consistent c \<longrightarrow> Contexts.can_take coin c"
  by (simp add: coin_def consistent_def Contexts.can_take_def)

lemma valid_posterior_coin_subsequent: "valid_context (posterior r1_r2_true coin)"
  apply (simp add: posterior_coin_subsequent)
  apply (simp add: valid_context_def)
  apply (simp add: posterior_coin_subsequent One_nat_def)
  by (simp add: consistent_empty_4)

lemma valid_true: "valid c \<longrightarrow> cexp_equiv c (Bc True)"
  apply (simp add: valid_def cexp_equiv_def)
  by auto

lemma consistent_medial_coin_3: "consistent (\<lambda>a. if a = V (R 2) then cexp.Eq (Num 0) else if a = V (R 1) then cexp.Bc True else \<lbrakk>\<rbrakk> a)"
  apply (simp add: consistent_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num 0>" in exI)
  apply (simp del: Nat.One_nat_def)
  by (simp add: consistent_empty_4)

lemma select_posterior_equiv: "(\<lambda>a. if a = V (R 2) then cexp.Eq (Num 0) else if a = V (R 1) then cexp.Bc True else \<lbrakk>\<rbrakk> a) = select_posterior"
  apply (rule ext)
  by simp

lemma posterior_coin_true: "(posterior (\<lambda>a. if a = V (R 2) then cexp.Eq (Num 0) else if a = V (R 1) then cexp.Bc True else \<lbrakk>\<rbrakk> a) coin) = r1_r2_true"
  unfolding posterior_def Let_def
  apply (simp add: guard_coin)
  apply (simp only: select_posterior_equiv consistent_select_posterior)
  apply (simp add: coin_def valid_def satisfiable_def remove_input_constraints_def)
  apply (rule ext)
  by simp

lemma r1_r2_true_equiv: "(\<lambda>a. if a = V (R 2) then cexp.Bc True else if a = V (R 1) then cexp.Bc True else \<lbrakk>\<rbrakk> a) = r1_r2_true"
  apply (rule ext)
  by simp

lemma posterior_n_coin_true_true: "(posterior_n n coin r1_r2_true) = r1_r2_true"
  proof (induct n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    then show ?case
      apply (simp add: r1_r2_true_equiv posterior_coin_subsequent  del: Nat.One_nat_def)
      using posterior_coin_subsequent by auto
  qed

lemma consistent_posterior_n_coin: "consistent (posterior_n n coin select_posterior)" (* We can go round coin as many times as we like *)
  proof(induct n)
    case 0
    then show ?case
      apply (simp add: consistent_def)
      apply (rule_tac x="<R 1 := Num 0, R 2 := Num 0>" in exI)
      apply (simp del: Nat.One_nat_def)
      using consistent_empty_4 by blast
  next
    case (Suc n)
    then show ?case
      apply (simp del: Nat.One_nat_def)
      apply (simp add: select_posterior_equiv del: Nat.One_nat_def)
      apply (simp only:  posterior_coin_first posterior_n_coin_true_true)
      using consistent_r1_r2_true by blast
  qed

lemma coin_before_vend: "Contexts.can_take vend (posterior_n n coin (posterior \<lbrakk>\<rbrakk> select)) \<longrightarrow> n > 0" (* We have to do a "coin" before we can do a "vend"*)
  apply (simp add: select_posterior del: Nat.One_nat_def)
  apply (cases n)
   apply (simp add: r2_0_vend del: Nat.One_nat_def)
  by simp

lemma posterior_n_coin_true_2: "(posterior_n (Suc n) coin select_posterior) = r1_r2_true"
  proof (induction n)
    case 0
    then show ?case
      apply (simp del: Nat.One_nat_def)
      apply (simp only: select_posterior_equiv posterior_coin_first)
      apply (rule ext)
      by simp
  next
    case (Suc n)
    then show ?case
      apply (simp add: select_posterior_equiv del: Nat.One_nat_def)
      apply (simp only: posterior_coin_first)
      by (simp only: posterior_coin_subsequent)
  qed

lemma can_take_vend: "0 < Suc n \<longrightarrow> Contexts.can_take vend r1_r2_true"
  apply (simp add: can_take_def consistent_def vend_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num 100>" in exI)
  by (simp add: consistent_empty_4)

lemma medial_vend: "medial r1_r2_true (Guard vend) = \<lbrakk>(V (R 1)) \<mapsto> Bc True, (V (R 2)) \<mapsto> (Geq (Num 100))\<rbrakk>"
  apply (simp add: vend_def)
  apply (rule ext)
  by simp

lemma consistent_medial_vend: "consistent \<lbrakk>(V (R 1)) \<mapsto> Bc True, (V (R 2)) \<mapsto> (Geq (Num 100))\<rbrakk>"
  apply (simp add: consistent_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num 100>" in exI)
  apply (simp del: Nat.One_nat_def)
  using consistent_empty_4 by auto

lemma "n > 0 \<longrightarrow> Contexts.can_take vend (posterior_n n coin (posterior empty select))" (* We can do any number of "coin"s before doing a "vend" *)
  proof (induction n)
  case 0
    then show ?case by simp
  next
    case (Suc n)
    then show ?case
      apply (simp del: Nat.One_nat_def)
      apply (simp only: select_posterior posterior_coin_first posterior_n_coin_true_true Contexts.can_take_def)
      by (simp only: medial_vend consistent_medial_vend)
  qed

lemma drinks2_0_invalid: "\<not> (fst a = ''select'' \<and> length (snd a) = 1) \<Longrightarrow>
    (possible_steps drinks2 0 Map.empty (fst a) (snd a)) = {||}"
  apply (simp add: drinks2_def possible_steps_def transitions)
  by force

lemma step_0: "length i = 1 \<Longrightarrow> step drinks2 0 Map.empty ''select'' i = Some (select, 1, [], <R 1 := hd i, R 2 := Num 0>)"
  apply (simp add: step_def possible_steps_0 select_def)
  apply (rule ext)
  apply (simp)
  using hd_input2state by auto

lemma updates_select: "length (snd a) = 1 \<Longrightarrow> (EFSM.apply_updates (Updates select) (case_vname (\<lambda>n. input2state (snd a) 1 (I n)) Map.empty) Map.empty) = <R 1:=hd (snd a), R 2 := Num 0>"
  apply (simp add: select_def)
  apply (rule ext)
  by (simp add: hd_input2state)

lemma drinks2_vend_empty: "possible_steps drinks2 0 Map.empty (''vend'') [] = {||}"
  using drinks2_0_invalid by auto

lemma drinks2_vend_insufficient: "possible_steps drinks2 1 r (''vend'') [] = {|(1, vend_nothing)|}"
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

lemma drinks2_2_coin: "fst a = ''coin'' \<and> length (snd a) = 1 \<Longrightarrow> possible_steps drinks2 2 r (''coin'') (snd a) = {|(2, coin)|}"
  unfolding possible_steps_def
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma updates_coin_2: "(EFSM.apply_updates (Updates coin) (case_vname (\<lambda>n. input2state (snd a) 1 (I n)) (\<lambda>n. if n = 1 then Some s else if R n = R 2 then r2 else None))
             (\<lambda>u. if u = R 1 then Some s else if u = R 2 then r2 else None)) = (\<lambda>u. if u = R 1 then Some s else if u = R 2 then value_plus r2  (input2state (snd a) 1 (I 1)) else None)"
  apply (rule ext)
  by (simp add: coin_def)

lemma drinks2_vend_r2_none: "r (R 2) = None \<Longrightarrow> possible_steps drinks2 2 r (''vend'') [] = {||}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma label_vend_not_coin: "Label b = (''vend'') \<Longrightarrow> b \<noteq> coin"
  using label_coin by auto

lemma drinks2_vend_insufficient2: "\<exists>x1. r (R 2) = Some (Num x1) \<and> x1 < 100 \<Longrightarrow> possible_steps drinks2 2 r (''vend'') [] = {|(2, vend_fail)|}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma updates_vend_fail: "(EFSM.apply_updates (Updates vend_fail) (case_vname Map.empty (\<lambda>n. if n = 1 then Some s else if R n = R 2 then r2 else None))
                   (\<lambda>u. if u = R 1 then Some s else if u = R 2 then r2 else None)) = (\<lambda>u. if u = R 1 then Some s else if u = R 2 then r2 else None)"
  apply (rule ext)
  by (simp add: vend_fail_def)

lemma drinks2_vend_sufficient: "r2 = Some (Num x1) \<Longrightarrow>
                \<not> x1 < 100 \<Longrightarrow>
                possible_steps drinks2 2 (\<lambda>u. if u = R 1 then Some s else if u = R 2 then r2 else None) (''vend'') [] = {|(3, vend)|}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

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

lemma drinks2_vend_r2_String: "r (R 2) = Some (Str x2) \<Longrightarrow>
                possible_steps drinks2 2 r (''vend'') [] = {||}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma drinks2_2_invalid: "fst a = ''coin'' \<longrightarrow> length (snd a) \<noteq> 1 \<Longrightarrow>
          a \<noteq> (''vend'', []) \<Longrightarrow>
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
    apply (case_tac "fst a = ''coin'' \<and> length (snd a) = 1")
    unfolding observe_trace_def
    apply (simp add: step_def)
     apply (simp add: drinks_1_coin coin_updates drinks2_2_coin updates_coin_2)
     apply (simp)

    apply (simp add: step_def)
    apply (case_tac "a = (''vend'', [])")
     apply (case_tac r2)
      apply (simp add: step_def)
    apply (simp add: drinks_vend_r2_none drinks2_vend_r2_none )
     apply (case_tac aa)
      apply (case_tac "x1 < 100")
    apply (simp add: step_def)
    apply (simp add: drinks_vend_insufficient2 drinks2_vend_insufficient2 updates_vend_fail )
    apply (simp add: step_def)
      apply (simp add: drinks_vend_sufficient drinks2_vend_sufficient vend_updates )
    using equal_2_3 observe_trace_def apply auto[1]
     apply (simp add: step_def)
     apply (simp add: drinks_vend_r2_String drinks2_vend_r2_String )
     apply (simp add: step_def)
    by (simp add: drinks_1_invalid drinks2_2_invalid )
qed

lemma drinks2_1_invalid: "fst a = ''coin'' \<longrightarrow> length (snd a) \<noteq> 1 \<Longrightarrow>
    a \<noteq> (''vend'', []) \<Longrightarrow>
    possible_steps drinks2 1 r (fst a) (snd a) = {||}"
  apply (simp add: drinks2_def possible_steps_def transitions)
  apply safe
  apply simp
  apply (metis One_nat_def coin_def label_coin label_vend_nothing length_0_conv n_not_Suc_n numeral_2_eq_2 select_convs(2) surjective_pairing vend_nothing_def)
  apply simp
  by (metis One_nat_def label_vend_nothing length_0_conv nat.inject numeral_2_eq_2 prod.collapse select_convs(2) vend_nothing_def)

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
    apply (case_tac "fst a = ''coin'' \<and> length (snd a) = 1")
     apply (simp add: step_def)
     apply (simp only: drinks_1_coin possible_steps_1)
     apply (simp add: )
    apply (simp only: coin_updates_equiv)
    using equal_1_2 observe_trace_def
    apply simp
    apply (case_tac "a = (''vend'', [])")
      apply (simp)
      apply (simp add: step_def drinks_vend_insufficient drinks2_vend_insufficient)
     apply (simp add: outputs_vend_fail outputs_vend_nothing )
     apply (simp add: apply_updates_vend_fail apply_updates_vend_nothing)
    apply (simp add: step_def)
    by (simp add: drinks_1_invalid drinks2_1_invalid step_def )
qed

lemma observational_equivalence: "efsm_equiv drinks drinks2 t" (* Corresponds to Example 3 in Foster et. al. *)
proof (induct t)
  case Nil
    then show ?case by (simp add: efsm_equiv_def observe_trace_def)
  next
  case (Cons a t)
  then show ?case
    apply (simp only: efsm_equiv_def observe_trace_def)
    apply (case_tac "fst a = ''select'' \<and> length (snd a) = 1")
     prefer 2
     apply (simp add: drinks2_0_invalid drinks_0_invalid is_singleton_def step_def )
    apply (simp)
    apply (simp add: possible_steps_0 Drinks_Machine.possible_steps_0 updates_select step_def)
    apply (case_tac t)
     apply simp
    using equal_1_1
    by (metis observe_trace_def)
qed

lemma "fset (Abs_fset s) = s"
proof (induct "Abs_fset s")
  case empty
  then show ?case
    apply simp
    sorry
next
  case (insert x1 x2)
  then show ?case
    sorry
qed

lemma "simulates_with drinks2 drinks (\<lambda>x. if x = 0 then 0 else if x = 1 then 1 else if x = 2 then 1 else if x = 3 then 2 else x)"
proof-
  have set_filter: "\<forall>s t l i r. ((s, 0), t) \<notin> (Set.filter
          (\<lambda>((origin, dest), t).
              origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))))
          (fset drinks2))"
    by (simp add: Set.filter_def drinks2_def)
  have test: "\<forall>s t i l r.((s, 0), t) |\<notin>| ffilter
        (\<lambda>((origin, dest), t).
            origin = s \<and>
            Label t = l \<and> length i = Arity t \<and> apply_guards (Guard t) (\<lambda>x. case x of I n \<Rightarrow> input2state i 1 (I n) | R n \<Rightarrow> r (R n))) drinks2"
    apply (simp add: ffilter_def)
    sorry
  have "\<forall>s t r l i. (0, t) |\<notin>| possible_steps drinks2 s r l i"
    apply clarify
    apply (simp add: possible_steps_def)
    using test
    by auto
qed
    



  show ?thesis
    apply (simp add: simulates_with_def)
    apply safe
    apply simp_all
                        apply (simp add: drinks2_end)
                        apply (simp add: drinks2_end drinks_end)
                        apply (simp add: drinks2_end drinks_end)
                        apply (simp add: drinks2_end drinks_end)
                        apply (simp add: drinks2_end drinks_end)
                       apply (case_tac "l = ''coin'' \<and> length i = 1")
                        apply (simp add: possible_steps_2_coin)
                       apply (case_tac "l = ''vend'' \<and> i = []")
                        apply (case_tac "r (R 2)")
                        apply (simp add: drinks2_vend_r2_none)
                        apply simp
                        apply (case_tac a)
                        prefer 2
                        apply (simp add: drinks2_vend_r2_String)
                        apply (case_tac "x1 \<ge> 100")
                        apply (simp add: possible_steps_2_vend Drinks_Machine.possible_steps_2_vend)
                        apply (simp add: drinks2_vend_insufficient2)
                       apply simp
    using drinks2_2_invalid
                       apply auto[1]
                      apply (case_tac "l = ''coin'' \<and> length i = 1")
                       apply (simp add: possible_steps_2_coin possible_steps_1_coin)
                      apply simp
                       apply (case_tac "l = ''vend'' \<and> i = []")
                        apply (case_tac "r (R 2)")
                        apply (simp add: drinks2_vend_r2_none)
                       apply simp
                       apply (case_tac a)
                        prefer 2
                        apply (simp add: drinks2_vend_r2_String)
                       apply (case_tac "x1 \<ge> 100")
                        apply simp
                        apply (simp add: possible_steps_2_vend)
                       apply (simp add: drinks_vend_insufficient)
                      apply simp
    using drinks2_2_invalid
                      apply auto[1]
                     apply (case_tac "l = ''coin'' \<and> length i = 1")
                      apply (simp add: Drinks_Machine.possible_steps_1_coin)
                     apply simp
                     apply (case_tac "l = ''vend'' \<and> i = []")
                      apply simp
                      apply (case_tac "r (R 2)")
                       apply (simp add: drinks2_vend_r2_none)
                       apply (case_tac a)
                        prefer 2
                        apply (simp add: drinks2_vend_r2_String)
                       apply (case_tac "x1 \<ge> 100")
                        apply (simp add: possible_steps_2_vend)
                      apply (simp add: drinks_vend_insufficient)
    using drinks2_2_invalid
                     apply auto[1]





   








    


end
