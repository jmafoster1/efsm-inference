subsection{*An Observationally Equivalent Model*}
text{*This theory defines a second formalisation of the drinks machine example which produces
identical output to the first model. This property is called \emph{observational equivalence} and is
discussed in more detail in \cite{foster2018}.*}
theory Drinks_Machine_2
  imports Drinks_Machine "../Contexts"
begin

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

lemmas transitions = select_def coin_def vend_def vend_fail_def vend_nothing_def connectives relations

lemma outputs_vend_nothing: "Outputs vend_nothing = []"
  by (simp add: vend_nothing_def)

lemma label_vend_nothing: "Label vend_nothing = ''vend''"
  by (simp add: vend_nothing_def)

definition drinks2 :: "statename efsm" where
"drinks2 \<equiv> \<lparr>
          s0 = q0,
          T = \<lambda> (a,b) .
              if (a,b) = (q0,q1) then {|select|}
              else if (a,b) = (q1,q1) then {|vend_nothing|}
              else if (a,b) = (q1,q2) then {|coin|}
              else if (a,b) = (q2,q2) then {|coin, vend_fail|}
              else if (a,b) = (q2,q3) then {|vend|}
              else {||}
         \<rparr>"

lemma s0_drinks2 [simp]: "s0 drinks2 = q0"
  by (simp add: drinks2_def)

lemma empty_not_singleton [simp]: "\<not> is_singleton {}"
  by (simp add: is_singleton_def)

lemma possible_steps_q0:  "length i = Suc 0 \<Longrightarrow> possible_steps drinks2 q0 Map.empty (''select'') i = {(q1, select)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (case_tac a)
          apply (simp add: drinks2_def)
         apply (simp add: drinks2_def)
        apply (simp add: drinks2_def)
       apply (simp add: drinks2_def)
      apply (case_tac a)
  by (simp_all add: drinks2_def select_def)

lemma possible_steps_q1: "length i = 1 \<Longrightarrow> possible_steps drinks2 q1 r (''coin'') i = {(q2, coin)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (case_tac a)
          apply (simp add: drinks2_def)
          apply (simp add: drinks2_def label_vend_nothing)
          apply (simp add: drinks2_def)
          apply (simp add: drinks2_def)
       apply (case_tac a)
          apply (simp add: drinks2_def)
        apply (simp add: drinks2_def)
       apply (case_tac "b = coin")
        apply (simp add: drinks2_def)
       apply (simp add: drinks2_def)
       apply (metis One_nat_def one_neq_zero transition.select_convs(2) vend_nothing_def)
  by (simp_all add: drinks2_def coin_def)

lemma possible_steps_q2_coin: "possible_steps drinks2 q2 r (''coin'') [Num 50] = {(q2, coin)}"
  apply (simp add: possible_steps_def)
  apply safe
  apply (case_tac a)
        apply (simp add: drinks2_def)
        apply (simp add: drinks2_def)
        apply (simp add: drinks2_def)
       apply (simp add: drinks2_def)
  using arity_vend apply linarith
      apply (case_tac a)
        apply (simp add: drinks2_def)
        apply (simp add: drinks2_def)
        apply (simp add: drinks2_def)
  using arity_vend_fail apply presburger
      apply (simp add: drinks2_def)
      apply (simp add: arity_vend)
  by (simp_all add: coin_def drinks2_def)

lemma possible_steps_q2_vend: "possible_steps drinks2 q2 <R (Suc 0) := Str ''coke'', R 2 := Num 100> (''vend'') [] = {(q3, vend)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (case_tac a)
          apply (simp add: drinks2_def)
          apply (simp add: drinks2_def)
        apply (case_tac "b = coin")
         apply (simp add: drinks2_def transitions(2))
        apply (simp add: drinks2_def vend_fail_def Lt_def)
          apply (simp add: drinks2_def)
       apply (case_tac a)
          apply (simp add: drinks2_def)
          apply (simp add: drinks2_def)
        apply (case_tac "b = coin")
        apply (simp add: drinks2_def coin_def vend_def)
          apply (simp add: drinks2_def vend_fail_def)
  by (simp_all add: drinks2_def vend_def Lt_def Ge_def gNot_def)

lemma purchase_coke: "observe_trace drinks2 (s0 drinks2) <> [(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 50]), (''vend'', [])] = [[], [Num 50], [Num 100], [Str ''coke'']]"
  apply (simp add: possible_steps_q0 s0_drinks2)
  apply (simp add: possible_steps_q1)
  apply (simp add: possible_steps_q2_coin)
  by (simp add: possible_steps_q2_vend vend_def coin_def)

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

lemma foo: "\<not> (x \<noteq> V (R 1) \<and> x \<noteq> V (R 2) \<and> (x = V (R 1) \<or> x = V (R 2)))"
  by auto

lemma consistent_medial_coin: "consistent \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk>"
  apply (simp add: consistent_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num 0>" in exI)
  apply (simp del: Nat.One_nat_def)
  using consistent_empty_4 by auto

lemma posterior_coin_first: "posterior select_posterior coin = \<lbrakk>(V (R 1)) \<mapsto> Bc True, (V (R 2)) \<mapsto> Bc True\<rbrakk>"
  apply (simp add: posterior_def consistent_medial_coin del: Nat.One_nat_def)
  apply (simp add: coin_def valid_def satisfiable_def)
  apply (rule ext)
  by simp

lemma consistent_medial_coin_2: "consistent \<lbrakk>V (R (Suc 0)) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Bc True\<rbrakk>"
  apply (simp add: consistent_def)
  apply (rule_tac x="<>" in exI)
  apply (simp del: Nat.One_nat_def)
  using consistent_empty_4 by auto

lemma posterior_coin_subsequent: "posterior \<lbrakk>V (R (Suc 0)) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Bc True\<rbrakk> coin = \<lbrakk>V (R (Suc 0)) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Bc True\<rbrakk>"
  apply (simp add: posterior_def consistent_medial_coin_2)
  apply (simp add: coin_def valid_def satisfiable_def)
  apply (rule ext)
  by simp

lemma value_lt_aval: "aval x r = Some a \<Longrightarrow> aval y r = Some aa \<Longrightarrow> ValueLt (Some a) (Some aa) = Some ab \<Longrightarrow> \<exists>n n'. a = Num n \<and> aa = Num n'"
  by (metis MaybeBoolInt.elims option.distinct(1) option.sel)

lemma ge_equiv: "gval (Ge x y) r = gval (gOr (gexp.Gt x y) (gexp.Eq x y)) r"
  apply (simp add: connectives relations)
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
  by (simp add: connectives relations)

lemma apply_gt_100_eq_100: "(apply_guard \<lbrakk>V (R 1) \<mapsto> cexp.Bc True\<rbrakk> (gOr (GExp.Lt (L (Num 100)) (V (R 1))) (gexp.Eq (V (R 1)) (L (Num 100))))) = \<lbrakk>V (R 1) \<mapsto> cexp.Not (And (Neq (Num 100)) (Leq (Num 100)))\<rbrakk>"
  apply (rule ext)
  by (simp add: connectives relations)

lemma "cexp_equiv (cexp.Not (And (Neq (Num 100)) (Leq (Num 100)))) (Geq (Num 100))"
  apply (simp add: cexp_equiv_def)
  apply (rule allI)
  apply (case_tac i)
   apply auto[1]
  by simp

lemma "context_equiv (apply_guard \<lbrakk>(V (R 1)) \<mapsto> Bc True\<rbrakk> (Ge (V (R 1)) (L (Num 100))))
                      (apply_guard \<lbrakk>(V (R 1)) \<mapsto> Bc True\<rbrakk> (gOr (gexp.Gt (V (R 1)) (L (Num 100))) (gexp.Eq (V (R 1)) (L (Num 100)))))"
  apply (simp only: apply_guard_ge_100 apply_gt_100_eq_100 connectives relations)
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
  apply (simp add: GExp.satisfiable_def connectives relations)
  apply (rule allI)
  apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some (Num 100)) (s (R 2))")
   apply simp
  apply simp
  apply (case_tac "s (R 2) = Some (Num 0)")
   apply simp
  by simp

lemma consistent_select_posterior: "consistent select_posterior"
  apply (simp add: consistent_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num 0>" in exI)
  apply (simp del: Nat.One_nat_def)
  apply (rule allI)
  apply (case_tac r)
     prefer 2
     apply (case_tac x2)
  by simp_all

lemma can_take_coin: "consistent c \<longrightarrow> Contexts.can_take coin c"
  by (simp add: coin_def consistent_def Contexts.can_take_def)

abbreviation r1_r2_true :: "context" where
"r1_r2_true \<equiv> \<lbrakk>(V (R 1)) \<mapsto> Bc True, (V (R 2)) \<mapsto> Bc True\<rbrakk>"

lemma consistent_r1_r2_true: "consistent r1_r2_true"
  apply (simp add: consistent_def)
  apply (rule_tac x="<>" in exI)
  apply (simp del: Nat.One_nat_def)
  using consistent_empty_1 by force

lemma posterior_r1_r2_true_coin: "(posterior r1_r2_true coin) = r1_r2_true"
  apply (simp add: posterior_def coin_def consistent_def satisfiable_def valid_def)
  apply safe
   apply auto[1]
  using consistent_empty_1 by force

lemma coin_empty: "(posterior r1_r2_true coin) = r1_r2_true"
  apply (rule ext)
  apply (simp add: posterior_def coin_def satisfiable_def consistent_def)
  using empty_not_undef by force

lemma valid_coin_empty: "valid_context (posterior r1_r2_true coin)"
  apply (simp add: posterior_r1_r2_true_coin)
  apply (simp add: valid_context_def)
  apply (simp add: posterior_coin_subsequent)
  by (simp add: consistent_empty_4)

lemma valid_true: "valid c \<longrightarrow> cexp_equiv c (Bc True)"
  apply (simp add: valid_def cexp_equiv_def)
  by auto

lemma consistent_medial_coin_3: "consistent (\<lambda>a. if a = V (R 2) then cexp.Eq (Num 0) else if a = V (R 1) then cexp.Bc True else \<lbrakk>\<rbrakk> a)"
  apply (simp add: consistent_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num 0>" in exI)
  apply (simp del: Nat.One_nat_def)
  by (simp add: consistent_empty_4)

lemma posterior_coin_true: "(posterior (\<lambda>a. if a = V (R 2) then cexp.Eq (Num 0) else if a = V (R 1) then cexp.Bc True else \<lbrakk>\<rbrakk> a) coin) = r1_r2_true"
  apply (simp add: posterior_def)
  apply (simp add: consistent_medial_coin_3)
  apply (simp add: coin_def valid_def satisfiable_def)
  apply (rule ext)
  by simp

lemma r1_r2_true_equiv: "(\<lambda>a. if a = V (R 2) then cexp.Bc True else if a = V (R 1) then cexp.Bc True else \<lbrakk>\<rbrakk> a) = r1_r2_true"
  apply (rule ext)
  by simp

lemma r2_0_r1_true_equiv: "(\<lambda>a. if a = V (R 2) then cexp.Eq (Num 0) else if a = V (R 1) then cexp.Bc True else \<lbrakk>\<rbrakk> a) = select_posterior"
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
      using posterior_r1_r2_true_coin by auto
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
      apply (simp add: r2_0_r1_true_equiv del: Nat.One_nat_def)
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
      apply (simp only: r2_0_r1_true_equiv posterior_coin_first)
      apply (rule ext)
      by simp
  next
    case (Suc n)
    then show ?case
      apply (simp del: Nat.One_nat_def)
      apply (simp only: r2_0_r1_true_equiv posterior_coin_first)
      apply (simp only: r1_r2_true_equiv)
      apply (simp add: posterior_coin_subsequent)
      apply (rule ext)
      by simp
  qed

lemma can_take_vend: "0 < Suc n \<longrightarrow> Contexts.can_take vend r1_r2_true"
  apply (simp add: can_take_def consistent_def vend_def connectives relations)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num 100>" in exI)
  by (simp add: consistent_empty_4)

lemma medial_vend: "medial r1_r2_true (Guard vend) = \<lbrakk>(V (R 1)) \<mapsto> Bc True, (V (R 2)) \<mapsto> (Geq (Num 100))\<rbrakk>"
  apply (simp add: vend_def connectives relations)
  apply (rule ext)
  by simp

lemma consistent_medial_vend: "consistent \<lbrakk>(V (R 1)) \<mapsto> Bc True, (V (R 2)) \<mapsto> (Geq (Num 100))\<rbrakk>"
  apply (simp add: consistent_def connectives relations)
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

lemma drinks_q0_invalid: "\<not> (fst a = ''select'' \<and> length (snd a) = 1) \<Longrightarrow>
    (possible_steps drinks q0 Map.empty (fst a) (snd a)) = {}"
  apply (simp add: possible_steps_def)
  apply (rule allI)
  apply (rule allI)
  apply (case_tac aa)
     apply (simp add: drinks_def)
    apply (simp add: drinks_def)
  apply (metis One_nat_def transition.simps(1) transition.simps(2) transitions(1))
   apply (simp add: drinks_def)
  by (simp add: drinks_def)

lemma drinks2_q0_invalid: "\<not> (fst a = ''select'' \<and> length (snd a) = 1) \<Longrightarrow>
    (possible_steps drinks2 q0 Map.empty (fst a) (snd a)) = {}"
  apply (simp add: possible_steps_def)
  apply (rule allI)
  apply (rule allI)
  apply (case_tac aa)
     apply (simp add: drinks2_def)
     apply (simp add: drinks2_def)
    apply (metis One_nat_def transition.simps(1) transition.simps(2) transitions(1))
     apply (simp add: drinks2_def)
  by (simp add: drinks2_def)

lemma updates_select: "length (snd a) = 1 \<Longrightarrow> (EFSM.apply_updates (Updates select) (case_vname (\<lambda>n. input2state (snd a) (Suc 0) (I n)) Map.empty) Map.empty) = <R 1:=hd (snd a), R 2 := Num 0>"
  apply (simp add: select_def)
  apply (rule ext)
  apply (simp add: hd_input2state)
  by (metis One_nat_def hd_input2state le_numeral_extra(4))

lemma drinks_vend_empty: "(possible_steps drinks q0 Map.empty (''vend'') []) = {}"
  apply (simp add: possible_steps_def)
  apply (rule allI)
  apply (rule allI)
  apply (case_tac a)
  by (simp_all add: drinks_def select_def)

lemma drinks2_vend_empty: "possible_steps drinks2 q0 Map.empty (''vend'') [] = {}"
  apply (simp add: possible_steps_def)
  apply (rule allI)
  apply (rule allI)
  apply (case_tac a)
  by (simp_all add: drinks2_def select_def)

lemma drinks_vend_insufficient: "n < 100 \<Longrightarrow>
    (possible_steps drinks q1 (\<lambda>a. if a = R 2 then Some (Num n) else if a = R (Suc 0) then Some s else None) (''vend'') []) = {(q1, vend_fail)}"
  apply (simp add: possible_steps_def)
  apply safe
  apply (case_tac a)
          apply (simp add: drinks_def)
         apply (simp add: drinks_def)
        apply (simp add: drinks_def vend_def connectives relations)
       apply (simp add: drinks_def)
      apply (case_tac a)
         apply (simp add: drinks_def)
        apply (case_tac "b=coin")
         apply (simp add: drinks_def coin_def)
        apply (simp add: drinks_def)
       apply (simp add: drinks_def vend_def)
  by (simp_all add: drinks_def vend_fail_def connectives relations)

lemma drinks2_vend_insufficient: "possible_steps drinks2 q1 r (''vend'') [] = {(q1, vend_nothing)}"
  apply (simp add: possible_steps_def)
  apply safe
  apply (case_tac a)
          apply (simp add: drinks2_def)
         apply (simp add: drinks2_def)
        apply (case_tac "b=coin")
         apply (simp add: drinks2_def coin_def)
        apply (simp add: drinks2_def)
       apply (simp add: drinks2_def)
      apply (case_tac a)
         apply (simp add: drinks2_def)
        apply (simp add: drinks2_def)
       apply (case_tac "b=coin")
        apply (simp add: drinks2_def coin_def)
       apply (simp add: drinks2_def)
  by (simp_all add: drinks2_def vend_nothing_def)

lemma apply_updates_vend_fail: "(EFSM.apply_updates (Updates vend_fail) (case_vname Map.empty (\<lambda>na. if na = 2 then Some (Num n) else if R na = R (Suc 0) then Some s else None))
       (\<lambda>a. if a = R 2 then Some (Num n) else if a = R (Suc 0) then Some s else None)) = <R (Suc 0) := s, R 2 := Num n>"
  apply (rule ext)
  by (simp add: vend_fail_def)

lemma apply_updates_vend_nothing: "(EFSM.apply_updates (Updates vend_nothing) (case_vname Map.empty (\<lambda>na. if na = 2 then Some (Num n) else if R na = R (Suc 0) then Some s else None))
       (\<lambda>a. if a = R 2 then Some (Num n) else if a = R (Suc 0) then Some s else None)) = <R (Suc 0) := s, R 2 := Num n>"
  apply (rule ext)
  by (simp add: vend_nothing_def)

lemma drinks_q1_coin: "length (snd a) = Suc 0 \<Longrightarrow> possible_steps drinks q1 r (''coin'') (snd a) = {(q1, coin)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (case_tac aa)
          apply (simp add: drinks_def)
         apply (simp add: drinks_def)
        apply (simp add: drinks_def label_vend)
       apply (simp add: drinks_def)
      apply (case_tac aa)
         apply (simp add: drinks_def)
        apply (case_tac "b=coin")
         apply (simp add: drinks_def)
        apply (simp add: drinks_def label_vend_fail)
       apply (simp add: drinks_def label_vend)
  by (simp_all add: drinks_def coin_def)

lemma drinks2_q1_coin: "length (snd a) = Suc 0 \<Longrightarrow> (possible_steps drinks2 q1 r (''coin'') (snd a)) = {(q2, coin)}"
  apply (simp add: possible_steps_def)
  apply safe
  apply (case_tac aa)
  apply (simp add: drinks2_def)
    apply (simp add: drinks2_def label_vend_nothing)
        apply (simp add: drinks2_def)
       apply (simp add: drinks2_def)
      apply (case_tac aa)
         apply (simp add: drinks2_def)
        apply (simp add: drinks2_def label_vend_nothing)
       apply (simp add: drinks2_def)
  by (simp_all add: drinks2_def coin_def)

lemma coin_updates: "(EFSM.apply_updates (Updates coin) (case_vname (\<lambda>n. input2state (snd a) (Suc 0) (I n)) (\<lambda>n. if n = 2 then Some (Num 0) else if R n = R (Suc 0) then Some s else None))
       (\<lambda>a. if a = R 2 then Some (Num 0) else if a = R (Suc 0) then Some s else None)) = (\<lambda>u. if u = R 1 then Some s else if u = R 2 then value_plus (Some (Num 0)) (input2state (snd a) 1 (I 1)) else None)"
  apply (rule ext)
  by (simp add: coin_def)

lemma drinks2_q2_coin: "fst a = ''coin'' \<and> length (snd a) = Suc 0 \<Longrightarrow> possible_steps drinks2 q2 r (''coin'') (snd a) = {(q2, coin)}"
  apply (simp add: possible_steps_def)
  apply safe
  apply (case_tac aa)
          apply (simp add: drinks2_def)
         apply (simp add: drinks2_def)
        apply (simp add: drinks2_def)
       apply (simp add: drinks2_def label_vend)
      apply (case_tac aa)
         apply (simp add: drinks2_def)
        apply (simp add: drinks2_def)
       apply (case_tac "b=coin")
        apply (simp add: drinks2_def)
       apply (simp add: drinks2_def label_vend_fail)
      apply (simp add: drinks2_def label_vend)
  by (simp_all add: drinks2_def coin_def)

lemma updates_coin_2: "(EFSM.apply_updates (Updates coin) (case_vname (\<lambda>n. input2state (snd a) (Suc 0) (I n)) (\<lambda>n. if n = Suc 0 then Some s else if R n = R 2 then r2 else None))
             (\<lambda>u. if u = R (Suc 0) then Some s else if u = R 2 then r2 else None)) = (\<lambda>u. if u = R 1 then Some s else if u = R 2 then value_plus r2  (input2state (snd a) 1 (I 1)) else None)"
  apply (rule ext)
  by (simp add: coin_def)

lemma drinks_vend_r2_none: "r2 = None \<Longrightarrow> possible_steps drinks q1 (\<lambda>u. if u = R (Suc 0) then Some s else if u = R 2 then r2 else None) (''vend'') [] = {}"
  apply (simp add: possible_steps_def)
  apply (rule allI)
  apply (rule allI)
  apply (case_tac a)
     apply (simp add: drinks_def)
    apply (simp add: drinks_def vend_fail_def label_coin connectives relations)
   apply (simp add: drinks_def vend_def connectives relations)
  by (simp add: drinks_def)

lemma drinks2_vend_r2_none: "r2 = None \<Longrightarrow> possible_steps drinks2 q2 (\<lambda>u. if u = R (Suc 0) then Some s else if u = R 2 then r2 else None) (''vend'') [] = {}"
  apply (simp add: possible_steps_def)
  apply (rule allI)
  apply (rule allI)
  apply (case_tac a)
     apply (simp add: drinks2_def)
    apply (simp add: drinks2_def)
   apply (simp add: drinks2_def vend_fail_def coin_def connectives relations)
  by (simp add: drinks2_def vend_def connectives relations)

lemma label_vend_not_coin: "Label b = (''vend'') \<Longrightarrow> b \<noteq> coin"
  using label_coin by auto

lemma drinks_vend_insufficient2: "r2 = Some (Num x1) \<Longrightarrow>
                x1 < 100 \<Longrightarrow>
                possible_steps drinks q1 (\<lambda>u. if u = R (Suc 0) then Some s else if u = R 2 then r2 else None) (''vend'') [] = {(q1, vend_fail)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (simp add: drinks_def)
       apply (case_tac a)
          apply simp
         apply (simp add: label_vend_not_coin vend_fail_def connectives relations)
        apply (simp add: drinks_def vend_def connectives relations)
       apply (simp add: drinks_def)
      apply (case_tac a)
         apply (simp add: drinks_def)
        apply (simp add: drinks_def label_vend_not_coin)
  by (simp_all add: drinks_def vend_fail_def vend_def connectives relations)

lemma drinks2_vend_insufficient2: "r2 = Some (Num x1) \<Longrightarrow>
                x1 < 100 \<Longrightarrow>
                possible_steps drinks2 q2 (\<lambda>u. if u = R (Suc 0) then Some s else if u = R 2 then r2 else None) (''vend'') [] = {(q2, vend_fail)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (case_tac a)
          apply (simp add: drinks2_def)
         apply (simp add: drinks2_def)
        apply (simp add: drinks2_def)
       apply (simp add: drinks2_def vend_def connectives relations)
      apply (case_tac a)
         apply (simp add: drinks2_def)
        apply (simp add: drinks2_def)
       apply (simp add: drinks2_def label_vend_not_coin relations connectives)
  by (simp_all add: drinks2_def vend_def vend_fail_def connectives relations)

lemma updates_vend_fail: "(EFSM.apply_updates (Updates vend_fail) (case_vname Map.empty (\<lambda>n. if n = Suc 0 then Some s else if R n = R 2 then r2 else None))
                   (\<lambda>u. if u = R (Suc 0) then Some s else if u = R 2 then r2 else None)) = (\<lambda>u. if u = R (Suc 0) then Some s else if u = R 2 then r2 else None)"
  apply (rule ext)
  by (simp add: vend_fail_def)

lemma drinks_vend_sufficient: "r2 = Some (Num x1) \<Longrightarrow>
                \<not> x1 < 100 \<Longrightarrow>
                (possible_steps drinks q1 (\<lambda>u. if u = R (Suc 0) then Some s else if u = R 2 then r2 else None) (''vend'') []) = {(q2, vend)}"
  apply (simp add: possible_steps_def)
  apply safe
  apply (case_tac a)
          apply (simp add: drinks_def)
         apply (simp add: drinks_def label_vend_not_coin vend_fail_def connectives relations)
        apply (simp add: drinks_def)
       apply (simp add: drinks_def)
      apply (case_tac a)
         apply (simp add: drinks_def)
        apply (simp add: drinks_def label_vend_not_coin vend_fail_def connectives relations)
  by (simp_all add: drinks_def vend_def connectives relations)

lemma drinks2_vend_sufficient: "r2 = Some (Num x1) \<Longrightarrow>
                \<not> x1 < 100 \<Longrightarrow>
                possible_steps drinks2 q2 (\<lambda>u. if u = R (Suc 0) then Some s else if u = R 2 then r2 else None) (''vend'') [] = {(q3, vend)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (case_tac a)
          apply (simp add: drinks2_def)
         apply (simp add: drinks2_def)
        apply (simp add: drinks2_def label_vend_not_coin vend_fail_def connectives relations)
       apply (simp add: drinks2_def)
      apply (case_tac a)
         apply (simp add: drinks2_def)
        apply (simp add: drinks2_def)
       apply (simp add: drinks2_def label_vend_not_coin vend_fail_def connectives relations)
  by (simp_all add: drinks2_def vend_def connectives relations)

lemma vend_updates: "(EFSM.apply_updates (Updates vend) (case_vname Map.empty (\<lambda>n. if n = Suc 0 then Some s else if R n = R 2 then r2 else None))
                   (\<lambda>u. if u = R (Suc 0) then Some s else if u = R 2 then r2 else None)) = (\<lambda>u. if u = R (Suc 0) then Some s else if u = R 2 then r2 else None)"
  apply (rule ext)
  by (simp add: vend_def)

lemma drinks_end: "possible_steps drinks q2 r (fst a) (snd a) = {}"
  apply (simp add: possible_steps_def)
  apply (rule allI)
  apply (rule allI)
  by (simp add: drinks_def)

lemma drinks2_end: "possible_steps drinks2 q3 r (fst a) (snd a) = {}"
  apply (simp add: possible_steps_def)
  apply (rule allI)
  apply (rule allI)
  by (simp add: drinks2_def)

lemma equal_q2_q3: "observe_trace drinks q2 r t = observe_trace drinks2 q3 r t"
proof (induction t)
  case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case
    by (simp add: drinks_end drinks2_end)
qed

lemma drinks_vend_r2_String: "r2 = Some (Str x2) \<Longrightarrow> possible_steps drinks q1 (\<lambda>u. if u = R (Suc 0) then Some s else if u = R 2 then r2 else None) (''vend'') [] = {}"
  apply (simp add: possible_steps_def)
  apply (rule allI)
  apply (rule allI)
  apply (case_tac a)
     apply (simp add: drinks_def)
    apply (simp add: drinks_def coin_def vend_fail_def connectives relations)
   apply (simp add: drinks_def vend_def connectives relations)
  by (simp add: drinks_def)

lemma drinks2_vend_r2_String: "r2 = Some (Str x2) \<Longrightarrow>
                possible_steps drinks2 q2 (\<lambda>u. if u = R (Suc 0) then Some s else if u = R 2 then r2 else None) (''vend'') [] = {}"
  apply (simp add: possible_steps_def)
  apply (rule allI)
  apply (rule allI)
  apply (case_tac a)
     apply (simp add: drinks2_def)
    apply (simp add: drinks2_def)
   apply (simp add: drinks2_def vend_fail_def coin_def connectives relations)
  by (simp add: drinks2_def vend_def connectives relations)

lemma drinks_q1_invalid: "fst a = ''coin'' \<longrightarrow> length (snd a) \<noteq> Suc 0 \<Longrightarrow>
          a \<noteq> (''vend'', []) \<Longrightarrow>
          possible_steps drinks q1 r (fst a) (snd a) = {}"
  apply (simp add: possible_steps_def)
  apply (rule allI)
  apply (rule allI)
  apply (case_tac aa)
     apply (simp add: drinks_def)
    apply (simp add: drinks_def label_coin label_vend_fail)
    apply (metis (no_types, lifting) One_nat_def arity_vend_fail length_0_conv prod.collapse transition.simps(2) transitions(2))
   apply (simp add: drinks_def)
   apply (metis arity_vend label_vend length_0_conv prod.collapse)
  by (simp add: drinks_def)

lemma drinks2_q2_invalid: "fst a = ''coin'' \<longrightarrow> length (snd a) \<noteq> Suc 0 \<Longrightarrow>
          a \<noteq> (''vend'', []) \<Longrightarrow>
          possible_steps drinks2 q2 r (fst a) (snd a) = {}"
  apply (simp add: possible_steps_def)
  apply (rule allI)
  apply (rule allI)
  apply (case_tac aa)
     apply (simp add: drinks2_def)
    apply (simp add: drinks2_def)
   apply (simp add: drinks2_def)
  apply (metis One_nat_def arity_vend_fail label_coin label_vend_fail length_0_conv prod.collapse transition.simps(2) transitions(2))
  apply (simp add: drinks2_def)
  by (metis arity_vend label_vend length_0_conv prod.collapse)

lemma equal_q1_q2: "\<forall>r2. observe_trace drinks q1 (\<lambda>u. if u = R (Suc 0) then Some s else if u = R 2 then r2 else None) t =
    observe_trace drinks2 q2 (\<lambda>u. if u = R (Suc 0) then Some s else if u = R 2 then r2 else None) t"
proof (induction t)
  case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case
    apply (case_tac "fst a = ''coin'' \<and> length (snd a) = 1")
     apply (rule allI)
     apply (simp add: drinks_q1_coin coin_updates drinks2_q2_coin updates_coin_2)
    apply (rule allI)
    apply (case_tac "a = (''vend'', [])")
     apply (case_tac r2)
      apply simp
    apply (simp add: drinks_vend_r2_none drinks2_vend_r2_none)
     apply (case_tac aa)
      apply (case_tac "x1 < 100")
    apply simp
    apply (simp add: drinks_vend_insufficient2 drinks2_vend_insufficient2 updates_vend_fail)
      apply simp
      apply (simp add: drinks_vend_sufficient drinks2_vend_sufficient vend_updates)
    using equal_q2_q3 apply blast
     apply (simp add: drinks_vend_r2_String drinks2_vend_r2_String)
    by (simp add: drinks_q1_invalid drinks2_q2_invalid)
qed

lemma drinks2_q1_invalid: "fst a = ''coin'' \<longrightarrow> length (snd a) \<noteq> Suc 0 \<Longrightarrow>
    a \<noteq> (''vend'', []) \<Longrightarrow>
    possible_steps drinks2 q1 r (fst a) (snd a) = {}"
  apply (simp add: possible_steps_def)
  apply (rule allI)
  apply (rule allI)
  apply (simp add: drinks2_def)
  apply (case_tac aa)
     apply simp
    apply (metis (no_types, lifting) label_vend_nothing length_0_conv prod.collapse statename.distinct(7) transition.simps(2) vend_nothing_def)
   apply (metis One_nat_def label_coin transition.simps(2) transitions(2))
  by simp

lemma equal_q1_q1: "observe_trace drinks q1 <R (Suc 0) := s, R 2 := Num 0> t = observe_trace drinks2 q1 <R (Suc 0) := s, R 2 := Num 0> t"
proof (induction t)
  case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case
    apply (case_tac "fst a = ''coin'' \<and> length (snd a) = 1")
     apply simp
     apply (simp add: drinks_q1_coin drinks2_q1_coin coin_updates)
    using equal_q1_q2 apply blast
    apply (case_tac "a = (''vend'', [])")
      apply simp
      apply (simp add: drinks_vend_insufficient drinks2_vend_insufficient)
      apply (simp add: outputs_vend_fail outputs_vend_nothing)
      apply (simp add: apply_updates_vend_fail apply_updates_vend_nothing)
    using Cons.IH apply blast
    apply simp
    by (simp add: drinks_q1_invalid drinks2_q1_invalid)
qed

lemma observational_equivalence: "efsm_equiv drinks drinks2 t" (* Corresponds to Example 3 in Foster et. al. *)
proof (induct t)
  case Nil
    then show ?case by (simp add: efsm_equiv_def)
  next
  case (Cons a t)
  then show ?case
    apply (simp only: efsm_equiv_def s0_drinks2)
    apply (case_tac "fst a = ''select'' \<and> length (snd a) = 1")
     prefer 2
     apply (simp add: drinks2_q0_invalid drinks_q0_invalid is_singleton_def)
    apply simp
    apply (simp add: possible_steps_q0 Drinks_Machine.possible_steps_q0 updates_select)
    apply (case_tac t)
     apply simp
    using equal_q1_q1 by blast
  qed

end
