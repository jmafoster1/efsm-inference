section{*Examples*}
subsection{*Drinks Machine*}
text{*This theory formalises a simple drinks machine. The \emph{select} operation takes one
argument - the desired beverage. The \emph{coin} operation also takes one parameter representing
the value of the coin. The \emph{vend} operation has two flavours - one which dispenses the drink if
the customer has inserted enough money, and one which dispenses nothing if the user has not inserted
sufficient funds.

We first define a datatype \emph{statemane} which corresponds to $S$ in the formal definition.
Note that, while statename has four elements, the drinks machine presented here only requires three
states. The fourth element is included here so that the \emph{statename} datatype may be used in
the next example.
*}
theory Drinks_Machine
  imports "../Contexts"
begin

definition select :: "transition" where
"select \<equiv> \<lparr>
        Label = ''select'',
        Arity = 1,
        Guard = [], \<comment> \<open> No guards \<close>
        Outputs = [],
        Updates = [ \<comment> \<open> Two updates: \<close>
                    (R 1, (V (I 1))), \<comment> \<open>  Firstly set value of r1 to value of i1 \<close>
                    (R 2, (L (Num 0))) \<comment> \<open> Secondly set the value of r2 to literal zero \<close>
                  ]
      \<rparr>"

(*select:1[]/[][(R 1, (V (I 1))), (R 2, (L (Num 0)))]*)

lemma guard_select: "Guard select = []"
  by (simp add: select_def)

lemma outputs_select: "Outputs select = []"
  by (simp add: select_def)

definition coin :: "transition" where
"coin \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [],
        Outputs = [Plus (V (R 2)) (V (I 1))],
        Updates = [
                    (R 1, V (R 1)),
                    (R 2, Plus (V (R 2)) (V (I 1)))
                  ]
      \<rparr>"

lemma Updates_coin: "Updates coin = [
                    (R 1, V (R 1)),
                    (R 2, Plus (V (R 2)) (V (I 1)))
                  ]"
  by (simp add: coin_def)

lemma label_coin: "Label coin = ''coin''"
  by (simp add: coin_def)

lemma guard_coin: "Guard coin = []"
  by (simp add: coin_def)

definition vend :: "transition" where
"vend \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [(Ge (V (R 2)) (L (Num 100)))],
        Outputs =  [(V (R 1))],
        Updates = [(R 1, V (R 1)), (R 2, V (R 2))]
      \<rparr>"

lemma label_vend: "Label vend = ''vend''"
  by (simp add: vend_def)

definition vend_fail :: "transition" where
"vend_fail \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [(GExp.Lt (V (R 2)) (L (Num 100)))],
        Outputs =  [],
        Updates = [(R 1, V (R 1)), (R 2, V (R 2))]
      \<rparr>"

lemma guard_vend_fail: "Guard vend_fail = [(GExp.Lt(V (R 2)) (L (Num 100)))]"
  by (simp add: vend_fail_def)

lemma outputs_vend_fail: "Outputs vend_fail = []"
  by (simp add: vend_fail_def)

lemma label_vend_fail: "Label vend_fail = ''vend''"
  by (simp add: vend_fail_def)

lemma arity_vend_fail: "Arity vend_fail = 0"
  by (simp add: vend_fail_def)

lemma guard_vend: "Guard vend = [(Ge (V (R 2)) (L (Num 100)))]"
  by (simp add: vend_def)

definition drinks :: "transition_matrix" where
"drinks \<equiv> {|
          ((0,1), select),    \<comment> \<open> If we want to go from state 1 to state 2 then select will do that \<close>
          ((1,1), coin),
          ((1, 1), vend_fail), \<comment> \<open> If we want to go from state 2 to state 2 then coin will do that \<close>
          ((1,2), vend) \<comment> \<open> If we want to go from state 2 to state 3 then vend will do that \<close>
         |}"

lemma "S drinks = {|0, 1, 2|}"
  apply (simp add: S_def drinks_def)
  by auto

lemmas transitions = select_def coin_def vend_def vend_fail_def

lemma possible_steps_0:  "length i = 1 \<Longrightarrow> possible_steps drinks 0 Map.empty (''select'') i = {|(1, select)|}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma updates_select: "(EFSM.apply_updates (Updates select)
              (case_vname (\<lambda>n. if n = 1 then Some (Str ''coke'') else input2state [] (1 + 1) (I n)) Map.empty) Map.empty) = <R 1:=Str ''coke'', R 2 := Num 0>"
  apply (simp add: select_def)
  apply (rule ext)
  by simp

lemma arity_vend: "Arity vend = 0"
  by (simp add: vend_def)

lemma drinks_vend_insufficient: "\<exists>x1. r (R 2) = Some (Num x1) \<and> x1 < 100 \<Longrightarrow> possible_steps drinks 1 r (''vend'') [] = {|(1, vend_fail)|}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma possible_steps_1_coin: "length i = 1 \<Longrightarrow> possible_steps drinks 1 r ''coin'' i = {|(1, coin)|}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma possible_steps_2_vend: "\<exists>n. r (R 2) = Some (Num n) \<and> n \<ge> 100 \<Longrightarrow> possible_steps drinks 1 r ''vend'' [] = {|(2, vend)|}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma drinks_1_coin: "length (snd a) = 1 \<Longrightarrow> possible_steps drinks 1 r (''coin'') (snd a) = {|(1, coin)|}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma updates_coin: " (EFSM.apply_updates (Updates coin)
            (case_vname (\<lambda>n. if n = 1 then Some (Num i) else input2state [] (1 + 1) (I n))
              (\<lambda>n. if n = 2 then Some (Num r) else <R 1 := s> (R n)))
            <R 1 := s, R 2 := Num r>) = <R 1 := s, R 2 := Num (r+i)>"
  apply (rule ext)
  by (simp add: coin_def del: One_nat_def)

lemma purchase_coke: "observe_trace drinks 0 <> [(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 50]), (''vend'', [])] = [[], [Num 50], [Num 100], [Str ''coke'']]"
  apply (simp add: observe_trace_def)
  apply (simp add: step_def possible_steps_0 fis_singleton_def outputs_select updates_select del: One_nat_def)
  apply (simp add: step_def possible_steps_1_coin updates_coin fis_singleton_def del: One_nat_def)
  apply (simp add: step_def possible_steps_2_vend del: One_nat_def)
  by (simp add: transitions)

lemma invalid_impossible: "l \<noteq> ''coin'' \<Longrightarrow> l \<noteq> ''vend'' \<Longrightarrow> possible_steps drinks 1 d l i = {||}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma invalid_input: "l \<noteq> ''coin'' \<Longrightarrow> l \<noteq> ''vend'' \<Longrightarrow> EFSM.valid drinks 1 d' [(l, i)] \<Longrightarrow> False"
  apply (cases rule: valid.cases)
    apply (simp del: One_nat_def)
   apply simp
  apply clarify
  apply (simp add: step_def del: One_nat_def)
  by (simp add: invalid_impossible fis_singleton_def is_singleton_def del: One_nat_def)

lemma invalid_valid_prefix: "l \<noteq> ''coin'' \<Longrightarrow> l \<noteq> ''vend'' \<Longrightarrow> \<not> (valid_trace drinks [(''select'', [Str ''coke'']), (l, i)])"
  apply clarify
  apply (cases rule: valid.cases)
    apply (simp add: valid_trace_def)
  apply (simp add: valid_trace_def)
  apply clarify
  apply (simp add: step_def possible_steps_0 invalid_input fis_singleton_def)
  using invalid_input by force

lemma invalid_termination: "observe_trace drinks 0 <> [(''select'', [Str ''coke'']), (''invalid'', [Num 50]), (''coin'', [Num 50])] = [[]]"
  apply (simp add: observe_trace_def step_def possible_steps_0 updates_select del: One_nat_def)
  by (simp add: invalid_impossible fis_singleton_def is_singleton_def transitions del: One_nat_def)

abbreviation select_posterior :: "context" where
  "select_posterior \<equiv> \<lbrakk>(V (R 1)) \<mapsto> Bc True, (V (R 2)) \<mapsto> Eq (Num 0)\<rbrakk>"

lemma consistent_select_posterior: "consistent select_posterior"
  apply (simp add: consistent_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num 0>" in exI)
  by (simp add: consistent_empty_4)

lemma select_posterior: "(posterior empty select) = select_posterior"
  apply (simp add: posterior_def select_def remove_input_constraints_def)
  apply (rule ext)
  by simp

lemma medial_select_posterior_vend: "medial select_posterior (Guard vend) = \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> And (Eq (Num 0)) (Geq (Num 100))\<rbrakk>"
  apply (rule ext)
  by (simp add: guard_vend)

lemma r2_0_vend: "\<not>Contexts.can_take vend select_posterior" (* You can't take vend immediately after taking select *)
  apply (simp only: can_take_def medial_select_posterior_vend)
  apply (simp add: consistent_def)
  apply (rule allI)
  apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some (Num 100)) (s (R 2))")
   apply fastforce
  apply simp
  by fastforce

lemma coin_before_vend: "Contexts.can_take vend (posterior_n n coin (posterior \<lbrakk>\<rbrakk> select)) \<longrightarrow> n > 0" (* Corresponds to Example 2 in Foster et. al. *)
  apply (simp add: select_posterior del: Nat.One_nat_def)
  apply (cases n)
   apply (simp add: r2_0_vend del: Nat.One_nat_def)
  by simp

lemma drinks_vend_r2_none: "r2 = None \<Longrightarrow> possible_steps drinks 1 (\<lambda>u. if u = R 1 then Some s else if u = R 2 then r2 else None) (''vend'') [] = {||}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma drinks_vend_sufficient: "r2 = Some (Num x1) \<Longrightarrow>
                \<not> x1 < 100 \<Longrightarrow>
                (possible_steps drinks 1 (\<lambda>u. if u = R 1 then Some s else if u = R 2 then r2 else None) (''vend'') []) = {|(2, vend)|}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma drinks_end: "possible_steps drinks 2 r a b = {||}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma drinks_vend_r2_String: "r2 = Some (Str x2) \<Longrightarrow> possible_steps drinks 1 (\<lambda>u. if u = R 1 then Some s else if u = R 2 then r2 else None) (''vend'') [] = {||}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma drinks_0_invalid: "\<not> (fst a = ''select'' \<and> length (snd a) = 1) \<Longrightarrow>
    (possible_steps drinks 0 Map.empty (fst a) (snd a)) = {||}"
  apply (simp add: drinks_def possible_steps_def transitions)
  by force

lemma drinks_vend_empty: "(possible_steps drinks 0 Map.empty (''vend'') []) = {||}"
  using drinks_0_invalid
  by auto

lemma drinks_1_invalid: "fst a = ''coin'' \<longrightarrow> length (snd a) \<noteq> 1 \<Longrightarrow>
          a \<noteq> (''vend'', []) \<Longrightarrow>
          possible_steps drinks 1 r (fst a) (snd a) = {||}"
proof
  assume not_coin: "fst a = ''coin'' \<longrightarrow> length (snd a) \<noteq> 1"
  assume not_vend: "a \<noteq> (''vend'', [])"
  show "possible_steps drinks 1 r (fst a) (snd a) |\<subseteq>| {||}"
    using not_coin not_vend
    apply (simp add: drinks_def possible_steps_def)
    apply safe
     apply simp
    apply (metis arity_vend arity_vend_fail label_coin label_vend label_vend_fail length_0_conv numeral_1_eq_Suc_0 prod.collapse zero_neq_numeral)
    apply simp
    by (metis One_nat_def arity_vend arity_vend_fail label_vend label_vend_fail length_0_conv numeral_1_eq_Suc_0 prod.collapse simps(2) transitions(2) zero_neq_numeral)
  show "{||} |\<subseteq>| possible_steps drinks 1 r (fst a) (snd a)"
    by simp
qed
end
