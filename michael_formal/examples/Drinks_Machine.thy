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

lemma guard_select [simp]: "Guard select = []"
  by (simp add: select_def)

lemma outputs_select [simp]: "Outputs select = []"
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

lemma label_coin: "Label coin = ''coin''"
  by (simp add: coin_def)

lemma guard_coin [simp]: "Guard coin = []"
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
          ((0,1), {|select|}),    (* If we want to go from state 1 to state 2 then select will do that *)
          ((1,1), {|coin, vend_fail|}), (* If we want to go from state 2 to state 2 then coin will do that *)
          ((1,2), {|vend|}) (* If we want to go from state 2 to state 3 then vend will do that *)
         |}"

lemma "S drinks = {|0, 1, 2|}"
  apply (simp add: S_def drinks_def)
  by auto

lemmas transitions = select_def coin_def vend_def vend_fail_def

definition possible_steps_aux :: "transition_matrix \<Rightarrow> nat \<Rightarrow> (nat \<times> transition) fset" where
  "possible_steps_aux t s = ffUnion (fimage (\<lambda>((origin, dest), t). fimage (\<lambda>x. (dest, x)) t) (ffilter (\<lambda>((origin, destination), t). origin = s) t))"

definition possible_steps :: "transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (nat \<times> transition) fset" where
  "possible_steps e s r l i = ffilter (\<lambda>(dest, t). (((Label t) = l) \<and> ((length i) = (Arity t)) \<and> (apply_guards (Guard t) (join_ir i r)))) (possible_steps_aux e s)"

lemma possible_steps_0:  "length i = Suc 0 \<Longrightarrow> possible_steps drinks 0 Map.empty (''select'') i = {|(1, select)|}"
proof
  have ffilter_drinks_0: "ffilter (\<lambda>((origin, destination), t). origin = 0) drinks = {|((0, 1), {|select|})|}"
    apply (simp add: drinks_def)
    by auto
  have possible_steps_aux_0: "possible_steps_aux drinks 0 = {|(1, select)|}"
    unfolding possible_steps_aux_def
    by (simp add: ffilter_drinks_0)
  show "length i = Suc 0 \<Longrightarrow> Drinks_Machine.possible_steps drinks 0 Map.empty ''select'' i |\<subseteq>| {|(1, select)|}"
    apply (simp add: possible_steps_def possible_steps_aux_0)
    by auto
  show "length i = Suc 0 \<Longrightarrow> {|(1, select)|} |\<subseteq>| Drinks_Machine.possible_steps drinks 0 Map.empty ''select'' i"
    by (simp add: possible_steps_def possible_steps_aux_0 select_def)
qed

lemma select_updates [simp]: "(EFSM.apply_updates (Updates select) (case_vname (\<lambda>n. if n = Suc 0 then Some (Str ''coke'') else input2state [] (Suc 0 + 1) (I n)) Map.empty) Map.empty) = <R 1:=Str ''coke'', R 2 := Num 0>"
  apply (simp add: select_def)
  apply (rule ext)
  by simp

lemma arity_vend: "Arity vend = 0"
  by (simp add: vend_def)

lemma ffilter_drinks_1: "ffilter (\<lambda>((origin, destination), t). origin = 1) drinks = {|((1, 1), {|coin, vend_fail|}), ((1, 2), {|vend|})|}"
  apply (simp add: drinks_def)
  by auto

lemma possible_steps_aux_1: "possible_steps_aux drinks 1 = {|(1, coin), (1, vend_fail), (2, vend)|}"
  unfolding possible_steps_aux_def
  using ffilter_drinks_1
  by auto

lemma possible_steps_1_coin: "length i = 1 \<Longrightarrow> possible_steps drinks 1 r (''coin'') i = {|(1, coin)|}"
proof
  show "length i = 1 \<Longrightarrow> Drinks_Machine.possible_steps drinks 1 r ''coin'' i |\<subseteq>| {|(1, coin)|}"
    apply (simp add: possible_steps_def possible_steps_aux_1 del: One_nat_def)
    using Pair_inject label_vend label_vend_fail by auto
  show "length i = 1 \<Longrightarrow> {|(1, coin)|} |\<subseteq>| Drinks_Machine.possible_steps drinks 1 r ''coin'' i"
    by (simp add: possible_steps_def possible_steps_aux_1 coin_def del: One_nat_def)
qed

lemma possible_steps_1_coin_2: "possible_steps drinks 1 <R (Suc 0) := Str ''coke'', R 2 := Num 50> (''coin'') [Num 50] = {|(1, coin)|}"
proof
  show "possible_steps drinks 1 <R (Suc 0) := Str ''coke'', R 2 := Num 50> ''coin'' [Num 50] |\<subseteq>| {|(1, coin)|}"
    apply (simp add: possible_steps_def possible_steps_aux_1 del: One_nat_def)
    using Pair_inject label_vend label_vend_fail by auto
  show "{|(1, coin)|} |\<subseteq>| Drinks_Machine.possible_steps drinks 1 <R (Suc 0) := Str ''coke'', R 2 := Num 50> ''coin'' [Num 50]"
    by (simp add: possible_steps_def possible_steps_aux_1 coin_def del: One_nat_def)
qed

lemma coin_updates [simp]: "(EFSM.apply_updates (Updates coin)
               (case_vname (\<lambda>n. if n = Suc 0 then Some (Num i) else input2state [] (Suc 0 + 1) (I n)) (\<lambda>n. if n = 2 then Some (Num r2) else <R (Suc 0) := s> (R n)))
               <R (Suc 0) := s', R 2 := Num r2>) = <R 1 := s, R 2 := Num (i+r2)>"
  apply (simp add: transitions)
  apply (rule ext)
  by simp

lemma possible_steps_2_vend: "possible_steps drinks 1 <R (Suc 0) := Str ''coke'', R 2 := Num 100> (''vend'') [] = {|(2, vend)|}"
proof
  show "possible_steps drinks 1 <R (Suc 0) := Str ''coke'', R 2 := Num 100> ''vend'' [] |\<subseteq>| {|(2, vend)|}"
    apply (simp add: possible_steps_def possible_steps_aux_1 del: One_nat_def)
    apply safe
    apply simp
     apply (case_tac "a=1")
      apply (case_tac "b=coin")
       apply (simp add: transitions)
      apply simp
      apply clarify
      apply (simp add: transitions relations join_ir_def)
     apply simp
    apply simp
    apply (case_tac "a=1")
     apply (case_tac "b=coin")
      apply (simp add: transitions)
     apply simp
     apply clarify
      apply (simp add: transitions relations join_ir_def)
    by simp
  show "{|(2, vend)|} |\<subseteq>| Drinks_Machine.possible_steps drinks 1 <R (Suc 0) := Str ''coke'', R 2 := Num 100> ''vend'' []"
    by (simp add: possible_steps_def possible_steps_aux_1 transitions relations connectives join_ir_def del: One_nat_def)
qed

lemma purchase_coke: "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 50]), (''vend'', [])] = [[], [Num 50], [Num 100], [Str ''coke'']]"
  apply (simp add: is_singleton_def the_elem_def possible_steps_0 possible_steps_1_coin possible_steps_1_coin_2 possible_steps_2_vend)
  by (simp add: transitions)

lemma invalid_impossible: "possible_steps drinks 1 d (''invalid'') [Num 50] = {}"
  by (simp add: possible_steps_def drinks_def arity_vend label_coin label_vend_fail)

lemma invalid_input: "EFSM.valid drinks 1 d' [(''invalid'', [Num 50])] \<Longrightarrow> False"
  apply (cases rule: valid.cases)
    apply simp
   apply simp
  apply clarify
  by (simp add: invalid_impossible is_singleton_def)

lemma invalid_valid_prefix: "\<not> (valid_trace drinks [(''select'', [Str ''coke'']), (''invalid'', [Num 50])])"
  apply clarify
  apply (cases rule: valid.cases)
    apply simp
   apply simp
  apply clarify
  apply (simp add: possible_steps_0 invalid_input)
  using invalid_input by force

lemma invalid_termination: "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''invalid'', [Num 50]), (''coin'', [Num 50])] = [[]]"
  apply (simp add: possible_steps_0 invalid_impossible)
  by (simp add: transitions is_singleton_def)

abbreviation select_posterior :: "context" where
  "select_posterior \<equiv> \<lbrakk>(V (R 1)) \<mapsto> Bc True, (V (R 2)) \<mapsto> Eq (Num 0) \<rbrakk>"

lemma consistent_select_posterior: "consistent select_posterior"
  apply (simp add: consistent_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num 0>" in exI)
  by (simp add: consistent_empty_4)

lemma select_posterior: "(posterior empty select) = select_posterior"
  apply (simp add: posterior_def select_def)
  apply (rule ext)
  by simp

lemma medial_select_posterior_vend: "medial select_posterior (Guard vend) = \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> And (Eq (Num 0)) (Geq (Num 100))\<rbrakk>"
  apply (rule ext)
  by (simp add: guard_vend Ge_def Lt_def gNot_def)

lemma r2_0_vend: "\<not>Contexts.can_take vend select_posterior" (* You can't take vend immediately after taking select *)
  apply (simp only: can_take_def medial_select_posterior_vend)
  apply (simp add: consistent_def gAnd_def gNot_def)
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

end
