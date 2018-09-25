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

datatype statename = q0 | q1 | q2 | q3

definition select :: "transition" where
"select \<equiv> \<lparr>
        Label = ''select'',
        Arity = 1,
        Guard = [], (* No guards *)
        Outputs = [],
        Updates = [ (* Two updates: *)
                    (R 1, (V (I 1))), (*  Firstly set value of r1 to value of i1 *)
                    (R 2, (L (Num 0))) (* Secondly set the value of r2 to literal zero *)
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
        Outputs = [(V (R 2)) + (V (I 1))],
        Updates = [
                    (R 1, V (R 1)),
                    (R 2, (V (R 2)) + (V (I 1)))
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
        Guard = [((V (R 2)) \<ge> (L (Num 100)))],
        Outputs =  [(V (R 1))],
        Updates = [(R 1, V (R 1)), (R 2, V (R 2))]
      \<rparr>"

lemma label_vend: "Label vend = ''vend''"
  by (simp add: vend_def)

definition vend_fail :: "transition" where
"vend_fail \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [((V (R 2)) < (L (Num 100)))],
        Outputs =  [],
        Updates = [(R 1, V (R 1)), (R 2, V (R 2))]
      \<rparr>"

lemma guard_vend_fail: "Guard vend_fail = [((V (R 2)) < (L (Num 100)))]"
  by (simp add: vend_fail_def)

lemma outputs_vend_fail: "Outputs vend_fail = []"
  by (simp add: vend_fail_def)

lemma label_vend_fail: "Label vend_fail = ''vend''"
  by (simp add: vend_fail_def)

lemma arity_vend_fail: "Arity vend_fail = 0"
  by (simp add: vend_fail_def)

lemma guard_vend: "Guard vend = [(Ge (V (R 2)) (L (Num 100)))]"
  by (simp add: vend_def)

definition drinks :: "statename efsm" where
"drinks \<equiv> \<lparr>
          s0 = q0,
          T = \<lambda> (a,b) .
              if (a,b) = (q0,q1) then {select}    (* If we want to go from state 1 to state 2 then select will do that *)
              else if (a,b) = (q1,q1) then {coin, vend_fail} (* If we want to go from state 2 to state 2 then coin will do that *)
              else if (a,b) = (q1,q2) then {vend} (* If we want to go from state 2 to state 3 then vend will do that *)
              else {} (* There are no other transitions *)
         \<rparr>"

lemma s0_drinks [simp]: "s0 drinks = q0"
  by (simp add: drinks_def)

lemmas transitions = select_def coin_def vend_def

lemma possible_steps_q0:  "length i = Suc 0 \<Longrightarrow> possible_steps drinks q0 Map.empty ''select'' i = {(q1, select)}"
  apply (simp add: possible_steps_def drinks_def)
  apply safe
       apply (meson empty_iff old.prod.inject statename.distinct(1))
      apply (meson empty_iff old.prod.inject singletonD statename.distinct(1))
  by (simp_all add: select_def)

lemma select_updates [simp]: "(EFSM.apply_updates (Updates select) (case_vname (\<lambda>n. if n = Suc 0 then Some (Str ''coke'') else input2state [] (Suc 0 + 1) (I n)) Map.empty) Map.empty) = <R 1:=Str ''coke'', R 2 := Num 0>"
  apply (simp add: select_def)
  apply (rule ext)
  by simp

lemma arity_vend: "Arity vend = 0"
  by (simp add: vend_def)

lemma possible_steps_q1_coin: "length i = 1 \<Longrightarrow> possible_steps drinks q1 r ''coin'' i = {(q1, coin)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (case_tac a)
         apply (simp add: drinks_def)
        apply (simp add: drinks_def)
       apply (simp add: drinks_def arity_vend)
       apply (case_tac a)
         apply (simp add: drinks_def)
       apply (simp add: drinks_def)
        apply (simp add: drinks_def)
       apply (simp add: drinks_def)
      apply (case_tac a)
         apply (simp add: drinks_def)
        apply (simp add: drinks_def)
        apply (case_tac "b = coin")
         apply simp
        apply (simp add: label_vend_fail)
       apply (simp add: drinks_def label_vend)
  by (simp_all add: drinks_def coin_def)

lemma possible_steps_q1_coin_2: "possible_steps drinks q1 <R (Suc 0) := Str ''coke'', R 2 := Num 50> ''coin'' [Num 50] = {(q1, coin)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (case_tac a)
         apply (simp add: drinks_def)
         apply (simp add: drinks_def)
         apply (simp add: drinks_def arity_vend)
       apply (case_tac a)
         apply (simp add: drinks_def)
         apply (simp add: drinks_def)
        apply (simp add: drinks_def)
       apply (simp add: drinks_def)
       apply (case_tac a)
         apply (simp add: drinks_def)
        apply (simp add: drinks_def)
        apply (case_tac "b = coin")
         apply simp
        apply (simp add: arity_vend_fail)
       apply (simp add: drinks_def arity_vend)
  by (simp_all add: drinks_def coin_def)

lemma coin_updates [simp]: "(EFSM.apply_updates (Updates coin)
               (case_vname (\<lambda>n. if n = Suc 0 then Some (Num i) else input2state [] (Suc 0 + 1) (I n)) (\<lambda>n. if n = 2 then Some (Num r2) else <R (Suc 0) := s> (R n)))
               <R (Suc 0) := s', R 2 := Num r2>) = <R 1 := s, R 2 := Num (i+r2)>"
  apply (simp add: transitions)
  apply (rule ext)
  by simp

lemma possible_steps_q2_vend: "possible_steps drinks q1 <R (Suc 0) := Str ''coke'', R 2 := Num 100> ''vend'' [] = {(q2, vend)}"
  apply (simp add: possible_steps_def drinks_def)
  apply safe
       apply (case_tac a)
         apply (simp add: drinks_def)
        apply (simp add: drinks_def)
        apply (case_tac "b = coin")
         apply (simp add: coin_def)
        apply (simp add: vend_fail_def)
       apply simp
      apply (case_tac a)
         apply (simp add: drinks_def)
       apply (simp add: drinks_def)
       apply (case_tac "b = coin")
        apply (simp add: coin_def)
        apply (simp add: vend_fail_def)
       apply simp
      apply simp
      apply (case_tac a)
         apply simp
        apply simp
        apply (case_tac "b = coin")
         apply (simp add: coin_def)
        apply (simp add: vend_fail_def)
  by (simp_all add: vend_def)

lemma purchase_coke: "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 50]), (''vend'', [])] = [[], [Num 50], [Num 100], [Str ''coke'']]"
  apply (simp add: is_singleton_def the_elem_def possible_steps_q0 possible_steps_q1_coin possible_steps_q1_coin_2 possible_steps_q2_vend)
  by (simp add: transitions)

lemma invalid_impossible: "possible_steps drinks q1 d ''invalid'' [Num 50] = {}"
  by (simp add: possible_steps_def drinks_def arity_vend label_coin label_vend_fail)

lemma invalid_input: "EFSM.valid drinks q1 d' [(''invalid'', [Num 50])] \<Longrightarrow> False"
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
  apply (simp add: possible_steps_q0 invalid_input)
  using invalid_input by force

lemma invalid_termination: "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''invalid'', [Num 50]), (''coin'', [Num 50])] = [[]]"
  apply (simp add: possible_steps_q0 invalid_impossible)
  by (simp add: transitions is_singleton_def)

abbreviation select_posterior :: "context" where
  "select_posterior \<equiv> \<lbrakk>(V (R 1)) \<mapsto> Bc True, (V (R 2)) \<mapsto> Eq (Num 0) \<rbrakk>"

lemma select_posterior: "(posterior empty select) = select_posterior"
  apply (simp add: posterior_def select_def)
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

end
