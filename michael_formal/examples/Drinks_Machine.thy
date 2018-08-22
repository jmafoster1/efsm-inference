theory Drinks_Machine
  imports "../EFSM"
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


lemma possible_steps_q0:  "possible_steps drinks q0 Map.empty ''select'' [Str ''coke''] = {(q1, select)}"
  apply (simp add: possible_steps_def drinks_def)
  apply safe
       apply (meson empty_iff old.prod.inject statename.distinct(1))
      apply (meson empty_iff old.prod.inject singletonD statename.distinct(1))
  by (simp_all add: select_def)

lemma select_updates [simp]: "(apply_updates (Updates select) (case_vname (\<lambda>n. if n = Suc 0 then Some (Str ''coke'') else index2state [] (Suc 0 + 1) (I n)) Map.empty) Map.empty) = <R 1:=Str ''coke'', R 2 := Num 0>"
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

lemma coin_50_updates [simp]: "(apply_updates (Updates coin)
               (case_vname (\<lambda>n. if n = Suc 0 then Some (Num 50) else index2state [] (Suc 0 + 1) (I n)) (\<lambda>n. if n = 2 then Some (Num 0) else <R (Suc 0) := Str ''coke''> (R n)))
               <R (Suc 0) := Str ''coke'', R 2 := Num 0>) = <R 1 := Str ''coke'', R 2 := Num 50>"
  apply (simp add: transitions)
  apply (rule ext)
  by simp

lemma coin_100_updates [simp]: "(apply_updates (Updates coin)
               (case_vname (\<lambda>n. if n = Suc 0 then Some (Num 50) else index2state [] (Suc 0 + 1) (I n)) (\<lambda>n. if n = 2 then Some (Num 50) else <R (Suc 0) := Str ''coke''> (R n)))
               <R (Suc 0) := Str ''coke'', R 2 := Num 50>) = <R 1 := Str ''coke'', R 2 := Num 100>"
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

lemma invalid_cat: "valid drinks q1 d' [(''invalid'', [Num 50])] \<Longrightarrow> False"
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
  apply (simp add: possible_steps_q0 invalid_cat)
  using invalid_cat by force

lemma invalid_termination: "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''invalid'', [Num 50]), (''coin'', [Num 50])] = [[]]"
  apply (simp add: possible_steps_q0 invalid_impossible)
  by (simp add: transitions is_singleton_def)
end