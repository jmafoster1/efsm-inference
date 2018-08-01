theory drinks_machine
  imports EFSM CExp
begin

(* This version of drinks_machine supercedes all of those before 03/04/18 *)
(* It also supercedes "drinks.thy"*)

datatype statename = q1 | q2 | q3

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
        Guard = [], (* No guards *)
        Outputs = [(Plus (V (R 2)) (V (I 1)))], (* This could also be written infix with ''+'' *)
        Updates = [
                    (R 1, V (R 1)),
                    (R 2, (Plus (V (R 2)) (V (I 1)))) (* The value of r2 is increased by the value of i1 *)
                  ]
      \<rparr>"

lemma guard_coin [simp]: "Guard coin = []"
  by (simp add: coin_def)

definition vend :: "transition" where
"vend \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [(Ge (V (R 2)) (L (Num 100)))], (* This is syntactic sugar for ''Not (Lt (V ''r2'') (N 100))'' which could also appear *)
        Outputs =  [(V (R 1))], (* This has one output o1:=r1 where ''r1'' is a variable with a value *)
        Updates = [(R 1, V (R 1)), (R 2, V (R 2))]
      \<rparr>"

lemma guard_vend: "Guard vend = [(Ge (V (R 2)) (L (Num 100)))]"
  by (simp add: vend_def)

definition drinks :: "statename efsm" where
"drinks \<equiv> \<lparr> 
          s0 = q1,
          T = \<lambda> (a,b) .
              if (a,b) = (q1,q2) then {select} (* If we want to go from state 1 to state 2 then select will do that *)
              else if (a,b) = (q2,q2) then {coin} (* If we want to go from state 2 to state 2 then coin will do that *)
              else if (a,b) = (q2,q3) then {vend} (* If we want to go from state 2 to state 3 then vend will do that *)
              else {} (* There are no other transitions *)
         \<rparr>"

lemma s0_drinks [simp]: "s0 drinks = q1"
  by (simp add: drinks_def)

(*
  These are lemmas about the machine which could maybe be in another file.
  They don't need to be translated to SAL
*)

lemmas transitions = select_def coin_def vend_def is_singleton_def the_elem_def

lemma "observe_trace drinks (s0 drinks) <> [] = []"
  by simp

lemma label_select_q2: "Label t = ''select'' \<and>
             t \<in> (if s' = q2 then {select} else if (q1, s') = (q2, q2) then {coin} else if (q1, s') = (q2, q3) then {vend} else {}) \<Longrightarrow> t = select \<and> s' = q2"
  apply (cases s')
    apply simp
   apply simp
  by (simp add: select_def)

lemma label_coin_q2: "Label b = ''coin'' \<Longrightarrow>
           b \<in> (if a = q2 then {coin} else if (q2, a) = (q2, q3) then {vend} else {}) \<Longrightarrow> b=coin \<and> a = q2"
  apply (cases a)
    apply simp
   apply simp
  by (simp add: vend_def)

lemma label_vend_q3: "Label b = ''vend'' \<Longrightarrow>
           b \<in> (if a = q2 then {coin} else if (q2, a) = (q2, q3) then {vend} else {}) \<Longrightarrow> b=vend \<and> a = q3"
  apply (cases a)
    apply simp
   apply (simp add: coin_def)
  by (simp add: vend_def)

lemma possible_steps_q1:  "possible_steps drinks q1 Map.empty ''select'' [Str ''coke''] = {(q2, select)}"
  apply (simp add: possible_steps_def drinks_def)
  apply safe
       apply (meson empty_iff old.prod.inject statename.distinct(1))
      apply (meson empty_iff old.prod.inject singletonD statename.distinct(1))
  by (simp_all add: select_def)

lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke''])] = [[]]"
  by (simp add: is_singleton_def the_elem_def possible_steps_q1)

lemma select_updates [simp]: "(apply_updates (Updates select) (case_vname (\<lambda>n. if n = Suc 0 then Some (Str ''coke'') else index2state [] (Suc 0 + 1) (I n)) Map.empty) Map.empty) = <R 1:=Str ''coke'', R 2 := Num 0>"
  apply (simp add: select_def)
  apply (rule ext)
  by simp

lemma possible_steps_q2_coin: "possible_steps drinks q2 <R (Suc 0) := Str ''coke'', R 2 := Num 0> ''coin'' [Num 50] = {(q2, coin)}"
  apply (simp add: possible_steps_def drinks_def)
  apply safe
  using label_coin_q2 apply blast
      apply (metis One_nat_def empty_iff one_neq_zero singletonD transition.select_convs(2) vend_def)
  by (simp_all add: coin_def)

lemma possible_steps_q2_coin_2: "possible_steps drinks q2 <R (Suc 0) := Str ''coke'', R 2 := Num 50> ''coin'' [Num 50] = {(q2, coin)}"
  apply (simp add: possible_steps_def drinks_def)
  apply safe
  using label_coin_q2 apply blast
      apply (metis One_nat_def empty_iff one_neq_zero singletonD transition.select_convs(2) vend_def)
  by (simp_all add: coin_def)

lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''coin'', [Num 50])] = [[], [Num 50]]"
  apply (simp add: is_singleton_def the_elem_def possible_steps_q1 possible_steps_q2_coin possible_steps_q2_coin_2)
  by (simp add: coin_def)

lemma coin_50_updates [simp]: "(apply_updates (Updates coin)
               (case_vname (\<lambda>n. if n = Suc 0 then Some (Num 50) else index2state [] (Suc 0 + 1) (I n)) (\<lambda>n. if n = 2 then Some (Num 0) else <R (Suc 0) := Str ''coke''> (R n)))
               <R (Suc 0) := Str ''coke'', R 2 := Num 0>) = <R 1 := Str ''coke'', R 2 := Num 50>"
  apply (simp add: transitions)
  apply (rule ext)
  by simp

lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 50])] = [[], [Num 50], [Num 100]]"
  apply (simp add: is_singleton_def the_elem_def possible_steps_q1 possible_steps_q2_coin possible_steps_q2_coin_2)
  by (simp add: transitions)

lemma coin_100_updates [simp]: "(apply_updates (Updates coin)
               (case_vname (\<lambda>n. if n = Suc 0 then Some (Num 50) else index2state [] (Suc 0 + 1) (I n)) (\<lambda>n. if n = 2 then Some (Num 50) else <R (Suc 0) := Str ''coke''> (R n)))
               <R (Suc 0) := Str ''coke'', R 2 := Num 50>) = <R 1 := Str ''coke'', R 2 := Num 100>"
  apply (simp add: transitions)
  apply (rule ext)
  by simp

lemma possible_steps_q3_vend: "possible_steps drinks q2 <R (Suc 0) := Str ''coke'', R 2 := Num 100> ''vend'' [] = {(q3, vend)}"
  apply (simp add: possible_steps_def drinks_def)
  apply safe
       apply (metis coin_def empty_iff old.prod.inject one_neq_zero singletonD transition.select_convs(2))
      apply (metis coin_def empty_iff one_neq_zero singleton_iff transition.select_convs(2))
  by (simp_all add: vend_def)

lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 50]), (''vend'', [])] = [[], [Num 50], [Num 100], [Str ''coke'']]"
  apply (simp add: is_singleton_def the_elem_def possible_steps_q1 possible_steps_q2_coin possible_steps_q2_coin_2 possible_steps_q3_vend)
  by (simp add: transitions)

lemma cat_impossible: "possible_steps drinks q2 <R (Suc 0) := Str ''coke'', R 2 := Num 0> ''cat'' [Num 50] = {}"
  apply (simp add: possible_steps_def drinks_def)
  by (simp add: vend_def coin_def)

(*Stop when we hit a spurious input*)
lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''cat'', [Num 50])] = [[]]"
  by (simp add: is_singleton_def the_elem_def possible_steps_q1 cat_impossible)

lemma "\<not> (valid_trace (drinks) [(''select'', [Str ''coke'']), (''cat'', [Num 50])])"
  apply (simp add: possible_steps_q1 cat_impossible)
  by (simp add: transitions)

lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''cat'', [Num 50]), (''coin'', [Num 50])] = [[]]"
  apply (simp add: possible_steps_q1 cat_impossible)
  by (simp add: transitions)

lemma "( t = []) \<Longrightarrow> (observe_trace e (s0 e) <> t = []) "
  by(simp)
end
