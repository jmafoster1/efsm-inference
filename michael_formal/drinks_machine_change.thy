theory drinks_machine_change
  imports drinks_machine
begin

definition vend :: "transition" where
"vend \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [(Ge (V (R 2)) (L (Num 100)))], (* This is syntactic sugar for ''Not (Lt (V (R 2)) (N 100))'' which could also appear *)
        Outputs =  [(V (R 1)), (Minus (V (R 2)) (L (Num 100)))],
        Updates = [(R 1, (V (R 1))), (R 2, (V (R 2)))]
      \<rparr>"

definition drinks :: "drinks_machine.statename efsm" where
"drinks \<equiv> \<lparr> 
          s0 = q1,
          T = \<lambda> (a,b) .
                   if (a,b) = (q1,q2) then {select} (* If we want to go from state 1 to state 2 then select will do that *)
              else if (a,b) = (q2,q2) then {coin} (* If we want to go from state 2 to state 2 then coin will do that *)
              else if (a,b) = (q2,q3) then {vend} (* If we want to go from state 2 to state 3 then drinks will do that *)
              else {} (* There are no other transitions *)
         \<rparr>"

lemma s0_drinks [simp]: "s0 drinks = q1"
  by (simp add: drinks_def)


(*
  These are lemmas about the machine which could maybe be in another file.
  They don't need to be translated to SAL
*)

lemmas transitions = select_def coin_def vend_def

lemma "observe_trace drinks (s0 drinks) <> [] = []"
  by simp

lemma label_select_q2: "Label b = ''select'' \<Longrightarrow> b \<in> T drinks_machine_change.drinks (q1, a) \<Longrightarrow> b = select \<and> a = q2"
  apply (simp add: drinks_def)
  apply (cases a)
  by simp_all

lemma possible_steps_q1: "possible_steps drinks q1 Map.empty ''select'' [Str ''coke''] = {(q2, select)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (simp add: label_select_q2)
      apply (simp add: label_select_q2)
     apply (simp add: select_def)
    apply (simp add: drinks_def)
   apply (simp add: select_def)
  by (simp add: select_def)

lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke''])] = [[]]"
  by (simp add: possible_steps_q1)

lemma label_coin_q2: "Label b = ''coin'' \<Longrightarrow> b \<in> T drinks (q2, a) \<Longrightarrow> b = coin \<and> a = q2"
  apply (simp add: drinks_def)
  apply (cases a)
  by (simp_all add: vend_def)

lemma possible_steps_q2_coin: "possible_steps drinks q2 r ''coin'' [Num n'] = {(q2, coin)}"
    apply (simp add: possible_steps_def)
  apply safe
       apply (simp add: label_coin_q2)
      apply (simp add: label_coin_q2)
     apply (simp add: coin_def)
    apply (simp add: drinks_def coin_def)
   apply (simp add: coin_def)
  by (simp add: coin_def)

lemma label_vend_q3: "Label b = ''vend'' \<Longrightarrow> b \<in> T drinks (q2, a) \<Longrightarrow> b = vend \<and> a = q3"
  apply (simp add: drinks_def)
  apply (cases a)
  by (simp_all add: coin_def)

lemma possible_steps_q2_vend: "n \<ge> 100 \<Longrightarrow> possible_steps drinks_machine_change.drinks q2 <R (Suc 0) := Str ''coke'', R 2 := Num n> ''vend'' [] = {(q3, vend)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (simp add: label_vend_q3)
      apply (simp add: label_vend_q3)
     apply (simp add: vend_def)
    apply (simp add: vend_def drinks_def)
   apply (simp add: vend_def)
  by (simp add: vend_def)

lemma updates_coin_150 [simp]: "(apply_updates (Updates coin)
          (case_vname (\<lambda>n. if n = Suc 0 then Some (Num 100) else index2state [] (Suc 0 + 1) (I n)) (\<lambda>n. if n = 2 then Some (Num 50) else <R (Suc 0) := Str ''coke''> (R n)))
          <R (Suc 0) := Str ''coke'', R 2 := Num 50>) = <R 1 := Str ''coke'', R 2 := Num 150>"
  apply (rule ext)
  by (simp add: coin_def)

lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 50]), (''vend'', [])] = [[], [Num 50], [Num 100], [Str ''coke'', Num 0]]"
  apply (simp add: possible_steps_q1 possible_steps_q2_coin possible_steps_q2_vend)
  by (simp add: transitions)

lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 100]), (''vend'', [])] = [[], [Num 50], [Num 150], [Str ''coke'', Num 50]]"
  apply (simp add: possible_steps_q1 possible_steps_q2_coin possible_steps_q2_vend)
  by (simp add: transitions)

lemma cat_impossible: "possible_steps drinks q2 d ''cat'' [Num 50] = {}"
  apply (simp add: possible_steps_def drinks_def)
  by (simp add: vend_def coin_def)

(*Stop when we hit a spurious input*)
lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''cat'', [Num 50])] = [[]]"
  by (simp add: possible_steps_q1 cat_impossible is_singleton_def)

lemma invalid_cat: "valid drinks q2 d' [(''cat'', [Num 50])] \<Longrightarrow> False"
  apply (cases rule: valid.cases)
    apply simp
   apply simp
  apply clarify
  by (simp add: cat_impossible is_singleton_def)

lemma "\<not> (valid_trace (drinks) [(''select'', [Str ''coke'']), (''cat'', [Num 50])])"
  apply clarify
  apply (cases rule: valid.cases)
    apply simp
   apply simp
  apply clarify
  apply (simp add: possible_steps_q1 invalid_cat)
  using invalid_cat by force

lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''cat'', [Num 50]), (''coin'', [Num 50])] = [[]]"
  by (simp add: possible_steps_q1 cat_impossible is_singleton_def)

lemma "( t = []) \<Longrightarrow> (observe_trace e (s0 e) <> t = []) "
  by(simp)
end
