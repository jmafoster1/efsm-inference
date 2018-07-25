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

definition drinks :: "efsm" where
"drinks \<equiv> \<lparr> 
          S = [1,2,3],
          s0 = 1,
          T = \<lambda> (a,b) .
              if (a,b) = (1,2) then [select] (* If we want to go from state 1 to state 2 then select will do that *)
              else if (a,b) = (2,2) then [coin] (* If we want to go from state 2 to state 2 then coin will do that *)
              else if (a,b) = (2,3) then [vend] (* If we want to go from state 2 to state 3 then drinks will do that *)
              else [] (* There are no other transitions *)
         \<rparr>"

(*
  These are lemmas about the machine which could maybe be in another file.
  They don't need to be translated to SAL
*)

lemmas transitions = select_def coin_def vend_def

lemma "observe_trace drinks (s0 drinks) <> [] = []"
  by simp

lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke''])] = [[]]"
  by (simp add: drinks_def transitions step_def)

lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''coin'', [Num 50])] = [[], [Num 50]]"
  by (simp_all add: step_def drinks_def transitions)

lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 50])] = [[], [Num 50], [Num 100]]"
  by (simp add: step_def drinks_def transitions)

lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 50]), (''vend'', [])] = [[], [Num 50], [Num 100], [Str ''coke'', Num 0]]"
  by (simp_all add: step_def drinks_def transitions)

lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 100]), (''vend'', [])] = [[], [Num 50], [Num 150], [Str ''coke'', Num 50]]"
  by (simp_all add: step_def drinks_def transitions)

(*Stop when we hit a spurious input*)
lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''cat'', [Num 50])] = [[]]"
  by (simp add: step_def drinks_def transitions)

lemma "\<not> (valid_trace (drinks) [(''select'', [Str ''coke'']), (''cat'', [Num 50])])"
  by(simp add: step_def drinks_def transitions)

lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''cat'', [Num 50]), (''coin'', [Num 50])] = [[]]"
  by (simp add: step_def drinks_def transitions)

lemma "( t = []) \<Longrightarrow> (observe_trace e (s0 e) <> t = []) "
  by(simp)
end
