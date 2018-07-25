theory drinks_machine
  imports EFSM CExp
begin

(* This version of drinks_machine supercedes all of those before 03/04/18 *)
(* It also supercedes "drinks.thy"*)

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

definition drinks :: "efsm" where
"drinks \<equiv> \<lparr> 
          S = [1,2,3],
          s0 = 1,
          T = \<lambda> (a,b) .
              if (a,b) = (1,2) then [select] (* If we want to go from state 1 to state 2 then select will do that *)
              else if (a,b) = (2,2) then [coin] (* If we want to go from state 2 to state 2 then coin will do that *)
              else if (a,b) = (2,3) then [vend] (* If we want to go from state 2 to state 3 then vend will do that *)
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

lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 50]), (''vend'', [])] = [[], [Num 50], [Num 100], [Str ''coke'']]"
  by (simp add: step_def drinks_def transitions)

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
