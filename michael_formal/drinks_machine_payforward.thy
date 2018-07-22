theory drinks_machine_payforward
  imports EFSM CExp
begin

(* This version of drinks_machine supercedes all of those before 03/04/18 *)
(* It also supercedes "vend.thy"*)

definition "setup" :: "transition" where
"setup \<equiv> \<lparr>
        Label = ''setup'',
        Arity = 0,
        Guard = [], (* No guards *)
        Outputs = [],
        Updates = [ (* Two updates: *)
                    (R 2, (L (Num 0)))
                  ]
      \<rparr>"

definition "t1 \<equiv> \<lparr>
        Label = ''select'',
        Arity = 1,
        Guard = [], (* No guards *)
        Outputs = [],
        Updates = [
                    (R 1, (V (I 1))), (*  Firstly set value of r1 to value of i1 *)
                    (R 2, (V (R 2)))
                  ]
      \<rparr>"

definition t2 :: "transition" where
"t2 \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [], (* No guards *)
        Outputs = [(Plus (V (R 2)) (V (I 1)))], (* This could also be written infix with ''+'' *)
        Updates = [
                    (R 1, (V (R 1))), (* The value of r1 is unchanged *)
                    (R 2, (Plus (V (R 2)) (V (I 1)))) (* The value of r2 is increased by the value of i1 *)
                  ]
      \<rparr>"

definition t3 :: "transition" where
"t3 \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [(Ge (V (R 2)) (L (Num 100)))], (* This is syntactic sugar for ''Not (Lt (V (R 2)) (N 100))'' which could also appear *)
        Outputs =  [(V (R 1))], (* This has one output o1:=r1 where ''r1'' is a variable with a value *)
        Updates = [
                    (R 1, (V (R 1))),
                    (R 2, Minus (V (R 2)) (L (Num 100)))
                  ]
      \<rparr>"

definition vend :: "efsm" where
"vend \<equiv> \<lparr> 
          S = [1,2,3],
          s0 = 1,
          T = \<lambda> (a,b) .
              if (a,b) = (1,2) then [setup] (* If we want to go from state 1 to state 2 then t1 will do that *)
              else if (a,b) = (2,3) then [t1] (* If we want to go from state 2 to state 2 then t2 will do that *)
              else if (a,b) = (3,3) then [t2] (* If we want to go from state 2 to state 3 then t3 will do that *)
              else if (a,b) = (3,2) then [t3]
              else [] (* There are no other transitions *)
         \<rparr>"

lemmas transitions = t1_def t2_def t3_def setup_def

lemma "observe_trace vend (s0 vend) <> [(''setup'', []), (''select'', [Str ''coke'']), (''coin'',[Num 110]), (''vend'', []), (''select'', [Str ''pepsi'']), (''coin'',[Num 90]), (''vend'', [])] = [[],[],[Num 110],[Str ''coke''],[],[Num 100],[Str ''pepsi'']]"
  by (simp add: step_def vend_def transitions)
end
