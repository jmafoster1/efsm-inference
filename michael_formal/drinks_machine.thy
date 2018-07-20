theory drinks_machine
  imports EFSM CExp
begin

(* This version of drinks_machine supercedes all of those before 03/04/18 *)
(* It also supercedes "vend.thy"*)

definition t1 :: "transition" where
"t1 \<equiv> \<lparr>
        Label = ''select'',
        Arity = 1,
        Guard = [], (* No guards *)
        Outputs = [],
        Updates = [ (* Two updates: *)
                    (R 1, (V (I 1))), (*  Firstly set value of r1 to value of i1 *)
                    (R 2, (N 0)) (* Secondly set the value of r2 to literal zero *)
                  ]
      \<rparr>"

lemma guard_t1 [simp]: "Guard t1 = []"
  by (simp add: t1_def)

definition t2 :: "transition" where
"t2 \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [], (* No guards *)
        Outputs = [(Plus (V (R 2)) (V (I 1)))], (* This could also be written infix with ''+'' *)
        Updates = [
                    (R 1, V (R 1)),
                    (R 2, (Plus (V (R 2)) (V (I 1)))) (* The value of r2 is increased by the value of i1 *)
                  ]
      \<rparr>"

lemma guard_t2 [simp]: "Guard t2 = []"
  by (simp add: t2_def)

definition t3 :: "transition" where
"t3 \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [(Ge (V (R 2)) (N 100))], (* This is syntactic sugar for ''Not (Lt (V ''r2'') (N 100))'' which could also appear *)
        Outputs =  [(V (R 1))], (* This has one output o1:=r1 where ''r1'' is a variable with a value *)
        Updates = [(R 1, V (R 1)), (R 2, V (R 2))]
      \<rparr>"

definition vend :: "efsm" where
"vend \<equiv> \<lparr> 
          S = [1,2,3],
          s0 = 1,
          T = \<lambda> (a,b) .
              if (a,b) = (1,2) then [t1] (* If we want to go from state 1 to state 2 then t1 will do that *)
              else if (a,b) = (2,2) then [t2] (* If we want to go from state 2 to state 2 then t2 will do that *)
              else if (a,b) = (2,3) then [t3] (* If we want to go from state 2 to state 3 then t3 will do that *)
              else [] (* There are no other transitions *)
         \<rparr>"

(*
  These are lemmas about the machine which could maybe be in another file.
  They don't need to be translated to SAL
*)

lemmas transitions = t1_def t2_def t3_def

lemma "observe_trace vend (s0 vend) <> [] = []"
  by simp

lemma "observe_trace vend (s0 vend) <> [(''select'', [Str ''coke''])] = [[]]"
  by (simp add: vend_def transitions step_def)

lemma "observe_trace vend (s0 vend) <> [(''select'', [Str ''coke'']), (''coin'', [Num 50])] = [[], [Num 50]]"
  by (simp_all add: step_def vend_def transitions)

lemma "observe_trace vend (s0 vend) <> [(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 50])] = [[], [Num 50], [Num 100]]"
  by (simp add: step_def vend_def transitions)

value "apply_updates [(R 1, (V (I 1))),(R 2, (N 0))] <> <> (R 1)"

lemma "observe_trace vend (s0 vend) <> [(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 50]), (''vend'', [])] = [[], [Num 50], [Num 100], [Str ''coke'']]"
  by (simp add: step_def vend_def transitions)

(*Stop when we hit a spurious input*)
lemma "observe_trace vend (s0 vend) <> [(''select'', [1]), (''cat'', [50])] = [[]]"
  by (simp add: step_def vend_def transitions)

lemma "\<not> (valid_trace (vend) [(''select'', [1]), (''cat'', [50])])"
  by(simp add: step_def vend_def transitions)

lemma "observe_trace vend (s0 vend) <> [(''select'', [1]), (''cat'', [50]), (''coin'', [50])] = [[]]"
  by (simp add: step_def vend_def transitions)

lemma "( t = []) \<Longrightarrow> (observe_trace e (s0 e) <> t = []) "
  by(simp)
end
