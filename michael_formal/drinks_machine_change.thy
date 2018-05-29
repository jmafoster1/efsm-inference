theory drinks_machine_change
  imports EFSM CExp
begin

definition t1 :: "transition" where
"t1 \<equiv> \<lparr>
        Label = ''select'',
        Arity = 1,
        Guard = [], (* No guards *)
        Outputs = [],
        Updates = [ (* Two updates: *)
                    (''r1'', (V ''i1'')), (*  Firstly set value of r1 to value of i1 *)
                    (''r2'', (N 0)) (* Secondly set the value of r2 to literal zero *)
                  ]
      \<rparr>"

definition t2 :: "transition" where
"t2 \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [], (* No guards *)
        Outputs = [(Plus (V ''r2'') (V ''i1''))], (* This could also be written infix with ''+'' *)
        Updates = [
                    (''r1'', (V ''r1'')), (* The value of r1 is unchanged *)
                    (''r2'', (Plus (V ''r2'') (V ''i1''))) (* The value of r2 is increased by the value of i1 *)
                  ]
      \<rparr>"

definition t3 :: "transition" where
"t3 \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [(Ge (V ''r2'') (N 100))], (* This is syntactic sugar for ''Not (Lt (V ''r2'') (N 100))'' which could also appear *)
        Outputs =  [(V ''r1''), (Minus (V ''r2'') (N 100))],
        Updates = [(''r1'', (V ''r1'')), (''r2'', (V ''r2''))]
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

lemma blank_state : "<> = <''r1'' := 0, ''r2'' := 0>"
  by (metis fun_upd_triv null_state_def)

lemma blank_state2:
  assumes "P <''r1'' := 0, ''r2'' := 0>"
  shows "P <>"
  by (metis assms blank_state)

lemma "observe_trace vend (s0 vend) <> [] = []"
  by simp

lemma "observe_trace vend (s0 vend) <> [(''select'', [1])] = [[]]"
  by (simp add: vend_def transitions step_def)

lemma "observe_trace vend (s0 vend) <> [(''select'', [1]), (''coin'', [50])] = [[], [50]]"
  by (simp_all add: step_def join_def index_def vend_def transitions showsp_int_def showsp_nat.simps shows_string_def null_state_def)

lemma "observe_trace vend (s0 vend) <> [(''select'', [1]), (''coin'', [50]), (''coin'', [50])] = [[], [50], [100]]"
  by (simp add: step_def index_def join_def vend_def transitions showsp_int_def showsp_nat.simps shows_string_def null_state_def)

lemma "observe_trace vend (s0 vend) <> [(''select'', [1]), (''coin'', [50]), (''coin'', [50]), (''vend'', [])] = [[], [50], [100], [1, 0]]"
  by (simp add: step_def index_def join_def vend_def transitions showsp_int_def showsp_nat.simps shows_string_def null_state_def)

lemma "observe_trace vend (s0 vend) <> [(''select'', [1]), (''coin'', [50]), (''coin'', [100]), (''vend'', [])] = [[], [50], [150], [1, 50]]"
  by (simp add: step_def index_def join_def vend_def transitions showsp_int_def showsp_nat.simps shows_string_def null_state_def)

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
