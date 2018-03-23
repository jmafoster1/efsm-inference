theory drinks_machine
  imports EFSM
begin

definition t1 :: "transition" where
"t1 \<equiv> \<lparr>
        Label = ''select'',
        Arity = 1,
        Guard = true,
        Outputs = [],
        Updates = [(''r1'', (V ''i1'')), (''r2'', (N 0))]
      \<rparr>"
declare t1_def [simp]

definition t2 :: "transition" where
"t2 \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = true,
        Outputs = [(''o1'', (Plus (V ''r2'') (V ''i1'')))],
        Updates = [
                  (''r1'', (V ''r1'')),
                  (''r2'', (Plus (V ''r2'') (V ''i1'')))
                ]
      \<rparr>"
declare t2_def [simp]

definition t3 :: "transition" where
"t3 \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [((V ''r2'') \<ge> (N 100))],
        Outputs =  [(''o1'', (V ''r1''))],
        Updates = [(''r1'', (V ''r1'')), (''r2'', (V ''r2''))]
      \<rparr>"
declare t3_def [simp]

lemma blank_state : "<> = <''r1'' := 0, ''r2'' := 0>"
  by (metis fun_upd_triv null_state_def)

lemma blank_state2:
  assumes "P <''r1'' := 0, ''r2'' := 0>"
  shows "P <>"
  by (metis assms blank_state)

definition vend :: "efsm" where
"vend \<equiv> \<lparr> 
          S = [1,2,3],
          s0 = 1,
          T = \<lambda> (a,b) .
              if (a,b) = (1,2) then [t1]
              else if (a,b) = (2,2) then [t2]
              else if (a,b) = (2,3) then [t3]
              else []
         \<rparr>"
declare vend_def [simp]

lemma "observe_trace vend (s0 vend) <> [] = []"
  by simp

lemma "observe_trace vend (s0 vend) <> [(''select'', [1])] = [[]]"
  by simp

lemma "observe_trace vend (s0 vend) <> [(''select'', [1]), (''coin'', [50])] = [[], [50]]"
  by (simp_all add: showsp_int_def showsp_nat.simps shows_string_def null_state_def)

lemma "observe_trace vend (s0 vend) <> [(''select'', [1]), (''coin'', [50]), (''coin'', [50])] = [[], [50], [100]]"
  by (simp add: showsp_int_def showsp_nat.simps shows_string_def null_state_def)

lemma "observe_trace vend (s0 vend) <> [(''select'', [1]), (''coin'', [50]), (''coin'', [50]), (''vend'', [])] = [[], [50], [100], [1]]"
  by (simp add: showsp_int_def showsp_nat.simps shows_string_def null_state_def)

(*Stop when we hit a spurious input*)
lemma "observe_trace vend (s0 vend) <> [(''select'', [1]), (''cat'', [50])] = [[]]"
  by simp

lemma "observe_trace vend (s0 vend) <> [(''select'', [1]), (''cat'', [50]), (''coin'', [50])] = [[]]"
  by simp

(*This crashes because of showsp_nat.simps*)
(*What is ".simps"? Why not "showsp_nat_def"?*)
(*lemma "observe_registers vend (s0 vend) <> [(''select'', [1]), (''coin'', [50]), (''coin'', [51])] = <''r1'':=1, ''r2'':=101>"
  apply (simp add: showsp_int_def showsp_nat.simps shows_string_def null_state_def)*)


lemma "((observe_trace e (s0 e) <> t) = obs) \<longrightarrow> ((observe_trace e (s0 e) <> (t@t')) = obs@(observe_trace e (s0 e) (observe_registers e (s0 e) <> t) t'))"
  apply (induct_tac "t")
   apply (simp)
  apply (simp only: observe_registers_def)
  sorry
end
