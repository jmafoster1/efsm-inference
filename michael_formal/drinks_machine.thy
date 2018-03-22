theory drinks_machine
  imports EFSM
begin

definition t1_updates :: update_function where
  "t1_updates = [(''r1'', (V ''i1'')), (''r2'', (N 0))]"
declare t1_updates_def [simp]

definition t1 :: "transition" where
"t1 \<equiv> \<lparr> Label = ''select'',
        Arity = 1,
        Guard = trueguard, 
        Outputs = blank,
        Updates = t1_updates (*<''r1'' := (V ''i1''), ''r2'' := 0>*)
      \<rparr>"
declare t1_def [simp]

definition t2_updates :: update_function where
  "t2_updates = [
                  (''r1'', (V ''r1'')),
                  (''r2'', (Plus (V ''r2'') (V ''i1'')))
                ]"
declare t2_updates_def [simp]

definition t2_outputs :: output_function where
  "t2_outputs = [ (''o1'', (Plus (V ''r2'') (V ''i1'')))]"
declare t2_outputs_def [simp]

definition t2 :: "transition" where
"t2 \<equiv> \<lparr> Label = ''coin'',
        Arity = 1,
        Guard = trueguard, 
        Outputs = t2_outputs,
        Updates = t2_updates (*<''r1'' := (V ''i1''), ''r2'' := 0>*)
      \<rparr>"
declare t2_def [simp]

definition t3_outputs :: output_function where
  "t3_outputs = [(''o1'', (V ''r1''))]"
declare t3_outputs_def [simp]

definition t3_guard :: guard where
"t3_guard = [(Less (N 100) (V ''r2''))]"
declare t3_guard_def [simp]

definition t3 :: "transition" where
"t3 \<equiv> \<lparr> Label = ''vend'',
        Arity = 0,
        Guard = t3_guard, 
        Outputs = t3_outputs,
        Updates = no_updates
      \<rparr>"
declare t3_def [simp]

lemma blank_state : "<> = <''r1'' := 0, ''r2'' := 0>"
  by (metis fun_upd_triv null_state_def)

lemma blank_state2 (*[intro]*):
  assumes "P <''r1'' := 0, ''r2'' := 0>"
  shows "P <>"
  by (metis assms blank_state)

definition vend :: "efsm" where
"vend \<equiv> \<lparr> S = [1,2,3],
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

lemma "observe_trace vend (s0 vend) <> [(''select'', [1])] = [<>]"
  by simp

lemma "input2state [1] 1 = <''i1'':=1>"
  apply (rule ext)
  apply (simp add: showsp_int_def cong: if_cong)
  apply (simp add: showsp_nat.simps)
  apply (simp add: shows_string_def)
  done

lemma "observe_trace vend (s0 vend) <''r1'':=0, ''r2'':=0> [(''select'', [1]), (''coin'', [50])] = [<>, <''o1'':=50>]"
  apply (simp cong: if_cong)
  
  

lemma "observe_trace vend (s0 vend) <> [(''select'', [1]), (''coin'', [50]), (''coin'', [50])] = [<>, <''o1'':=50>, <''o1'':=100>]"
  by simp

lemma "observe_trace vend (s0 vend) <> [(''select'', [1]), (''coin'', [50]), (''coin'', [51]), (''vend'', [])] = [[], [50], [101], [1]]"
  by simp

(*Stop when we hit a spurious input*)
lemma "observe_trace vend (s0 vend) <> [(''select'', [1]), (''cat'', [50])] = [[]]"
  by simp

lemma "observe_trace vend (s0 vend) <> [(''select'', [1]), (''cat'', [50]), (''coin'', [50])] = [[]]"
  by simp
end