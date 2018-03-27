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

definition t3 :: "transition" where
"t3 \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [((V ''r2'') \<ge> (N 100))],
        Outputs =  [(''o1'', (V ''r1''))],
        Updates = [(''r1'', (V ''r1'')), (''r2'', (V ''r2''))]
      \<rparr>"

lemmas transitions = t1_def t2_def t3_def

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

lemma "observe_trace vend (s0 vend) <> [] = []"
  by simp

lemma "observe_trace vend (s0 vend) <> [(''select'', [1])] = [[]]"
  by (simp add: vend_def transitions)

lemma "observe_trace vend (s0 vend) <> [(''select'', [1]), (''coin'', [50])] = [[], [50]]"
  by (simp_all add: vend_def transitions showsp_int_def showsp_nat.simps shows_string_def null_state_def)

lemma "observe_trace vend (s0 vend) <> [(''select'', [1]), (''coin'', [50]), (''coin'', [50])] = [[], [50], [100]]"
  by (simp add: vend_def transitions showsp_int_def showsp_nat.simps shows_string_def null_state_def)

lemma "observe_trace vend (s0 vend) <> [(''select'', [1]), (''coin'', [50]), (''coin'', [50]), (''vend'', [])] = [[], [50], [100], [1]]"
  by (simp add: vend_def transitions showsp_int_def showsp_nat.simps shows_string_def null_state_def)

(*Stop when we hit a spurious input*)
lemma "observe_trace vend (s0 vend) <> [(''select'', [1]), (''cat'', [50])] = [[]]"
  by (simp add: vend_def transitions)

lemma "\<not> (valid_trace (vend) [(''select'', [1]), (''cat'', [50])])"
  by(simp add: vend_def transitions valid_trace_def)

lemma "observe_trace vend (s0 vend) <> [(''select'', [1]), (''cat'', [50]), (''coin'', [50])] = [[]]"
  by (simp add: vend_def transitions)

(*This crashes because of showsp_nat.simps*)
(*What is ".simps"? Why not "showsp_nat_def"?*)
(*lemma "observe_registers vend (s0 vend) <> [(''select'', [1]), (''coin'', [50]), (''coin'', [51])] = <''r1'':=1, ''r2'':=101>"
  apply (simp add: showsp_int_def showsp_nat.simps shows_string_def null_state_def)*)

lemma "( t = []) \<Longrightarrow> (observe_trace e (s0 e) <> t = []) "
  by(simp)

lemma "a#l@l' = a#(l@l')" 
  oops

definition "reg_of t = (if t = [] then <> else snd (snd (last t)))"
definition "state_of e t = (if t = [] then s0 e else fst (last t))"

lemmas foo = reg_of_def 
lemmas bar = foo  state_of_def

lemma  valid_trace_non_empty_observe: "valid_trace e (a#list) \<Longrightarrow> [] \<noteq> observe_trace2 e (s0 e) <> (a # list)"
  apply(simp only:observe_trace2.simps(2) valid_trace_def)
  by auto

lemma "let obs = (observe_trace2 e (s0 e) <> t) in 
valid_trace e t \<longrightarrow> ((observe_trace2 e (s0 e) <> (t@t')) = (obs)@(observe_trace2 e (state_of e obs) (reg_of obs) t'))"
  apply(induct_tac "t")
  apply(simp add: foo) 
  apply(insert valid_trace_non_empty_observe)

  apply safe
lemma prefix_closure: "valid_trace e t \<Longrightarrow> ((observe_trace e (s0 e) <> (t@t')) = ((observe_trace e (s0 e) <> t))@(observe_trace e (s0 e) (observe_registers e (s0 e) <> t) t'))"
  apply(induct_tac "t'")
   apply(simp)
  apply(insert observe_trace.simps(2))
  
lemma prefix_closure: "((observe_trace e (s0 e) <> t) = obs) \<and> ( (observe_registers e (s0 e) <> t)= reg) \<longrightarrow> ((observe_trace e (s0 e) <> (t@t')) = obs@(observe_trace e (s0 e) reg  t'))"
  oops

lemma prefix_closure: "((observe_trace e (s0 e) <> t) = obs) \<longrightarrow> ((observe_trace e (s0 e) <> (t@t')) = obs@(observe_trace e (s0 e) (observe_registers e (s0 e) <> t) t'))"
  apply (induct_tac "t'")    
   apply (simp)
  apply (simp)

  apply (auto)
   apply (simp add: showsp_int_def)
    apply (simp add: showsp_nat.simps shows_string_def)

  sorry
end
