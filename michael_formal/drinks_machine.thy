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
        Guard = [((V ''r2'') \<ge> (N 100))], (* This is syntactic sugar for ''Not (Lt (V ''r2'') (N 100))'' which could also appear *)
        Outputs =  [(V ''r1'')], (* This has one output o1:=r1 where ''r1'' is a variable with a value *)
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

lemma "observe_trace vend (s0 vend) <> [(''select'', [1]), (''coin'', [50]), (''coin'', [50]), (''vend'', [])] = [[], [50], [100], [1]]"
  by (simp add: step_def index_def join_def vend_def transitions showsp_int_def showsp_nat.simps shows_string_def null_state_def)

(*Stop when we hit a spurious input*)
lemma "observe_trace vend (s0 vend) <> [(''select'', [1]), (''cat'', [50])] = [[]]"
  by (simp add: step_def vend_def transitions)

lemma "\<not> (valid_trace (vend) [(''select'', [1]), (''cat'', [50])])"
  by(simp add: step_def vend_def transitions valid_trace_def)

lemma "observe_trace vend (s0 vend) <> [(''select'', [1]), (''cat'', [50]), (''coin'', [50])] = [[]]"
  by (simp add: step_def vend_def transitions)

lemma "( t = []) \<Longrightarrow> (observe_trace e (s0 e) <> t = []) "
  by(simp)

(*Prefix closure stuff*)

lemma "a#l@l' = a#(l@l')" 
  oops

definition "reg_of t = (if t = [] then <> else snd (snd (last t)))"
definition "state_of e t = (if t = [] then s0 e else fst (last t))"

lemma valid_trace_non_empty_observe: "valid_trace e (a#list) \<Longrightarrow> [] \<noteq> observe_all e (s0 e) <> (a # list)"
  apply(simp only:observe_all.simps(2) valid_trace_def)
  by auto

lemma nonempty: "valid_trace e t \<and> t \<noteq> [] \<longrightarrow> observe_all e (s0 e) <> t \<noteq> []"
  apply (simp add: valid_trace_def)
  by auto

lemma valid_trace_drop: "valid_trace e (t @ xs @ [x]) \<Longrightarrow>  valid_trace e (t @ xs)"
proof(induct rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  then show ?case 
qed
  

lemma prefix_closure_single: 
"valid_trace e (t@[e']) \<Longrightarrow>let obs = (observe_all e (s0 e) <> t) in ((observe_all e (s0 e) <> (t@([e']))) = (obs)@(observe_all e (state_of e obs) (reg_of obs) ([e'])))"
proof(induct rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  then show ?case apply (case_tac "t=[]", simp add:state_of_def reg_of_def)
    using state_of_def reg_of_def nonempty try
qed


  apply(induct_tac t = "xs" in rev_induct)
  apply(simp)
   apply(simp add: reg_of_def state_of_def)
(*  apply (simp) *)
  apply (case_tac "t=[]")
apply (simp add: state_of_def reg_of_def)
   apply (simp add: state_of_def reg_of_def nonempty)
  apply(case_tac "step e (fst (last (observe_all e (s0 e) <> t))) (snd (snd (last (observe_all e (s0 e) <> t)))) (fst a) (snd a) = None")
   apply(simp)


lemma prefix_closure: "valid_trace e t \<Longrightarrow>let obs = (observe_all e (s0 e) <> t) in ((observe_all e (s0 e) <> (t@(t'))) = (obs)@(observe_all e (state_of e obs) (reg_of obs) (t')))"
  apply(induct_tac "t'")
   apply(simp add: reg_of_def state_of_def)
(*  apply (simp) *)
  apply (case_tac "t=[]")
apply (simp add: state_of_def reg_of_def)
   apply (simp add: state_of_def reg_of_def nonempty)
  apply(case_tac "step e (fst (last (observe_all e (s0 e) <> t))) (snd (snd (last (observe_all e (s0 e) <> t)))) (fst a) (snd a) = None")
   apply(simp)
  oops

lemma prefix_closure: "valid_trace e t \<Longrightarrow>let obs = (observe_all e (s0 e) <> t) in ((observe_all e (s0 e) <> (t@(rev t'))) = (obs)@(observe_all e (state_of e obs) (reg_of obs) (rev t')))"
  apply(induct_tac "t'")
   apply(simp add: reg_of_def state_of_def)
  apply (simp)
  apply (case_tac "t=[]")
   apply (simp add: state_of_def reg_of_def)
  apply(rule rev_induct, simp)
   apply (simp add: state_of_def reg_of_def nonempty)



  sorry

(*
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
*)
end
