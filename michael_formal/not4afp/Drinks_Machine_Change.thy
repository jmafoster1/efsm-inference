theory Drinks_Machine_Change
  imports "../examples/Drinks_Machine"
begin

definition vend :: "transition" where
"vend \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [(Ge (V (R 2)) (L (Num 100)))], \<comment>\<open> This is syntactic sugar for ''Not (Lt (V (R 2)) (N 100))'' which could also appear \<close>
        Outputs =  [(V (R 1)), (Minus (V (R 2)) (L (Num 100)))],
        Updates = [(R 1, (V (R 1))), (R 2, (V (R 2)))]
      \<rparr>"

definition drinks :: transition_matrix where
"drinks \<equiv> {|
             ((0,1), select), \<comment>\<open> If we want to go from state 0 to state 1 then select will do that \<close>
             ((1,1), coin),   \<comment>\<open> If we want to go from state 1 to state 1 then coin will do that \<close>
             ((1,2), vend)    \<comment>\<open> If we want to go from state 1 to state 2 then vend will do that \<close>
         |}"

lemmas transitions = select_def coin_def vend_def

lemma "observe_trace drinks 0 <> [] = []"
  by (simp add: observe_trace_def)

lemma possible_steps_0:  "length i = 1 \<Longrightarrow> possible_steps drinks 0 Map.empty (''select'') i = {|(1, select)|}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma "observe_trace drinks 0 <> [(''select'', [Str ''coke''])] = [[]]"
  unfolding observe_trace_def observe_all_def step_def
  apply (simp add: possible_steps_0)
  by (simp add: transitions)

lemma possible_steps_1_coin: "possible_steps drinks 1 r ''coin'' [Num n'] = {|(1, coin)|}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma possible_steps_1_vend: "n \<ge> 100 \<Longrightarrow> possible_steps drinks 1 <R 1 := Str ''coke'', R 2 := Num n> ''vend'' [] = {|(2, vend)|}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma "observe_trace drinks 0 <> [(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 50]), (''vend'', [])] = [[], [Some (Num 50)], [Some (Num 100)], [Some (Str ''coke''), Some (Num 0)]]"
  unfolding observe_trace_def observe_all_def step_def
  apply (simp add: possible_steps_0 updates_select outputs_select)
  apply (simp add: possible_steps_1_coin updates_coin)
  apply (simp add: possible_steps_1_vend)
  by (simp add: coin_def vend_def)

lemma "observe_trace drinks 0 <> [(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 100]), (''vend'', [])] = [[], [Some (Num 50)], [Some (Num 150)], [Some (Str ''coke''), Some (Num 50)]]"
  unfolding observe_trace_def observe_all_def step_def
  apply (simp add: possible_steps_0 updates_select outputs_select)
  apply (simp add: possible_steps_1_coin updates_coin)
  apply (simp add: possible_steps_1_vend)
  by (simp add: coin_def vend_def)

lemma possible_steps_invalid: "l \<noteq> ''coin'' \<and> l \<noteq> ''vend'' \<Longrightarrow> possible_steps drinks 1 d l i = {||}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

(* Stop when we hit a spurious input *)
lemma "observe_trace drinks 0 <> [(''select'', [Str ''coke'']), (''invalid'', [Num 50])] = [[]]"
  unfolding observe_trace_def observe_all_def step_def
  apply (simp add: possible_steps_0 updates_select outputs_select)
  by (simp add: possible_steps_invalid)

lemma invalid_input: "\<not> accepts drinks 1 d' [(''invalid'', [Num 50])]"
  apply safe
  apply (rule EFSM.accepts.cases)
    apply simp
   apply simp
  apply (simp add: step_def)
  using possible_steps_invalid
  by auto

lemma invalid_valid_prefix: "\<not> (accepts_trace (drinks) [(''select'', [Str ''coke'']), (''invalid'', [Num 50])])"
  unfolding accepts_trace_def
  apply clarify
  apply (rule EFSM.accepts.induct)
    apply simp
   apply simp
   defer
   apply simp
  apply (rule EFSM.accepts.cases)
    apply simp
   apply simp
  apply (simp add: step_def)
  apply clarify
  apply (simp add: possible_steps_0 outputs_select updates_select)
  using invalid_input
  by simp

lemma "observe_trace drinks 0 <> [(''select'', [Str ''coke'']), (''invalid'', [Num 50]), (''coin'', [Num 50])] = [[]]"
  unfolding observe_trace_def observe_all_def step_def
  apply (simp add: possible_steps_0 outputs_select updates_select)
  by (simp add: possible_steps_invalid)
end
