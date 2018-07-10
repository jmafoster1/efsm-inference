theory drinks_machine_string
  imports drinks_machine
begin



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

lemma "observe_trace vend (s0 vend) <> [(''select'', [''coke'']), (''coin'', [50])] = [[], [50]]"
  sorry

lemma "observe_trace vend (s0 vend) <> [(''select'', [''coke'']), (''coin'', [50]), (''coin'', [50])] = [[], [50], [100]]"
  sorry

lemma "observe_trace vend (s0 vend) <> [(''select'', [''pepsi'']), (''coin'', [50]), (''coin'', [50]), (''vend'', [])] = [[], [50], [100], [''pepsi'', 0]]"
  sorry

lemma "observe_trace vend (s0 vend) <> [(''select'', [''fanta'']), (''coin'', [50]), (''coin'', [100]), (''vend'', [])] = [[], [50], [150], [''fanta'', 50]]"
  sorry
end
