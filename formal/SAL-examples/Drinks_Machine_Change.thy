theory Drinks_Machine_Change
  imports "../examples/Drinks_Machine"
begin

definition vend :: "transition" where
"vend \<equiv> \<lparr>
        Label = (STR ''vend''),
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

lemma possible_steps_0:  "length i = 1 \<Longrightarrow> possible_steps drinks 0 Map.empty ((STR ''select'')) i = {|(1, select)|}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma "observe_trace drinks 0 <> [((STR ''select''), [Str ''coke''])] = [[]]"
  unfolding observe_trace_def observe_all_def step_def
  apply (simp add: possible_steps_0)
  by (simp add: transitions)

lemma possible_steps_1_coin: "possible_steps drinks 1 r (STR ''coin'') [Num n'] = {|(1, coin)|}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma possible_steps_1_vend: "n \<ge> 100 \<Longrightarrow> possible_steps drinks 1 <R 1 := Str ''coke'', R 2 := Num n> (STR ''vend'') [] = {|(2, vend)|}"
proof-
  assume premise: "n \<ge> 100"
  have filter: " ffilter
     (\<lambda>((origin, dest), t).
         origin = 1 \<and>
         Label t = STR ''vend'' \<and>
         Arity t = 0 \<and>
         apply_guards (Guard t) (\<lambda>x. case x of I n \<Rightarrow> input2state [] 1 (I n) | R na \<Rightarrow> <R 1 := EFSM.Str ''coke'', R 2 := Num n> (R na)))
     Drinks_Machine_Change.drinks =
    {|((1, 2), Drinks_Machine_Change.vend)|}"
    using premise
    apply (simp add: ffilter_def drinks_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply safe
    by (simp_all add: transitions gval.simps ValueGt_def)
  show ?thesis
    by (simp add: possible_steps_def filter)
qed

lemma "observe_trace drinks 0 <> [((STR ''select''), [Str ''coke'']), ((STR ''coin''), [Num 50]), ((STR ''coin''), [Num 50]), ((STR ''vend''), [])] = [[], [Some (Num 50)], [Some (Num 100)], [Some (Str ''coke''), Some (Num 0)]]"
  unfolding observe_trace_def observe_all_def step_def
  apply (simp add: possible_steps_0 updates_select outputs_select)
  apply (simp add: possible_steps_1_coin updates_coin)
  apply (simp add: possible_steps_1_vend)
  by (simp add: coin_def vend_def)

lemma "observe_trace drinks 0 <> [((STR ''select''), [Str ''coke'']), ((STR ''coin''), [Num 50]), ((STR ''coin''), [Num 100]), ((STR ''vend''), [])] = [[], [Some (Num 50)], [Some (Num 150)], [Some (Str ''coke''), Some (Num 50)]]"
  unfolding observe_trace_def observe_all_def step_def
  apply (simp add: possible_steps_0 updates_select outputs_select)
  apply (simp add: possible_steps_1_coin updates_coin)
  apply (simp add: possible_steps_1_vend)
  by (simp add: coin_def vend_def)

lemma possible_steps_invalid: "l \<noteq> (STR ''coin'') \<and> l \<noteq> (STR ''vend'') \<Longrightarrow> possible_steps drinks 1 d l i = {||}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

(* Stop when we hit a spurious input *)
lemma "observe_trace drinks 0 <> [((STR ''select''), [Str ''coke'']), ((STR ''invalid''), [Num 50])] = [[]]"
  unfolding observe_trace_def observe_all_def step_def
  apply (simp add: possible_steps_0 updates_select outputs_select)
  by (simp add: possible_steps_invalid)

lemma invalid_input: "\<not> accepts drinks 1 d' [((STR ''invalid''), [Num 50])]"
  apply safe
  apply (rule EFSM.accepts.cases)
    apply simp
   apply simp
  apply (simp add: step_def)
  using possible_steps_invalid
  by auto

lemma invalid_valid_prefix: "\<not> (accepts_trace (drinks) [((STR ''select''), [Str ''coke'']), ((STR ''invalid''), [Num 50])])"
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

lemma "observe_trace drinks 0 <> [((STR ''select''), [Str ''coke'']), ((STR ''invalid''), [Num 50]), ((STR ''coin''), [Num 50])] = [[]]"
  unfolding observe_trace_def observe_all_def step_def
  apply (simp add: possible_steps_0 outputs_select updates_select)
  by (simp add: possible_steps_invalid)
end
