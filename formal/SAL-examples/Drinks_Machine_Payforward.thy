theory Drinks_Machine_Payforward
  imports "../examples/Drinks_Machine"
begin

definition "setup" :: "transition" where
"setup \<equiv> \<lparr>
        Label = (STR ''setup''),
        Arity = 0,
        Guard = [], \<comment>\<open> No guards \<close>
        Outputs = [],
        Updates = [(R 2, (L (Num 0)))]
      \<rparr>"

definition "select" :: transition where
"select \<equiv> \<lparr>
        Label = (STR ''select''),
        Arity = 1,
        Guard = [], \<comment>\<open> No guards \<close>
        Outputs = [],
        Updates = [
                    (R 1, (V (I 1))), \<comment>\<open>  Firstly set value of r1 to value of i1 \<close>
                    (R 2, (V (R 2)))
                  ]
      \<rparr>"

definition vend :: "transition" where
"vend \<equiv> \<lparr>
        Label = (STR ''vend''),
        Arity = 0,
        Guard = [(Ge (V (R 2)) (L (Num 100)))], \<comment>\<open> This is syntactic sugar for ''Not (Lt (V (R 2)) (N 100))'' which could also appear \<close>
        Outputs =  [(V (R 1))], \<comment>\<open> This has one output o1:=r1 where (STR ''r1'') is a variable with a value \<close>
        Updates = [
                    (R 1, (V (R 1))),
                    (R 2, Minus (V (R 2)) (L (Num 100)))
                  ]
      \<rparr>"

definition drinks :: transition_matrix where
"drinks \<equiv> {|
             ((0,1), setup),  \<comment>\<open> If we want to go from state 0 to state 1 then select will do that \<close>
             ((1,2), select), \<comment>\<open> If we want to go from state 1 to state 2 then coin will do that \<close>
             ((2,2), coin),   \<comment>\<open> If we want to go from state 2 to state 2 then drinks will do that \<close>
             ((2,1), vend)    \<comment>\<open> If we want to go from state 2 to state 1 then drinks will do that \<close>
         |}"

lemmas transitions = select_def coin_def vend_def setup_def

lemma possible_steps_0: "possible_steps drinks 0 Map.empty (STR ''setup'') [] = {|(1, setup)|}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma possible_steps_1: "possible_steps drinks 1 d (STR ''select'') [Str s] = {|(2, select)|}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma possible_steps_2_coin: "possible_steps drinks 2 d (STR ''coin'') [Num n] = {|(2, coin)|}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma possible_steps_2_vend: "r (R 2) = Some (Num n) \<Longrightarrow> n \<ge> 100 \<Longrightarrow> possible_steps drinks 2 r (STR ''vend'') [] = {|(1, vend)|}"
proof-
  assume premise1: "r (R 2) = Some (Num n)"
  assume premise2: "n \<ge> 100"
  have filter: "ffilter
     (\<lambda>((origin, dest), t).
         origin = 2 \<and>
         Label t = STR ''vend'' \<and> Arity t = 0 \<and> apply_guards (Guard t) (\<lambda>x. case x of I n \<Rightarrow> input2state [] 1 (I n) | R n \<Rightarrow> r (R n)))
     Drinks_Machine_Payforward.drinks =
    {|((2, 1), Drinks_Machine_Payforward.vend)|}"
    using premise1 premise2
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
    apply safe
    by (simp_all add: transitions gval.simps ValueGt_def)
  show ?thesis
    by (simp add: possible_steps_def filter)
qed

lemma "observe_trace drinks 0 <> [((STR ''setup''), []), ((STR ''select''), [Str ''coke'']), ((STR ''coin''),[Num 110]), ((STR ''vend''), []), ((STR ''select''), [Str ''pepsi'']), ((STR ''coin''),[Num 90]), ((STR ''vend''), [])] = [[],[],[Some (Num 110)],[Some (Str ''coke'')],[],[Some (Num 100)],[Some (Str ''pepsi'')]]"
  unfolding observe_trace_def observe_all_def step_def
  apply (simp add: possible_steps_0 setup_def)
  apply (simp add: possible_steps_1 select_def)
  apply (simp add: possible_steps_2_coin coin_def)
  apply (simp add: possible_steps_2_vend vend_def)
  apply (simp add: possible_steps_1 select_def)
  apply (simp add: possible_steps_2_coin coin_def)
  by (simp add: possible_steps_2_vend vend_def)
end