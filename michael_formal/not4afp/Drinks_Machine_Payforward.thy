theory Drinks_Machine_Payforward
  imports "../examples/Drinks_Machine"
begin

definition "setup" :: "transition" where
"setup \<equiv> \<lparr>
        Label = ''setup'',
        Arity = 0,
        Guard = [], \<comment>\<open> No guards \<close>
        Outputs = [],
        Updates = [(R 2, (L (Num 0)))]
      \<rparr>"

definition "select" :: transition where
"select \<equiv> \<lparr>
        Label = ''select'',
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
        Label = ''vend'',
        Arity = 0,
        Guard = [(Ge (V (R 2)) (L (Num 100)))], \<comment>\<open> This is syntactic sugar for ''Not (Lt (V (R 2)) (N 100))'' which could also appear \<close>
        Outputs =  [(V (R 1))], \<comment>\<open> This has one output o1:=r1 where ''r1'' is a variable with a value \<close>
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

lemma possible_steps_0: "possible_steps drinks 0 Map.empty ''setup'' [] = {|(1, setup)|}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma possible_steps_1: "possible_steps drinks 1 d ''select'' [Str s] = {|(2, select)|}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma possible_steps_2_coin: "possible_steps drinks 2 d ''coin'' [Num n] = {|(2, coin)|}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma possible_steps_2_vend: "r (R 2) = Some (Num n) \<Longrightarrow> n \<ge> 100 \<Longrightarrow> possible_steps drinks 2 r ''vend'' [] = {|(1, vend)|}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma "observe_trace drinks 0 <> [(''setup'', []), (''select'', [Str ''coke'']), (''coin'',[Num 110]), (''vend'', []), (''select'', [Str ''pepsi'']), (''coin'',[Num 90]), (''vend'', [])] = [[],[],[Some (Num 110)],[Some (Str ''coke'')],[],[Some (Num 100)],[Some (Str ''pepsi'')]]"
  unfolding observe_trace_def observe_all_def step_def
  apply (simp add: possible_steps_0 setup_def)
  apply (simp add: possible_steps_1 select_def)
  apply (simp add: possible_steps_2_coin coin_def)
  apply (simp add: possible_steps_2_vend vend_def)
  apply (simp add: possible_steps_1 select_def)
  apply (simp add: possible_steps_2_coin coin_def)
  by (simp add: possible_steps_2_vend vend_def)
end