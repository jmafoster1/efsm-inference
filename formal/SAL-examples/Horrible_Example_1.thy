theory Horrible_Example_1
imports "../EFSM"
begin
definition t1 :: "transition" where
"t1 \<equiv> \<lparr>
        Label = (STR ''f''),
        Arity = 1,
        Guard = [],
        Outputs = [],
        Updates = [(R 1, (V (I 1)))]
      \<rparr>"

definition t2 :: "transition" where
"t2 \<equiv> \<lparr>
        Label = (STR ''g''),
        Arity = 0,
        Guard = [(gexp.Gt (V (R 1)) (L (Num 5)))],
        Outputs = [],
        Updates = [(R 1, (Plus (V (R 1)) (L (Num 5))))]
      \<rparr>"

definition t3 :: "transition" where
"t3 \<equiv> \<lparr>
        Label = (STR ''h''),
        Arity = 0,
        Guard = [(GExp.Lt (V (R 1)) (L (Num 10)))],
        Outputs = [],
        Updates = []
      \<rparr>"

definition t4 :: "transition" where
"t4 \<equiv> \<lparr>
        Label = (STR ''h''),
        Arity = 0,
        Guard = [(Ge (V (R 1)) (L (Num 10)))],
        Outputs = [],
        Updates = []
      \<rparr>"

definition vend :: transition_matrix where
"vend \<equiv> {| 
              ((0,1), t1),    \<comment>\<open> If we want to go from state 1 to state 2, t1 will do that \<close>
              ((1,1), t2),    \<comment>\<open> If we want to go from state 2 to state 2, t2 will do that \<close>
              ((1,2), t3),    \<comment>\<open> If we want to go from state 2 to state 3, t3 or t4 will do that \<close>
              ((1, 2), t4)
         |}"

lemma "\<forall> i r. \<not> (apply_guards (Guard t3) (join_ir i r) \<and> apply_guards (Guard t4) (join_ir i r))"
  by (simp add: t3_def t4_def gval.simps)
end