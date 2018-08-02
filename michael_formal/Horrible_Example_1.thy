theory Horrible_Example_1
imports EFSM
begin
definition t1 :: "transition" where
"t1 \<equiv> \<lparr>
        Label = ''f'',
        Arity = 1,
        Guard = [],
        Outputs = [],
        Updates = [(R 1, (V (I 1)))]
      \<rparr>"

definition t2 :: "transition" where
"t2 \<equiv> \<lparr>
        Label = ''g'',
        Arity = 0,
        Guard = [(gexp.Gt (V (R 1)) (L (Num 5)))],
        Outputs = [],
        Updates = [(R 1, (Plus (V (R 1)) (L (Num 5))))]
      \<rparr>"

definition t3 :: "transition" where
"t3 \<equiv> \<lparr>
        Label = ''h'',
        Arity = 0,
        Guard = [(GExp.Lt (V (R 1)) (L (Num 10)))],
        Outputs = [],
        Updates = []
      \<rparr>"

definition t4 :: "transition" where
"t4 \<equiv> \<lparr>
        Label = ''h'',
        Arity = 0,
        Guard = [(Ge (V (R 1)) (L (Num 10)))],
        Outputs = [],
        Updates = []
      \<rparr>"

datatype statename = q1 | q2 | q3

definition vend :: "statename efsm" where
"vend \<equiv> \<lparr> 
          s0 = q1,
          T = \<lambda> (a,b) .
                   if (a,b) = (q1,q2) then {t1} (* If we want to go from state 1 to state 2 then t1 will do that *)
              else if (a,b) = (q2,q2) then {t2} (* If we want to go from state 2 to state 2 then t2 will do that *)
              else if (a,b) = (q2,q3) then {t3, t4} (* If we want to go from state 2 to state 3 then t3 or t4 will do that *)
              else {} (* There are no other transitions *)
         \<rparr>"

lemma "\<forall> i r. \<not> (apply_guards (Guard t3) (join_ir i r) \<and> apply_guards (Guard t4) (join_ir i r))"
  by (simp add: t3_def t4_def) 
end