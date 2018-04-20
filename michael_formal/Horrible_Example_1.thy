theory Horrible_Example_1
imports Constraints EFSM
begin
definition t1 :: "transition" where
"t1 \<equiv> \<lparr>
        Label = ''f'',
        Arity = 1,
        Guard = [],
        Outputs = [],
        Updates = [(''r1'', (V ''i1''))]
      \<rparr>"

definition t2 :: "transition" where
"t2 \<equiv> \<lparr>
        Label = ''g'',
        Arity = 0,
        Guard = [(gexp.Gt ''r1'' (N 5))],
        Outputs = [],
        Updates = [(''r1'', (Plus (V ''r1'') (N 5)))]
      \<rparr>"

definition t3 :: "transition" where
"t3 \<equiv> \<lparr>
        Label = ''h'',
        Arity = 0,
        Guard = [(gexp.Lt ''r1'' (N 10))],
        Outputs = [],
        Updates = []
      \<rparr>"

definition t4 :: "transition" where
"t4 \<equiv> \<lparr>
        Label = ''h'',
        Arity = 0,
        Guard = [(Ge ''r1'' (N 10))],
        Outputs = [],
        Updates = []
      \<rparr>"

definition vend :: "efsm" where
"vend \<equiv> \<lparr> 
          S = [1,2,3],
          s0 = 1,
          T = \<lambda> (a,b) .
              if (a,b) = (1,2) then [t1] (* If we want to go from state 1 to state 2 then t1 will do that *)
              else if (a,b) = (2,2) then [t2] (* If we want to go from state 2 to state 2 then t2 will do that *)
              else if (a,b) = (2,3) then [t3, t4] (* If we want to go from state 2 to state 3 then t3 or t4 will do that *)
              else [] (* There are no other transitions *)
         \<rparr>"

lemma "\<forall> i r. \<not> (apply_guards (Guard t3) i r \<and> apply_guards (Guard t4) i r)"
  by (simp add: t3_def t4_def) 
end