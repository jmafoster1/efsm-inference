theory simple_drinks_machine
imports EFSM
begin
definition t1 :: "transition" where
"t1 \<equiv> \<lparr>
        Label = ''select'',
        Arity = 1,
        Guard = [],
        Outputs = [],
        Updates = [(''r1'', (V ''i1'')), (''r2'', (N 0))]
      \<rparr>"

definition t2 :: "transition" where
"t2 \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [(gexp.Eq ''i1'' (N 50))],
        Outputs = [(Plus (V ''r2'') (V ''i1''))],
        Updates = [(''r1'', (V ''r1'')),  (''r2'', (Plus (V ''r2'') (V ''i1'')))]
      \<rparr>"

definition t2' :: "transition" where
"t2' \<equiv> \<lparr>
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
        Label = ''coin'',
        Arity = 1,
        Guard = [(gexp.Eq ''i1''(N 50))],
        Outputs = [(Plus (V ''r2'') (V ''i1''))],
        Updates = [
                  (''r1'', (V ''r1'')),
                  (''r2'', (Plus (V ''r2'') (V ''i1'')))
                ]
      \<rparr>"

definition t4 :: "transition" where
"t4 \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [(Ge ''r2'' (N 100))],
        Outputs =  [(V ''r1'')],
        Updates = [(''r1'', (V ''r1'')), (''r2'', (V ''r2''))]
      \<rparr>"

lemma "transition_simulates (posterior empty t1) t2' t2"
  by (simp add: transition_simulates_def constraints_simulates_def posterior_def t1_def t2_def t2'_def consistent_def)
end