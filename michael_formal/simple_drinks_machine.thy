theory simple_drinks_machine
imports EFSM CExp
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
        Guard = [((V ''i1'') = (N 50))],
        Outputs = [(Plus (V ''r2'') (V ''i1''))],
        Updates = [
                  (''r1'', (V ''r1'')),
                  (''r2'', (Plus (V ''r2'') (V ''i1'')))
                ]
      \<rparr>"

definition t3 :: "transition" where
"t3 \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [((V ''i1'') = (N 50))],
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
        Guard = [((V ''r2'') \<ge> (N 100))],
        Outputs =  [(V ''r1'')],
        Updates = [(''r1'', (V ''r1'')), (''r2'', (V ''r2''))]
      \<rparr>"

value "(constraints empty t1) ''r2''"
value "constraints (constraints empty t1) t2"
end