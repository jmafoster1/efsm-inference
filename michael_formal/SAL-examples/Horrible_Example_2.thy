theory Horrible_Example_2
imports Horrible_Example_1
begin
definition t3 :: "transition" where
"t3 \<equiv> \<lparr>
        Label = ''h'',
        Arity = 0,
        Guard = [],
        Outputs = [],
        Updates = []
      \<rparr>"

definition h2 :: transition_matrix where
"h2 \<equiv> {|
              ((0,1), t1), \<comment>\<open> If we want to go from state 1 to state 2, t1 will do that \<close>
              ((1,1), t2), \<comment>\<open> If we want to go from state 2 to state 2, t2 will do that \<close>
              ((1,2), t3)  \<comment>\<open> If we want to go from state 2 to state 3, t3 will do that \<close>
       |}"
end