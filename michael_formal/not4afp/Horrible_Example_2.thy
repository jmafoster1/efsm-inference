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

definition h2 :: "statename efsm" where
"h2 \<equiv> \<lparr> 
          s0 = q1,
          T = \<lambda> (a,b) .
                   if (a,b) = (q1,q2) then {t1} (* If we want to go from state 1 to state 2 then t1 will do that *)
              else if (a,b) = (q2,q2) then {t2} (* If we want to go from state 2 to state 2 then t2 will do that *)
              else if (a,b) = (q2,q3) then {t3} (* If we want to go from state 2 to state 3 then t3 or t4 will do that *)
              else {} (* There are no other transitions *)
         \<rparr>"
end