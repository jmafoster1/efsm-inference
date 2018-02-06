theory Vend2
  imports Vend
begin

definition vend2 :: "efsm" where
"vend2 \<equiv> \<lparr>S = [1,2,3,4],
          s0 = 1,
          d0 = ((blankdata \<oplus> (1,Some (Inl 0))) \<oplus> (2,Some (Inl 0))),
          M = \<lambda>(s,s') . 
                if (s,s') = (1,2) then [t1]
                else if (s,s') = (2,3) then [t2]
                else if (s,s') = (3,3) then [t2]
                else if (s,s') = (3,4) then [t3]
                else []
          \<rparr>"

theorem "equiv vend2 vend tr1"
  by (simp add: t1_def t2_def t3_def vend_def vend2_def equiv_def observe_def tr1_def)
  
end