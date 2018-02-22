theory Vend2
  imports Vend
begin

definition vend2 :: "efsm" where
"vend2 \<equiv> \<lparr>S = [1,2,3,4],
          s0 = 1,
          M = \<lambda>(s,s') . 
                if (s,s') = (1,2) then [t1]
                else if (s,s') = (2,3) then [t2]
                else if (s,s') = (3,3) then [t2]
                else if (s,s') = (3,4) then [t3]
                else []
          \<rparr>"

lemma "equiv vend2 vend tr1"
  by (simp add: t1_def t2_def t3_def vend_def vend2_def equiv_def observe_def tr1_def)

theorem "equiv vend2 vend t"
  apply (simp only: equiv_def observe_def)
  apply (induct_tac "t")
  using observe_steps.simps(1) apply auto[1]

  apply (simp only: observe_steps_def)
 

  apply (simp only: step_def)
  apply (simp only: possible_steps_def)

  apply (simp split: option.splits)
  
  


end