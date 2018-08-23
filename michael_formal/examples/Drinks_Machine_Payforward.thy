theory Drinks_Machine_Payforward
  imports Drinks_Machine
begin

(* This version of drinks_machine supercedes all of those before 03/04/18 *)
(* It also supercedes "vend.thy"*)

definition "setup" :: "transition" where
"setup \<equiv> \<lparr>
        Label = ''setup'',
        Arity = 0,
        Guard = [], (* No guards *)
        Outputs = [],
        Updates = [(R 2, (L (Num 0)))]
      \<rparr>"

definition "select1 \<equiv> \<lparr>
        Label = ''select'',
        Arity = 1,
        Guard = [], (* No guards *)
        Outputs = [],
        Updates = [
                    (R 1, (V (I 1))), (*  Firstly set value of r1 to value of i1 *)
                    (R 2, (V (R 2)))
                  ]
      \<rparr>"

definition vend :: "transition" where
"vend \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [(Ge (V (R 2)) (L (Num 100)))], (* This is syntactic sugar for ''Not (Lt (V (R 2)) (N 100))'' which could also appear *)
        Outputs =  [(V (R 1))], (* This has one output o1:=r1 where ''r1'' is a variable with a value *)
        Updates = [
                    (R 1, (V (R 1))),
                    (R 2, Minus (V (R 2)) (L (Num 100)))
                  ]
      \<rparr>"

definition drinks :: "statename efsm" where
"drinks \<equiv> \<lparr> 
          s0 = q1,
          T = \<lambda> (a,b) .
                   if (a,b) = (q1,q2) then {setup} (* If we want to go from state 1 to state 2 then select will do that *)
              else if (a,b) = (q2,q3) then {select1} (* If we want to go from state 2 to state 2 then coin will do that *)
              else if (a,b) = (q3,q3) then {coin} (* If we want to go from state 2 to state 3 then drinks will do that *)
              else if (a,b) = (q3,q2) then {vend} (* If we want to go from state 2 to state 3 then drinks will do that *)
              else {} (* There are no other transitions *)
         \<rparr>"

lemma s0_drinks [simp]: "s0 drinks = q1"
  by (simp add: drinks_def)

lemmas transitions = select1_def coin_def vend_def setup_def

lemma label_setup_q2: "Label b = ''setup'' \<Longrightarrow> b \<in> T drinks (q1, a) \<Longrightarrow> b = setup \<and> a = q2"
  apply (simp add: drinks_def)
  apply (cases a)
  by simp_all

lemma possible_steps_q1: "possible_steps drinks q1 Map.empty ''setup'' [] = {(q2, setup)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (simp add: label_setup_q2)
      apply (simp add: label_setup_q2)
     apply (simp add: setup_def)
    apply (simp add: drinks_def)
   apply (simp add: setup_def)
  by (simp add: setup_def)

lemma possible_steps_q2: "possible_steps drinks q2 d ''select'' [Str s] = {(q3, select1)}"
  apply (simp add: possible_steps_def)
  apply safe
  apply (case_tac a)
          apply (simp add: drinks_def)
         apply (simp add: drinks_def)
        apply (simp add: drinks_def)
       apply (simp add: drinks_def)
      apply (case_tac a)
  by (simp_all add: drinks_def select1_def)

lemma possible_steps_q3_coin: "possible_steps drinks q3 d ''coin'' [Num n] = {(q3, coin)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (case_tac a)
          apply (simp add: drinks_def)
         apply (simp add: drinks_def)
        apply (simp add: drinks_def)
        apply (metis (no_types, lifting) Drinks_Machine_Payforward.vend_def One_nat_def one_neq_zero transition.simps(2))
       apply (case_tac a)
          apply (simp add: drinks_def)
         apply (simp add: drinks_def)
        apply (simp add: drinks_def)
       apply (simp add: drinks_def)
      apply (simp add: drinks_def)
      apply (metis (no_types, lifting) Drinks_Machine_Payforward.vend_def One_nat_def empty_iff one_neq_zero singletonD transition.simps(2))
  by (simp_all add: coin_def drinks_def)

lemma possible_steps_q3_vend: "r (R 2) = Some (Num n) \<Longrightarrow> n \<ge> 100 \<Longrightarrow> possible_steps drinks q3 r ''vend'' [] = {(q2, vend)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (case_tac a)
          apply (simp add: drinks_def)
         apply (simp add: drinks_def)
        apply (simp add: drinks_def)
       apply (simp add: drinks_def coin_def)
      apply (case_tac a)
  by (simp_all add: drinks_def coin_def vend_def)

lemma "observe_trace drinks (s0 drinks) <> [(''setup'', []), (''select'', [Str ''coke'']), (''coin'',[Num 110]), (''vend'', []), (''select'', [Str ''pepsi'']), (''coin'',[Num 90]), (''vend'', [])] = [[],[],[Num 110],[Str ''coke''],[],[Num 100],[Str ''pepsi'']]"
  apply (simp add: possible_steps_q1 setup_def del: One_nat_def)
  apply (simp add: possible_steps_q2 select1_def del: One_nat_def)
  apply (simp add: possible_steps_q3_coin coin_def del: One_nat_def)
  apply (simp add: possible_steps_q3_vend vend_def del: One_nat_def)
  apply (simp add: possible_steps_q2 select1_def del: One_nat_def)
  apply (simp add: possible_steps_q3_coin coin_def del: One_nat_def)
  by (simp add: possible_steps_q3_vend vend_def del: One_nat_def)

end
