theory drinks_machine_payforward
  imports EFSM drinks_machine
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

definition drinks :: "drinks_machine.statename efsm" where
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

lemma apply_updates_setup [simp]: "(apply_updates (Updates setup) (case_vname Map.empty Map.empty) Map.empty) = <R 2 := Num 0>"
  apply (simp add: setup_def)
  apply (rule ext)
  by simp

lemma label_select_q2: "Label b = ''select'' \<Longrightarrow> b \<in> T drinks (q2, a) \<Longrightarrow> b = select1 \<and> a = q3"
  apply (simp add: drinks_def)
  apply (cases a)
    apply simp
   apply simp
  by (simp add: select1_def)

lemma possible_steps_q2: "possible_steps drinks_machine_payforward.drinks q2 d ''select'' [Str s] = {(q3, select1)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (simp add: label_select_q2)
      apply (simp add: label_select_q2)
     apply (simp add: select1_def)
    apply (simp add: select1_def drinks_def)
   apply (simp add: select1_def)
  by (simp add: select1_def)

lemma updates_select1: "(apply_updates (Updates select1) (case_vname (\<lambda>n. if n = 1 then Some (Str d) else index2state [] (1 + 1) (I n)) (\<lambda>n. if n = 2 then Some (Num n') else None))
          <R 2 := Num 0>) = <R 1 := Str d, R 2 := Num n'>"
  apply (simp add: select1_def)
  apply (rule ext)
  by simp

lemma label_coin_q3: "Label b = ''coin'' \<Longrightarrow> b \<in> T drinks_machine_payforward.drinks (q3, a) \<Longrightarrow> b = coin \<and> a = q3"
  apply (simp add: drinks_def)
  apply (cases a)
    apply (simp add: vend_def)
   apply (simp add: vend_def)
  by (simp add: select1_def)

lemma apply_updates_coin [simp]: "(apply_updates (Updates coin)
          (case_vname (\<lambda>n. if n = 1 then Some (Num input) else index2state [] (1 + 1) (I n)) (\<lambda>n. if n = 2 then Some (Num original) else <R 1 := Str s> (R n)))
          <R 1 := Str s, R 2 := Num original>) = <R 1 := Str s, R 2 := Num (original+input)>"
  apply (simp add: coin_def)
  apply (rule ext)
  by simp

lemma possible_steps_q3_coin: "possible_steps drinks_machine_payforward.drinks q3 d ''coin'' [Num n] = {(q3, coin)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (simp add: label_coin_q3)
      apply (simp add: label_coin_q3)
     apply (simp add: coin_def)
    apply (simp add: coin_def drinks_def)
   apply (simp add: coin_def)
  by (simp add: coin_def)

lemma label_vend_q1: "Label b = ''vend'' \<Longrightarrow> b \<in> T drinks (q3, a) \<Longrightarrow> b = vend \<and> a = q2"
  apply (simp add: drinks_def)
  apply (cases a)
    apply simp
   apply simp
  by (simp add: coin_def)

lemma possible_steps_q3_vend: "n \<ge> 100 \<Longrightarrow> possible_steps drinks_machine_payforward.drinks q3 <R 1 := Str s, R 2 := Num n> ''vend'' [] = {(q2, vend)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (simp add: label_vend_q1)
      apply (simp add: label_vend_q1)
     apply (simp add: vend_def)
    apply (simp add: vend_def drinks_def)
   apply (simp add: vend_def)
  by (simp add: vend_def)

lemma apply_updates_vend [simp]: "(apply_updates (Updates drinks_machine_payforward.vend) (case_vname Map.empty (\<lambda>n. if n = 2 then Some (Num 110) else <R 1 := Str ''coke''> (R n)))
          <R 1 := Str ''coke'', R 2 := Num 110>) = <R 1 := Str ''coke'', R 2 := Num 10>"
  apply (rule ext)
  by (simp add: vend_def)

lemma apply_updates_coin_2 [simp]:"(apply_updates (Updates coin)
          (case_vname (\<lambda>n. if n = 1 then Some (Num 90) else index2state [] (1 + 1) (I n))
            (\<lambda>n. apply_updates (Updates select1)
                   (case_vname (\<lambda>n. if n = 1 then Some (Str ''pepsi'') else index2state [] (1 + 1) (I n)) (\<lambda>n. if n = 2 then Some (Num 10) else <R 1 := Str ''coke''> (R n)))
                   <R 1 := Str ''coke'', R 2 := Num 10> (R n)))
          (apply_updates (Updates select1)
            (case_vname (\<lambda>n. if n = 1 then Some (Str ''pepsi'') else index2state [] (1 + 1) (I n)) (\<lambda>n. if n = 2 then Some (Num 10) else <R 1 := Str ''coke''> (R n)))
            <R 1 := Str ''coke'', R 2 := Num 10>)) = <R 1 := Str ''pepsi'', R 2 := Num 100>"
  apply (rule ext)
  by (simp add: coin_def select1_def)

lemma "observe_trace drinks (s0 drinks) <> [(''setup'', []), (''select'', [Str ''coke'']), (''coin'',[Num 110]), (''vend'', []), (''select'', [Str ''pepsi'']), (''coin'',[Num 90]), (''vend'', [])] = [[],[],[Num 110],[Str ''coke''],[],[Num 100],[Str ''pepsi'']]"
  apply (simp add: possible_steps_q1 possible_steps_q2 updates_select1 possible_steps_q3_coin possible_steps_q3_vend del: One_nat_def)
  by (simp add: transitions)
end
