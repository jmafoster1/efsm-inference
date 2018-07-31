theory simple_drinks_machine
imports EFSM Contexts drinks_machine
begin
definition t1 :: "transition" where
"t1 \<equiv> \<lparr>
        Label = ''select'',
        Arity = 1,
        Guard = [],
        Outputs = [],
        Updates = [(R 1, (V (I 1))), (R 2, (L (Num 0)))]
      \<rparr>"

definition coin50 :: "transition" where
"coin50 \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [(gexp.Eq (V (I 1)) (L (Num 50)))],
        Outputs = [(Plus (V (R 2)) (V (I 1)))],
        Updates = [(R 1, (V (R 1))),  (R 2, Plus (V (R 2)) (L (Num 50)))]
      \<rparr>"

lemma updates_coin50: "Updates coin50 = [(R 1, (V (R 1))),  (R 2, Plus (V (R 2)) (L (Num 50)))]"
  by (simp add: coin50_def)

definition coin :: "transition" where
"coin \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [],
        Outputs = [(Plus (V (R 2)) (V (I 1)))],
        Updates = [
                  (R 1, (V (R 1))),
                  (R 2, (Plus (V (R 2)) (V (I 1))))
                ]
      \<rparr>"

lemma guard_coin: "Guard coin = []"
  by (simp add: coin_def)

definition t3 :: "transition" where
"t3 \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [(Ge (V (R 2)) (L (Num 100)))],
        Outputs =  [(V (R 1))],
        Updates = [(R 1, (V (R 1))), (R 2, (V (R 2)))]
      \<rparr>"

definition vend :: "statename efsm" where
"vend \<equiv> \<lparr> 
          s0 = q0,
          T = \<lambda> (a,b) .
                   if (a,b) = (q0,q1) then {t1} (* If we want to go from state 1 to state 2 then t1 will do that *)
              else if (a,b) = (q1,q1) then {coin50} (* If we want to go from state 2 to state 2 then coin50 will do that *)
              else if (a,b) = (q1,q2) then {t3} (* If we want to go from state 2 to state 3 then t3 will do that *)
              else {} (* There are no other transitions *)
         \<rparr>"

definition vend_equiv :: "statename efsm" where
"vend_equiv \<equiv> \<lparr> 
          s0 = q0,
          T = \<lambda> (a,b) .
                   if (a,b) = (q0,q1) then {t1} (* If we want to go from state 1 to state 2 then t1 will do that *)
              else if (a,b) = (q1,q1) then {coin} (* If we want to go from state 2 to state 2 then coin will do that *)
              else if (a,b) = (q1,q2) then {t3} (* If we want to go from state 2 to state 3 then t3 will do that *)
              else {} (* There are no other transitions *)
         \<rparr>"

lemma medial_coin50: "medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> (Guard coin50) = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n), V (I 1) \<mapsto> Eq (Num 50)\<rbrakk>"
  apply (simp add: coin50_def)
  apply (rule ext)
  by simp

lemma consistent_medial_coin50: "consistent (medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> (Guard coin50))"
  apply (simp add: coin50_def consistent_def del: Nat.One_nat_def)
  apply (rule_tac x="<R 1 := Num 1, R 2 := Num n, I 1 := Num 50>" in exI)
  by (simp add: consistent_empty_4)

lemma compose_plus_n_50: "(compose_plus (Eq (Num n)) (Eq (Num 50))) = Eq (Num (n+50))"
  apply (simp add: valid_def satisfiable_def)
  by auto

lemma coin50_posterior: "posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> coin50 = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> Eq (Num (n+50))\<rbrakk>"
  apply (simp add: posterior_def consistent_medial_coin50 del: Nat.One_nat_def)
  apply (simp only: medial_coin50 updates_coin50)
  apply (simp add: compose_plus_n_50 del: compose_plus.simps)
  apply (rule ext)
  by simp

lemma consistent_medial_coin: "consistent (medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n), V (I 1) \<mapsto> cexp.Eq (Num 50)\<rbrakk> (Guard coin))"
  apply (simp add: coin_def consistent_def del: One_nat_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num n, I 1 := Num 50>" in exI)
  apply (simp del: One_nat_def)
  by (simp add: consistent_empty_4)

lemma consistent_medial_coin_2: "consistent (medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> (Guard coin))"
  apply (simp add: coin_def consistent_def del: One_nat_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num n, I 1 := Num 50>" in exI)
  apply (simp del: One_nat_def)
  by (simp add: consistent_empty_4)

lemma posterior_coin_2: "posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n), V (I 1) \<mapsto> cexp.Eq (Num 50)\<rbrakk> coin = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> Eq (Num (n+50))\<rbrakk>"
  apply (simp add: posterior_def consistent_medial_coin del: Nat.One_nat_def)
  apply (simp add: coin_def compose_plus_n_50 del: Nat.One_nat_def compose_plus.simps)
  apply (rule ext)
  by simp

lemma posterior_coin: "(posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> coin) = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> Bc True\<rbrakk>"
  apply (simp add: posterior_def consistent_medial_coin_2 del: Nat.One_nat_def)
  apply (simp add: coin_def compose_plus_n_50 valid_def satisfiable_def del: Nat.One_nat_def)
  apply (rule ext)
  by simp

lemma consistent_true: "\<forall>r. c r = Undef \<or> c r = Bc True \<Longrightarrow> consistent c"
  apply (simp only: consistent_def)
  apply (rule_tac x="<>" in exI)
  apply (rule allI)
  by auto

(* coin subsumes coin50 no matter how many times it is looped round *)
lemma "subsumes \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> Eq (Num n)\<rbrakk> coin coin50"
  apply (simp only: subsumes_def)
  apply safe
     apply (simp add: coin_def coin50_def)
    apply (simp add: coin_def coin50_def)
   apply (simp add: coin50_posterior medial_coin50 posterior_coin_2 del: Nat.One_nat_def)
  by (simp add: posterior_coin consistent_empty_1 consistent_true del: Nat.One_nat_def)
end