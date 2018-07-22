theory simple_drinks_machine
imports EFSM Contexts
begin
definition t1 :: "transition" where
"t1 \<equiv> \<lparr>
        Label = ''select'',
        Arity = 1,
        Guard = [],
        Outputs = [],
        Updates = [(R 1, (V (I 1))), (R 2, (L (Num 0)))]
      \<rparr>"

definition t2 :: "transition" where
"t2 \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [(gexp.Eq (V (I 1)) (L (Num 50)))],
        Outputs = [(Plus (V (R 2)) (V (I 1)))],
        Updates = [(R 1, (V (R 1))),  (R 2, Plus (V (R 2)) (L (Num 50)))]
      \<rparr>"

lemma updates_t2: "Updates t2 = [(R 1, (V (R 1))),  (R 2, Plus (V (R 2)) (L (Num 50)))]"
  by (simp add: t2_def)

definition t2' :: "transition" where
"t2' \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [],
        Outputs = [(Plus (V (R 2)) (V (I 1)))],
        Updates = [
                  (R 1, (V (R 1))),
                  (R 2, (Plus (V (R 2)) (V (I 1))))
                ]
      \<rparr>"

lemma guard_t2': "Guard t2' = []"
  by (simp add: t2'_def)

definition t3 :: "transition" where
"t3 \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [(Ge (V (R 2)) (L (Num 100)))],
        Outputs =  [(V (R 1))],
        Updates = [(R 1, (V (R 1))), (R 2, (V (R 2)))]
      \<rparr>"

definition vend :: "efsm" where
"vend \<equiv> \<lparr> 
          S = [1,2,3],
          s0 = 1,
          T = \<lambda> (a,b) .
              if (a,b) = (1,2) then [t1] (* If we want to go from state 1 to state 2 then t1 will do that *)
              else if (a,b) = (2,2) then [t2] (* If we want to go from state 2 to state 2 then t2 will do that *)
              else if (a,b) = (2,3) then [t3] (* If we want to go from state 2 to state 3 then t3 will do that *)
              else [] (* There are no other transitions *)
         \<rparr>"

definition vend_equiv :: "efsm" where
"vend_equiv \<equiv> \<lparr> 
          S = [1,2,3],
          s0 = 1,
          T = \<lambda> (a,b) .
              if (a,b) = (1,2) then [t1] (* If we want to go from state 1 to state 2 then t1 will do that *)
              else if (a,b) = (2,2) then [t2'] (* If we want to go from state 2 to state 2 then t2' will do that *)
              else if (a,b) = (2,3) then [t3] (* If we want to go from state 2 to state 3 then t3 will do that *)
              else [] (* There are no other transitions *)
         \<rparr>"

lemma medial_t2: "medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> (Guard t2) = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n), V (I 1) \<mapsto> Eq (Num 50)\<rbrakk>"
  apply (simp add: t2_def)
  apply (rule ext)
  by simp

lemma consistent_medial_t2: "consistent (medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> (Guard t2))"
  apply (simp add: t2_def consistent_def del: Nat.One_nat_def)
  apply (rule_tac x="<R 1 := Num 1, R 2 := Num n, I 1 := Num 50>" in exI)
  by (simp add: consistent_empty_4)

lemma compose_plus_n_50: "(compose_plus (Eq (Num n)) (Eq (Num 50))) = Eq (Num (n+50))"
  apply (simp add: valid_def satisfiable_def)
  by auto

lemma t2_posterior: "posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> t2 = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> Eq (Num (n+50))\<rbrakk>"
  apply (simp add: posterior_def consistent_medial_t2 del: Nat.One_nat_def)
  apply (simp only: medial_t2 updates_t2)
  apply (simp add: compose_plus_n_50 del: compose_plus.simps)
  apply (rule ext)
  by simp

lemma consistent_medial_t2': "consistent (medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n), V (I 1) \<mapsto> cexp.Eq (Num 50)\<rbrakk> (Guard t2'))"
  apply (simp add: t2'_def consistent_def del: One_nat_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num n, I 1 := Num 50>" in exI)
  apply (simp del: One_nat_def)
  by (simp add: consistent_empty_4)

lemma consistent_medial_t2'_2: "consistent (medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> (Guard t2'))"
  apply (simp add: t2'_def consistent_def del: One_nat_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num n, I 1 := Num 50>" in exI)
  apply (simp del: One_nat_def)
  by (simp add: consistent_empty_4)

lemma posterior_t2'_2: "posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n), V (I 1) \<mapsto> cexp.Eq (Num 50)\<rbrakk> t2' = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> Eq (Num (n+50))\<rbrakk>"
  apply (simp add: posterior_def consistent_medial_t2' del: Nat.One_nat_def)
  apply (simp add: t2'_def compose_plus_n_50 del: Nat.One_nat_def compose_plus.simps)
  apply (rule ext)
  by simp

lemma posterior_t2': "(posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num n)\<rbrakk> t2') = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> Bc True\<rbrakk>"
  apply (simp add: posterior_def consistent_medial_t2'_2 del: Nat.One_nat_def)
  apply (simp add: t2'_def compose_plus_n_50 valid_def satisfiable_def del: Nat.One_nat_def)
  apply (rule ext)
  by simp

(* t2' subsumes t2 no matter how many times it is looped round *)
lemma "subsumes \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> Eq (Num n)\<rbrakk> t2' t2"
  apply (simp only: subsumes_def)
  apply safe
     apply (simp add: t2'_def t2_def)
  apply (simp add: t2'_def t2_def)
   apply (simp add: t2_posterior del: Nat.One_nat_def)
   apply (simp add: medial_t2 posterior_t2'_2 del: Nat.One_nat_def)
   apply auto[1]
  apply (simp add: posterior_t2' del: Nat.One_nat_def)
  apply (simp add: consistent_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num 0>" in exI)
  apply simp
  by (simp add: consistent_empty_4)
end