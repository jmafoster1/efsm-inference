theory simple_drinks_machine
imports EFSM Contexts
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
        Guard = [(gexp.Eq (V ''i1'') (N 50))],
        Outputs = [(Plus (V ''r2'') (V ''i1''))],
        Updates = [(''r1'', (V ''r1'')),  (''r2'', Plus (V ''r2'') (N 50))]
      \<rparr>"

definition t2' :: "transition" where
"t2' \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [],
        Outputs = [(Plus (V ''r2'') (V ''i1''))],
        Updates = [
                  (''r1'', (V ''r1'')),
                  (''r2'', (Plus (V ''r2'') (V ''i1'')))
                ]
      \<rparr>"

definition t3 :: "transition" where
"t3 \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [(Ge (V ''r2'') (N 100))],
        Outputs =  [(V ''r1'')],
        Updates = [(''r1'', (V ''r1'')), (''r2'', (V ''r2''))]
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

lemma medial_t2: "medial \<lbrakk>V ''r1'' \<mapsto> cexp.Bc True, V ''r2'' \<mapsto> cexp.Eq 0\<rbrakk> (Guard t2) =  \<lbrakk>V ''r1'' \<mapsto> cexp.Bc True, V ''r2'' \<mapsto> cexp.Eq 0, V ''i1'' \<mapsto> Eq 50\<rbrakk>"
  apply (rule ext)
  by (simp add: t2_def)

lemma consistent_medial_t2: "consistent \<lbrakk>V ''r1'' \<mapsto> cexp.Bc True, V ''r2'' \<mapsto> cexp.Eq 0, V ''i1'' \<mapsto> cexp.Eq 50\<rbrakk>"
  apply (simp add: medial_t2 consistent_def)
  apply (rule_tac x="<''i1'' := 50>" in exI, simp)
  by (simp add: consistent_empty_4 null_state_def)

lemma medial_t2': "medial \<lbrakk>V ''r1'' \<mapsto> cexp.Bc True, V ''r2'' \<mapsto> cexp.Eq 0\<rbrakk> (Guard t2') =  \<lbrakk>V ''r1'' \<mapsto> cexp.Bc True, V ''r2'' \<mapsto> cexp.Eq 0\<rbrakk>"
  apply (rule ext)
  by (simp add: t2'_def)

lemma consistent_medial_t2': "consistent \<lbrakk>V ''r1'' \<mapsto> cexp.Bc True, V ''r2'' \<mapsto> cexp.Eq 0\<rbrakk>"
  apply (simp add: consistent_def)
  apply (rule_tac x="<''r2'' := 0>" in exI, simp)
  using consistent_empty_4 by blast

lemma guard_t2': "(Guard t2') = []"
  by (simp add: t2'_def)

lemma posterior_t2: "posterior \<lbrakk>V ''r1'' \<mapsto> cexp.Bc True, V ''r2'' \<mapsto> cexp.Eq 0\<rbrakk> t2 = \<lbrakk>V ''r1'' \<mapsto> cexp.Bc True, V ''r2'' \<mapsto> Eq 50\<rbrakk>"
  apply (simp add: posterior_def consistent_medial_t2 medial_t2)
  apply (simp add: t2_def valid_def satisfiable_def)
  apply safe
    apply presburger
   apply presburger
  by auto

lemma posterior_t2': "posterior \<lbrakk>V ''r1'' \<mapsto> cexp.Bc True, V ''r2'' \<mapsto> cexp.Eq 0, V ''i1'' \<mapsto> cexp.Eq 50\<rbrakk> t2' = \<lbrakk>V ''r1'' \<mapsto> cexp.Bc True, V ''r2'' \<mapsto> Eq 50\<rbrakk>"
  apply (simp add: posterior_def guard_t2')
  apply (insert medial_t2 consistent_medial_t2)
  apply (simp add: medial_t2 consistent_medial_t2)
  apply (simp add: t2'_def valid_def satisfiable_def)
  apply safe
    apply presburger
   apply presburger
  by auto

lemma t2'_subsumes_t2_aux1: "consistent (posterior \<lbrakk>V ''r1'' \<mapsto> cexp.Bc True, V ''r2'' \<mapsto> cexp.Eq 0\<rbrakk> t2')"
  apply (simp add: posterior_def guard_t2' consistent_medial_t2')
  apply (simp add: t2'_def valid_def satisfiable_def consistent_def)
  apply (rule_tac x="<>" in exI)
  by (simp add: consistent_empty_4)

lemma medial_t2_n: "medial \<lbrakk>V ''r1'' \<mapsto> cexp.Bc True, V ''r2'' \<mapsto> cexp.Eq n\<rbrakk> (Guard t2) = \<lbrakk>V ''r1'' \<mapsto> cexp.Bc True, V ''r2'' \<mapsto> cexp.Eq n, V ''i1'' \<mapsto> Eq 50\<rbrakk>"
  apply (rule ext)
  by (simp add: t2_def)

lemma consistent_medial_t2_n: "consistent \<lbrakk>V ''r1'' \<mapsto> cexp.Bc True, V ''r2'' \<mapsto> cexp.Eq n, V ''i1'' \<mapsto> cexp.Eq 50\<rbrakk>"
  apply (simp add: consistent_def)
  apply (rule_tac x="<''r2'' := n, ''i1'' := 50>" in exI, simp)
  using consistent_empty_4 by blast

lemma posterior_t2_n: "posterior \<lbrakk>V ''r1'' \<mapsto> cexp.Bc True, V ''r2'' \<mapsto> cexp.Eq n\<rbrakk> t2 = \<lbrakk>V ''r1'' \<mapsto> cexp.Bc True, V ''r2'' \<mapsto> cexp.Eq (n+50)\<rbrakk>"
  apply (simp add: posterior_def medial_t2_n consistent_medial_t2_n)
  apply (simp add: t2_def valid_def satisfiable_def)
  apply safe
  using zero_neq_numeral apply presburger
   apply presburger
  by auto

lemma consistent_medial_t2'_n: "consistent \<lbrakk>V ''r1'' \<mapsto> cexp.Bc True, V ''r2'' \<mapsto> cexp.Eq n\<rbrakk>"
  apply (simp add: consistent_def)
  apply (rule_tac x="<''r2'' := n, ''i1'' := 50>" in exI, simp)
  using consistent_empty_4 by blast

lemma posterior_t2'_n: "posterior \<lbrakk>V ''r1'' \<mapsto> cexp.Bc True, V ''r2'' \<mapsto> cexp.Eq n, V ''i1'' \<mapsto> cexp.Eq 50\<rbrakk> t2' =  \<lbrakk>V ''r1'' \<mapsto> Bc True, V ''r2'' \<mapsto> Eq (n+50)\<rbrakk>"
  apply (simp add: posterior_def guard_t2' consistent_medial_t2_n)
  apply (simp add: t2'_def valid_def satisfiable_def)
  apply safe
  using zero_neq_numeral apply presburger
   apply presburger
  by auto

lemma posterior_t2'_n2: "posterior \<lbrakk>V ''r1'' \<mapsto> cexp.Bc True, V ''r2'' \<mapsto> cexp.Eq n\<rbrakk> t2' = \<lbrakk>V ''r1'' \<mapsto> cexp.Bc True, V ''r2'' \<mapsto> Bc True\<rbrakk>"
  apply (simp add: posterior_def guard_t2' consistent_medial_t2'_n)
  apply (simp add: t2'_def valid_def satisfiable_def)
  by (rule ext, simp)

lemma consistent_posterior_t2': "consistent (posterior \<lbrakk>V ''r1'' \<mapsto> cexp.Bc True, V ''r2'' \<mapsto> cexp.Eq n\<rbrakk> t2')"
  apply (simp add: consistent_def posterior_t2'_n2)
  apply (rule_tac x="<>" in exI)
  by (simp add: consistent_empty_4)

(* t2' subsumes t2 no matter how many times it is looped round *)
lemma "subsumes \<lbrakk>V ''r1'' \<mapsto> Bc True, V ''r2'' \<mapsto> Eq n\<rbrakk> t2' t2"
  apply (simp only: subsumes_def)
  apply safe
     apply (simp add: guard_t2' medial_t2_n)
     apply (smt aexp.inject(2) aexp.simps(18) ceval.simps(2) ceval.simps(3) fun_upd_other fun_upd_same list.sel(1))
    apply (simp add: t2_def t2'_def)
   apply (simp add: medial_t2_n posterior_t2_n posterior_t2'_n)
  by (simp add: consistent_posterior_t2')
end