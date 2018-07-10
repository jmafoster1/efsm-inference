theory Generalisation
imports Contexts drinks_machine2
begin
definition select :: "transition" where
"select \<equiv> \<lparr>
        Label = ''select'',
        Arity = 1,
        Guard = [(gexp.Eq (V (I 1)) (N 1))],
        Outputs = [],
        Updates = []
      \<rparr>"

definition coin50 :: "transition" where
"coin50 \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [(gexp.Eq (V (I 1)) (N 50))],
        Outputs = [],
        Updates = []
      \<rparr>"

definition coin_init :: "transition" where
"coin_init \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [],
        Outputs = [],
        Updates = [(R 1, (V (I 1)))]
      \<rparr>"

definition coin_inc :: "transition" where
"coin_inc \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [],
        Outputs = [],
        Updates = [(R 1, (Plus (V (R 1)) (V (I 1))))]
      \<rparr>"

definition vends :: "transition" where
"vends \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [],
        Outputs =  [(N 1)],
        Updates = []
      \<rparr>"

definition vends_g :: "transition" where
"vends_g \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [(Ge (V (R 1)) (N 100))],
        Outputs =  [(N 1)],
        Updates = []
      \<rparr>"

definition venderr :: "transition" where
"venderr \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [],
        Outputs =  [],
        Updates = []
      \<rparr>"

definition venderr_g :: "transition" where
"venderr_g \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [(gexp.Lt (V (R 1)) (N 100))],
        Outputs =  [(N 1)],
        Updates = []
      \<rparr>"

definition vend :: "efsm" where
"vend \<equiv> \<lparr> 
          S = [1,2,3,4,5],
          s0 = 1,
          T = \<lambda> (a,b) .
              if (a,b) = (1,2) then [select] 
              else if (a,b) = (2,3) then [coin50]
              else if (a,b) = (3,3) then [venderr]
              else if (a,b) = (3,4) then [coin50]
              else if (a,b) = (4,5) then [vends]
              else [] (* There are no other transitions *)
         \<rparr>"

definition vend_g :: "efsm" where
"vend_g \<equiv> \<lparr> 
          S = [1,2,3,4],
          s0 = 1,
          T = \<lambda> (a,b) .
              if (a,b) = (1,2) then [select] 
              else if (a,b) = (2,3) then [coin_init]
              else if (a,b) = (3,3) then [venderr_g, coin_inc]
              else if (a,b) = (3,4) then [vends_g]
              else [] (* There are no other transitions *)
         \<rparr>"

lemma "posterior r1_r2_true coin_init = \<lbrakk>(V (R 1)) \<mapsto> Bc True\<rbrakk>"
  apply (rule ext)
  apply (simp add: coin_init_def posterior_def consistent_def)
  using empty_not_undef gval.simps(1) by force
  

lemma posterior_empty_coin_inc_not_consistent: "\<not> consistent (posterior empty coin_inc)"
  apply (simp add: posterior_def coin_inc_def valid_def satisfiable_def)
  apply (simp add: consistent_def)
  apply (rule allI)
  apply (rule_tac x="V (R 1)" in exI)
  by simp

lemma posterior_empty_coin_inc: "(posterior empty coin_inc) = (\<lambda>r. if r = V (R 1) then cexp.Bc False else Contexts.empty r)"
  by (simp add: posterior_def coin_inc_def satisfiable_def)

lemma foo: "\<not> (\<forall>s. \<exists>r. (r = V (I 1) \<longrightarrow> s (I 1) \<noteq> 50) \<and>
             (r \<noteq> V (I 1) \<longrightarrow> and (Contexts.empty r) (cexp.Bc True) \<noteq> Undef \<and> \<not> gval (cexp2gexp r (and (Contexts.empty r) (cexp.Bc True))) s))"
  apply simp
  using consistent_empty_1 by force

lemma empty_neq_false: "(\<lambda>i. cexp.Bc False) \<noteq> Contexts.empty"
  by (metis empty_never_false)

lemma posterior_empty_coin50: "(posterior \<lbrakk>\<rbrakk> coin50) = \<lbrakk>\<rbrakk>"
  apply (simp add: posterior_def coin50_def satisfiable_def consistent_def empty_neq_false)
  using empty_not_undef by force

lemma posterior_empty_coin_init: "posterior \<lbrakk>\<rbrakk> coin_init = \<lbrakk>V (R 1) \<mapsto> Bc True\<rbrakk>"
  apply (rule ext)
  by (simp add: posterior_def coin_init_def)

lemma "subsumes empty coin_init coin50"
  apply (simp add: subsumes_def)
  apply safe
     apply (simp add: coin50_def coin_init_def)
    apply (simp add: coin50_def coin_init_def)
   apply (simp add: posterior_empty_coin50 posterior_empty_coin_init empty_not_undef)
  apply (simp add: posterior_empty_coin50 posterior_empty_coin_init consistent_def)
  apply (rule_tac x="<>" in exI)
  using empty_not_undef by force

lemma "\<not> subsumes empty coin_inc coin50"
  by (simp add: subsumes_def posterior_empty_coin50 posterior_empty_coin_inc_not_consistent)

lemma posterior_coin_inc_r1_true: "posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True\<rbrakk> coin_inc = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True\<rbrakk>"
  apply (simp add: posterior_def coin_inc_def consistent_def valid_def satisfiable_def)
  apply safe
   apply auto[1]
  using consistent_empty_1 by fastforce

lemma posterior_coin50_true: "posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True\<rbrakk> coin50 = \<lbrakk>\<rbrakk>"
  apply (simp add: posterior_def coin50_def consistent_def empty_neq_false)
  using empty_not_undef by force

lemma medial_coin50: "medial \<lbrakk>V (R (Suc 0)) \<mapsto> cexp.Bc True\<rbrakk> (Guard coin50) = \<lbrakk>V (R (Suc 0)) \<mapsto> cexp.Bc True, V (I 1) \<mapsto> Eq 50\<rbrakk>"
  apply (simp add: coin50_def)
  apply (rule ext)
  by simp

lemma sucZero: "Suc 0 = 1"
  by simp

lemma "subsumes \<lbrakk>V (R 1) \<mapsto> Bc True\<rbrakk> coin_inc coin50"
  apply (simp add: subsumes_def)
  apply safe
     apply (simp add: coin50_def coin_inc_def)
    apply (simp add: coin50_def coin_inc_def)
   apply (simp only: sucZero posterior_coin50_true)
  using consistent_empty_1 apply force
   apply (simp only: sucZero posterior_coin_inc_r1_true consistent_def)
  apply (rule_tac x="<>" in exI)
  by (simp add: consistent_empty_4)

lemma "(posterior_sequence [coin_init, coin_inc] empty) = \<lbrakk>V (R 1) \<mapsto> Bc True\<rbrakk>"
  apply (simp add: posterior_sequence_def posterior_def coin_init_def coin_inc_def satisfiable_def valid_def consistent_def)
  using consistent_def consistent_empty_1 consistent_empty_3 by auto

lemma "\<not> subsumes empty vends_g vends"
  apply (simp add: subsumes_def vends_g_def vends_def posterior_def)
  apply (simp add: consistent_def)
  by auto

lemma posterior_vends_g: "posterior \<lbrakk>V (R 1) \<mapsto> Geq 100\<rbrakk> vends_g =  \<lbrakk>\<rbrakk>"
  apply (simp add: posterior_def consistent_def vends_g_def)
  using consistent_empty_1 by fastforce

lemma posterior_vends: "posterior \<lbrakk>V (R 1) \<mapsto> Geq 100\<rbrakk> vends = \<lbrakk>\<rbrakk>"
  apply (simp add: posterior_def consistent_def vends_def)
  using consistent_empty_1 by fastforce

lemma medial_vends: "medial \<lbrakk>V (R 1) \<mapsto> Geq 100\<rbrakk> (Guard vends) = \<lbrakk>V (R 1) \<mapsto> Geq 100\<rbrakk>"
  by (simp add: vends_def)

lemma "subsumes \<lbrakk>V (R 1) \<mapsto> Geq 100\<rbrakk> vends_g vends"
  apply (simp only: subsumes_def)
  apply safe
  apply (simp add: vends_def vends_g_def)
     apply auto[1]
    apply (simp add: vends_def vends_g_def)
   apply (simp add: medial_vends posterior_vends)
   apply (simp only: sucZero posterior_vends)
  apply (simp add: empty_not_undef)
  by (simp only: sucZero posterior_vends posterior_vends_g)

definition test1 :: transition where
"test1 \<equiv> \<lparr>
        Label = ''foo'',
        Arity = 1,
        Guard = [(gexp.Eq (V (I 1)) (N 6))],
        Outputs =  [(N 6)],
        Updates = [(R 1, (N 6))]
      \<rparr>"

definition test2 :: transition where
"test2 \<equiv> \<lparr>
        Label = ''foo'',
        Arity = 1,
        Guard = [(gexp.Gt (V (I 1)) (N 0))],
        Outputs =  [(V (I 1))],
        Updates = [(R 1, (V (I 1)))]
      \<rparr>"

lemma medial_test1: "medial empty (Guard test1) = (\<lambda>i. if i = V (I 1) then Eq 6 else empty i)"
  apply (simp add: test1_def)
  apply (rule ext)
  by auto

lemma consistent_medial_test1: "consistent (medial empty (Guard test1))"
  apply (simp add: medial_test1 consistent_def)
  apply (rule_tac x="<I 1 := 6>" in exI)
  apply simp
  by (simp add: consistent_empty_4)

lemma medial_test2: "medial empty (Guard test2) = (\<lambda>i. if i = V (I 1) then Gt 0 else empty i)"
  apply (simp add: test2_def)
  apply (rule ext)
  by auto

lemma test2_subsumes_test1_aux1: "let c' = medial (\<lambda>i. if i = V (I 1) then cexp.Eq 6 else \<lbrakk>\<rbrakk> i) (Guard test2)
                   in consistent c'"
  apply (simp add: test2_def consistent_def)
  apply (rule_tac x="<I 1 := 6>" in exI)
  by (simp add: consistent_empty_4)

lemma posterior_test1: "posterior \<lbrakk>\<rbrakk> test1 = \<lbrakk>V (R 1) \<mapsto> Eq 6\<rbrakk>"
  apply (simp add: posterior_def consistent_medial_test1)
  apply (simp add: medial_test1 test1_def)
  apply (rule ext)
  by simp

lemma posterior_test2: "(posterior \<lbrakk>\<rbrakk> test2) = \<lbrakk>V (R 1) \<mapsto> Gt 0\<rbrakk>"
  apply (simp add: posterior_def test2_def consistent_def)
  apply safe
   apply auto[1]
  using consistent_empty_4 zero_less_numeral by blast

lemma medial_test2_2: "medial (\<lambda>i. if i = V (I 1) then cexp.Eq 6 else \<lbrakk>\<rbrakk> i) (Guard test2) = \<lbrakk>V (I 1) \<mapsto> And (cexp.Eq 6) (cexp.Gt 0)\<rbrakk>"
  apply (simp add: test2_def)
  apply (rule ext)
  by (simp)

lemma consistent_medial_test2:"consistent\<lbrakk>V (I (Suc 0)) \<mapsto> And (cexp.Eq 6) (cexp.Gt 0)\<rbrakk>"
  apply (simp add: consistent_def)
  apply (rule_tac x="<I 1 := 6>" in exI, simp)
  by (simp add: consistent_empty_4)

lemma posterior_test2_2: "posterior (\<lambda>i. if i = V (I 1) then cexp.Eq 6 else \<lbrakk>\<rbrakk> i) test2 = \<lbrakk>V (R 1) \<mapsto> And (cexp.Eq 6) (cexp.Gt 0)\<rbrakk>"
  apply (simp add: posterior_def)
  apply (simp only: sucZero medial_test2_2 )
  apply (simp add: consistent_medial_test2)
  apply (simp add: test2_def)
  apply (rule ext)
  by simp

lemma test2_subsumes_test1_aux2: "consistent (posterior \<lbrakk>\<rbrakk> test2)"
  apply (simp add: posterior_test2 consistent_def)
  apply (rule_tac x="<R 1 := 1>" in exI)
  by (simp add: consistent_empty_4)

lemma test2_subsumes_test1: "subsumes \<lbrakk>\<rbrakk> test2 test1"
  apply (simp only: subsumes_def)
  apply safe
     apply (simp add: medial_test1 medial_test2)
     apply auto[1]
    apply (simp add: test1_def test2_def)
   apply (simp only: medial_test1 posterior_test2_2 posterior_test1)
   apply auto[1]
  by (simp add: test2_subsumes_test1_aux2)
end