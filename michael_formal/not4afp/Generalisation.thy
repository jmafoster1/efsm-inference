subsection{*Generalisation*}
text{*This theory presents a simple EFSM definition and uses contexts to prove
transition subsumption. 
*}
theory Generalisation
imports "../Contexts" "../examples/Drinks_Machine_2"
begin
declare One_nat_def[simp del]

definition select :: "transition" where
"select \<equiv> \<lparr>
        Label = ''select'',
        Arity = 1,
        Guard = [(gexp.Eq (V (I 1)) (L (Num 1)))],
        Outputs = [],
        Updates = []
      \<rparr>"

definition coin50 :: "transition" where
"coin50 \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [(gexp.Eq (V (I 1)) (L (Num 50)))],
        Outputs = [],
        Updates = []
      \<rparr>"

lemma guard_coin50: "Guard coin50 = [(gexp.Eq (V (I 1)) (L (Num 50)))]"
  by (simp add: coin50_def)

definition coin_init :: "transition" where
"coin_init \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [],
        Outputs = [],
        Updates = [(R 1, (V (I 1)))]
      \<rparr>"

lemma guard_coin_init: "Guard coin_init = []"
  by (simp add: coin_init_def)

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
        Outputs =  [L (Num 1)],
        Updates = []
      \<rparr>"

lemma outputs_vends [simp]: "Outputs vends = [L (Num 1)]"
  by (simp add: vends_def)

lemma guard_vends [simp]: "Guard vends = []"
  by (simp add: vends_def)

lemma updates_vends [simp]: "Updates vends = []"
  by (simp add: vends_def)

definition vends_g :: "transition" where
"vends_g \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [(Ge (V (R 1)) (L (Num 100)))],
        Outputs =  [L (Num 1)],
        Updates = []
      \<rparr>"

lemma outputs_vends_g [simp]: "Outputs vends_g = [L (Num 1)]"
  by (simp add: vends_g_def)

lemma guard_vends_g [simp]: "Guard vends_g = [(Ge (V (R 1)) (L (Num 100)))]"
  by (simp add: vends_g_def)

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
        Guard = [(GExp.Lt (V (R 1)) (L (Num 100)))],
        Outputs =  [L (Num 1)],
        Updates = []
      \<rparr>"

definition vend :: transition_matrix where
"vend \<equiv> {|
              ((0,1), select),
              ((1,2), coin50),
              ((2,2), venderr),
              ((2,3), coin50),
              ((3,4), vends)
         |}"

definition vend_g :: transition_matrix where
"vend_g \<equiv> {|
              ((0,1), select),
              ((1,2), coin_init),
              ((2,2), venderr_g),
              ((2,2), coin_inc),
              ((2,3), vends_g)
         |}"

lemma posterior_coin_init_r1_r2_true: "posterior r1_r2_true coin_init = r1_r2_true"
proof-
  show ?thesis
    unfolding posterior_def Let_def
    apply (simp add: consistent_r1_r2_true coin_init_def)
    apply (rule ext)
    by simp
qed

lemma posterior_empty_coin_inc_not_consistent: "\<not> consistent (posterior empty coin_inc)"
  apply (simp add: posterior_def coin_inc_def valid_def satisfiable_def)
  apply (simp add: consistent_def)
  apply (rule allI)
  apply (rule_tac x="V (R 1)" in exI)
  by simp

lemma posterior_empty_coin_inc: "(posterior empty coin_inc) = (\<lambda>r. if r = V (R 1) then cexp.Bc False else Contexts.empty r)"
  by (simp add: posterior_def coin_inc_def satisfiable_def)

lemma medial_coin50: "medial \<lbrakk>\<rbrakk> (Guard coin50) = \<lbrakk>V (I 1) \<mapsto> Eq (Num 50)\<rbrakk>"
  apply (simp add: coin50_def)
  apply (rule ext)
  by simp

lemma consistent_medial_coin50: "consistent (medial \<lbrakk>\<rbrakk> (Guard coin50))"
  apply (simp add: consistent_def medial_coin50)
  apply (rule_tac x="<I 1 := Num 50>" in exI)
  apply simp
  by (simp add: consistent_empty_4)

lemma posterior_empty_coin50: "(posterior \<lbrakk>\<rbrakk> coin50) = \<lbrakk>\<rbrakk>"
  apply (simp add: posterior_def consistent_medial_coin50)
  by (simp add: coin50_def)

lemma posterior_empty_coin_init: "posterior \<lbrakk>\<rbrakk> coin_init = \<lbrakk>V (R 1) \<mapsto> Bc True\<rbrakk>"
  apply (rule ext)
  by (simp add: posterior_def coin_init_def)

lemma "subsumes empty coin_init coin50"
  apply (simp add: subsumes_def)
  apply safe
     apply (simp add: guard_coin50 guard_coin_init)
     apply (case_tac r)
        apply simp
       apply simp
       apply (case_tac x2)
        apply simp
       apply simp
      apply simp
     apply simp
    apply (simp add: guard_coin50)
    apply (simp add: coin50_def coin_init_def)
   apply (simp add: posterior_empty_coin50)
   apply (case_tac r)
      apply simp
     apply simp
  apply (case_tac x2)
      apply simp
     apply simp
    apply simp
   apply simp
  apply (simp add: posterior_empty_coin_init posterior_empty_coin50)
  apply (simp add: consistent_def)
  using consistent_empty_4 by blast

lemma "\<not> subsumes empty coin_inc coin50"
  by (simp add: subsumes_def posterior_empty_coin50 posterior_empty_coin_inc_not_consistent)

lemma posterior_coin_inc_r1_true: "posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True\<rbrakk> coin_inc = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True\<rbrakk>"
proof-
  have consistent: "consistent \<lbrakk>V (R 1) \<mapsto> cexp.Bc True\<rbrakk>"
    apply (simp add: consistent_def)
    apply (rule_tac x="<>" in exI)
    by (simp add: consistent_empty_4)
  show ?thesis
    unfolding posterior_def Let_def
    apply (simp add: coin_inc_def consistent)
    apply (rule ext)
    by simp
qed

lemma consistent_medial_coin50_true: "consistent (medial \<lbrakk>V (R (Suc 0)) \<mapsto> cexp.Bc True\<rbrakk> (Guard coin50))"
  apply (simp add: coin50_def consistent_def)
  apply (rule_tac x="<I 1 := Num 50>" in exI)
  apply simp
  using consistent_empty_4 by auto

lemma posterior_coin50_true: "posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True\<rbrakk> coin50 = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True\<rbrakk>"
proof-
  have consistent_medial: "consistent (medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True\<rbrakk> (Guard coin50))"
    apply (simp add: coin50_def)
    unfolding consistent_def
    apply (rule_tac x="<I 1 := Num 50>" in exI)
    apply simp
    by (simp add: consistent_empty_4)
  show ?thesis
    unfolding posterior_def Let_def
    apply (simp add: consistent_medial)
    by (simp add: coin50_def)
qed

lemma "(posterior_sequence empty vend_g 0 <> [(''select'', [c]), (''coin'', [v1]), (''coin'', [v2])]) = \<lbrakk>V (R 1) \<mapsto> Bc True\<rbrakk>"
  apply (simp add: posterior_sequence_def posterior_def coin_init_def coin_inc_def satisfiable_def valid_def consistent_def)
  sorry

lemma not_consistent_medial_vends_g_empty: "\<not>consistent (\<lambda>r. and (\<lbrakk>\<rbrakk> r) (if r = V (R 1) then snd (V (R 1), (Geq (Num 100))) else cexp.Bc True))"
  apply (simp add: consistent_def)
  apply (rule allI)
  apply (rule_tac x="V (R 1)" in exI)
  apply simp
  apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some (Num 100)) (s (R (Suc 0)))")
   apply simp
  by simp

lemma posterior_empty_vends_g: "posterior \<lbrakk>\<rbrakk> vends_g = (\<lambda>i. Bc False)"
  by (simp add: posterior_def not_consistent_medial_vends_g_empty )

lemma posterior_empty_vends: "posterior \<lbrakk>\<rbrakk> vends = \<lbrakk>\<rbrakk>"
  by (simp add: posterior_def)

lemma "\<not> subsumes empty vends_g vends"
  apply (simp add: subsumes_def)
  apply (simp add: consistent_def posterior_empty_vends_g posterior_empty_vends)
  apply (rule_tac x="<>" in exI)
  apply (rule allI)
  apply (case_tac r)
     apply simp
    apply simp
    apply (case_tac x2)
     apply simp
    apply simp
   apply simp
  by simp

lemma consistent_medial_vends_g: "consistent (medial \<lbrakk>V (R 1) \<mapsto> Geq (Num 100)\<rbrakk> (Guard vends_g))"
  apply (simp add: vends_g_def consistent_def)
  apply (rule_tac x="<R 1 := Num 100>" in exI)
  by (simp add: consistent_empty_4)

lemma posterior_vends_g: "posterior \<lbrakk>V (R 1) \<mapsto> Geq (Num 100)\<rbrakk> vends_g =  \<lbrakk>\<rbrakk>"
  apply (simp add: posterior_def consistent_medial_vends_g del: guard_vends_g Nat.One_nat_def)
  by (simp add: vends_g_def)

lemma consistent_medial_vends: "consistent (medial \<lbrakk>V (R (Suc 0)) \<mapsto> Geq (Num 100)\<rbrakk> (Guard vends))"
  apply (simp add: vends_def consistent_def)
  apply (rule_tac x="<R 1 := Num 100>" in exI)
  by (simp add: consistent_empty_4)

lemma posterior_vends: "posterior \<lbrakk>V (R 1) \<mapsto> Geq (Num 100)\<rbrakk> vends = \<lbrakk>\<rbrakk>"
  by (simp add: posterior_def consistent_medial_vends del: guard_vends)

lemma medial_vends: "medial \<lbrakk>V (R 1) \<mapsto> Geq (Num 100)\<rbrakk> (Guard vends) = \<lbrakk>V (R 1) \<mapsto> Geq (Num 100)\<rbrakk>"
  by (simp add: vends_def)

lemma "subsumes \<lbrakk>V (R 1) \<mapsto> Geq (Num 100)\<rbrakk> vends_g vends"
  apply (simp only: subsumes_def)
  apply safe
  apply (simp add: vends_def vends_g_def)
     apply auto[1]
    apply (simp add: vends_def vends_g_def)
   apply (simp add: medial_vends posterior_vends)
  using posterior_vends_g apply auto[1]
  apply (simp only: posterior_vends_g)
  by simp

definition test1 :: transition where
"test1 \<equiv> \<lparr>
        Label = ''foo'',
        Arity = 1,
        Guard = [(gexp.Eq (V (I 1)) (L (Num 6)))],
        Outputs =  [(L (Num 6))],
        Updates = [(R 1, (L (Num 6)))]
      \<rparr>"

lemma guard_test1: "Guard test1 = [(gexp.Eq (V (I 1)) (L (Num 6)))]"
  by (simp add: test1_def)

definition test2 :: transition where
"test2 \<equiv> \<lparr>
        Label = ''foo'',
        Arity = 1,
        Guard = [(gexp.Gt (V (I 1)) (L (Num 0)))],
        Outputs =  [(V (I 1))],
        Updates = [(R 1, (V (I 1)))]
      \<rparr>"

lemma medial_test1: "medial empty (Guard test1) = (\<lambda>i. if i = V (I 1) then Eq (Num 6) else empty i)"
  apply (simp add: test1_def)
  apply (rule ext)
  by auto

lemma consistent_medial_test1: "consistent (medial empty (Guard test1))"
  apply (simp add: medial_test1 consistent_def)
  apply (rule_tac x="<I 1 := Num 6>" in exI)
  apply simp
  by (simp add: consistent_empty_4)

lemma medial_test2: "medial empty (Guard test2) = (\<lambda>i. if i = V (I 1) then Gt (Num 0) else empty i)"
  apply (simp add: test2_def)
  apply (rule ext)
  by auto

lemma test2_subsumes_test1_aux1: "let c' = medial (\<lambda>i. if i = V (I 1) then cexp.Eq (Num 6) else \<lbrakk>\<rbrakk> i) (Guard test2)
                   in consistent c'"
  apply (simp add: test2_def consistent_def)
  apply (rule_tac x="<I 1 := Num 6>" in exI)
  by (simp add: consistent_empty_4)

lemma posterior_test1: "posterior \<lbrakk>\<rbrakk> test1 = \<lbrakk>V (R 1) \<mapsto> Eq (Num 6)\<rbrakk>"
  apply (simp add: posterior_def consistent_medial_test1)
  apply (simp add: medial_test1 test1_def)
  apply (rule ext)
  by simp

lemma consistent_medial_test2: "consistent (medial \<lbrakk>\<rbrakk> (Guard test2))"
  apply (simp add: test2_def consistent_def)
  apply (rule_tac x="<I 1 := Num 6>" in exI)
  by (simp add: consistent_empty_4)

lemma posterior_test2: "(posterior \<lbrakk>\<rbrakk> test2) = \<lbrakk>V (R 1) \<mapsto> Gt (Num 0)\<rbrakk>"
  apply (simp add: posterior_def consistent_medial_test2)
  apply (simp add: test2_def)
  apply (rule ext)
  by simp

lemma medial_test2_2: "medial (\<lambda>i. if i = V (I 1) then cexp.Eq (Num 6) else \<lbrakk>\<rbrakk> i) (Guard test2) = \<lbrakk>V (I 1) \<mapsto> And (cexp.Eq (Num 6)) (cexp.Gt (Num 0))\<rbrakk>"
  apply (simp add: test2_def)
  apply (rule ext)
  by (simp)

lemma consistent_medial_test2_2:"consistent (medial (\<lambda>i. if i = V (I (Suc 0)) then cexp.Eq (Num 6) else \<lbrakk>\<rbrakk> i) (Guard test2))"
  apply (simp add: consistent_def test2_def)
  apply (rule_tac x="<I 1 := Num 6>" in exI, simp)
  by (simp add: consistent_empty_4)

lemma posterior_test2_2: "posterior (\<lambda>i. if i = V (I 1) then cexp.Eq (Num 6) else \<lbrakk>\<rbrakk> i) test2 = \<lbrakk>V (R 1) \<mapsto> And (cexp.Eq (Num 6)) (cexp.Gt (Num 0))\<rbrakk>"
  apply (simp add: posterior_def consistent_medial_test2_2)
  apply (simp add: test2_def)
  apply (rule ext)
  by simp

lemma test2_subsumes_test1_aux2: "consistent (posterior \<lbrakk>\<rbrakk> test2)"
  apply (simp add: posterior_test2 consistent_def)
  apply (rule_tac x="<R 1 := Num 1>" in exI)
  by (simp add: consistent_empty_4)

lemma test2_subsumes_test1: "subsumes \<lbrakk>\<rbrakk> test2 test1"
  apply (simp only: subsumes_def)
  apply safe
     apply (simp add: medial_test1 medial_test2)
     apply auto[1]
    apply (simp add: test1_def test2_def)
   apply (simp only: posterior_test1 medial_test1 posterior_test2_2)
   apply (simp del: One_nat_def)
   apply (case_tac "r = V (R 1)")
    apply simp
    apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some i) (Some (Num 0))")
     apply simp
    apply simp
   apply simp
  by (simp add: test2_subsumes_test1_aux2)
end
