subsection{*Generalisation*}
text{*This theory presents a simple EFSM definition and uses contexts to prove
transition subsumption. 
*}
theory Generalisation
imports "../Contexts" "../examples/Drinks_Machine_2"
begin

definition select :: "transition" where
"select \<equiv> \<lparr>
        Label = (STR ''select''),
        Arity = 1,
        Guard = [(gexp.Eq (V (I 1)) (L (Str ''coke'')))],
        Outputs = [],
        Updates = []
      \<rparr>"

definition coin50 :: "transition" where
"coin50 \<equiv> \<lparr>
        Label = (STR ''coin''),
        Arity = 1,
        Guard = [(gexp.Eq (V (I 1)) (L (Num 50)))],
        Outputs = [],
        Updates = []
      \<rparr>"

lemma guard_coin50: "Guard coin50 = [(gexp.Eq (V (I 1)) (L (Num 50)))]"
  by (simp add: coin50_def)

definition coin_init :: "transition" where
"coin_init \<equiv> \<lparr>
        Label = (STR ''coin''),
        Arity = 1,
        Guard = [],
        Outputs = [],
        Updates = [(R 1, (V (I 1)))]
      \<rparr>"

lemma guard_coin_init: "Guard coin_init = []"
  by (simp add: coin_init_def)

definition coin_inc :: "transition" where
"coin_inc \<equiv> \<lparr>
        Label = (STR ''coin''),
        Arity = 1,
        Guard = [],
        Outputs = [],
        Updates = [(R 1, (Plus (V (R 1)) (V (I 1))))]
      \<rparr>"

definition vends :: "transition" where
"vends \<equiv> \<lparr>
        Label = (STR ''vend''),
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
        Label = (STR ''vend''),
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
        Label = (STR ''vend''),
        Arity = 0,
        Guard = [],
        Outputs =  [],
        Updates = []
      \<rparr>"

definition venderr_g :: "transition" where
"venderr_g \<equiv> \<lparr>
        Label = (STR ''vend''),
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

lemmas transitions = select_def coin_init_def vends_g_def venderr_g_def coin_inc_def coin50_def vends_def

lemma posterior_coin_init_r1_r2_true: "posterior r1_r2_true coin_init = r1_r2_true"
  apply (simp add: posterior_def posterior_separate_def coin_init_def medial_empty consistent_r1_r2_true)
  apply (simp add: remove_obsolete_constraints_def r1_r2_true_def)
  apply (rule ext)
  by (simp add: r1_r2_true_def)

lemma medial_coin50: "medial \<lbrakk>\<rbrakk> (Guard coin50) = \<lbrakk>V (I 1) \<mapsto> {|Eq (Num 50), Bc True|}\<rbrakk>"
  apply (simp add: coin50_def medial_def pairs2context_def List.maps_def)
  apply (rule ext)
  by simp

lemma consistent_medial_coin50: "consistent (medial \<lbrakk>\<rbrakk> (Guard coin50))"
  apply (simp add: consistent_def medial_coin50 cval_true)
  apply (rule_tac x="<I 1 := Num 50>" in exI)
  apply (simp add: cval_def gval.simps ValueEq_def)
  apply (rule allI)
  apply (case_tac r)
     apply (simp add: gval.simps)
    apply (case_tac x2)
  by (simp_all add: gval.simps ValueEq_def)

lemma posterior_empty_coin50: "(posterior \<lbrakk>\<rbrakk> coin50) = \<lbrakk>\<rbrakk>"
  apply (simp add: posterior_def posterior_separate_def Let_def consistent_medial_coin50)
  by (simp add: coin50_def)

lemma posterior_empty_coin_init: "posterior \<lbrakk>\<rbrakk> coin_init = \<lbrakk>V (R 1) \<mapsto> {|Bc True|}\<rbrakk>"
  apply (rule ext)
  apply (simp add: posterior_def coin_init_def posterior_separate_def medial_empty)
  by (simp add: remove_obsolete_constraints_def)

lemma "subsumes coin_init empty coin50"
  apply (simp add: subsumes_def)
  apply (standard, simp add: coin50_def coin_init_def)+
   apply (simp add: medial_empty medial_def List.maps_def pairs2context_def)
  apply (standard, simp add: coin50_def coin_init_def)
  apply (standard, simp add: coin50_def coin_init_def)
  apply standard
   apply (simp add: posterior_separate_def Let_def coin_init_def consistent_medial_coin50 posterior_empty_coin50 remove_obsolete_constraints_def)
  apply (simp add: posterior_empty_coin50 posterior_empty_coin_init)
  apply (simp add: consistent_def)
  apply (rule_tac x="<>" in exI)
  by (simp add: cval_true consistent_empty_fball)

lemma posterior_empty_coin_inc: "posterior \<lbrakk>\<rbrakk> coin_inc = \<lbrakk>\<rbrakk>"
  apply (simp add: posterior_def coin_inc_def posterior_separate_def medial_empty fprod_singletons)
  apply (simp add: remove_obsolete_constraints_def)
  apply (rule ext)
  apply (case_tac a)
  by auto

lemma "subsumes coin_inc empty coin50"
  apply (simp add: subsumes_def)
  apply (standard, simp add: coin50_def coin_inc_def)+
   apply (simp add: medial_empty)
   apply (rule allI)+
  using consistent_empty_fball guard_coin50 medial_coin50 apply auto[1]
  apply standard
   apply (simp add: coin50_def coin_inc_def)
  apply standard
   apply (simp add: coin50_def coin_inc_def)
  apply standard
   apply (simp add: coin_inc_def  posterior_empty_coin50)
   apply (simp add: posterior_separate_def Let_def consistent_medial_coin50)
   apply (simp add: remove_obsolete_constraints_def)
  by (simp add: posterior_empty_coin50 posterior_empty_coin_inc)

lemma posterior_select: "posterior \<lbrakk>\<rbrakk> Generalisation.select = \<lbrakk>\<rbrakk>"
proof-
  have medial_select: "medial \<lbrakk>\<rbrakk> (Guard Generalisation.select) = \<lbrakk>V (I 1) \<mapsto> {|Eq (Str ''coke''), Bc True|}\<rbrakk>"
    apply (rule ext)
    by (simp add: medial_def List.maps_def pairs2context_def select_def)
  have consistent_medial_select: "consistent (medial \<lbrakk>\<rbrakk> (Guard Generalisation.select))"
    apply (simp add: medial_select consistent_def)
    apply (rule_tac x="<I 1 := Str ''coke''>" in exI)
    apply (simp add: cval_def gval.simps ValueEq_def)
    apply (rule allI)
    apply (case_tac r)
       apply (simp add: gval.simps)
      apply (case_tac x2)
       apply (simp add: gval.simps)
    apply (simp add: gval.simps ValueEq_def)
    by (simp_all add: gval.simps)
  show ?thesis
    apply (simp add: posterior_def posterior_separate_def consistent_medial_select Let_def)
    by (simp add: select_def)
qed

lemma posterior_empty_vends_g: "posterior \<lbrakk>\<rbrakk> vends_g = (\<lambda>i. {|Bc False|})"
proof-
  have inconsistent_medial: "\<not>consistent (medial \<lbrakk>\<rbrakk> [Ge (V (R 1)) (L (Num 100))])"
    apply (simp add: medial_def List.maps_def pairs2context_def consistent_def)
    apply (rule allI)
    apply (rule_tac x="V (R 1)" in exI)
    by (simp add: cval_def gval.simps ValueGt_def ValueEq_def)
  show ?thesis
    by (simp add: posterior_def posterior_separate_def Let_def inconsistent_medial)
qed

lemma posterior_empty_vends: "posterior \<lbrakk>\<rbrakk> vends = \<lbrakk>\<rbrakk>"
  by (simp add: vends_def posterior_def posterior_separate_def  medial_empty)

lemma "\<not> subsumes vends_g empty vends"
  by (simp add: subsumes_def posterior_empty_vends posterior_empty_vends_g inconsistent_false)

lemma "subsumes vends_g \<lbrakk>V (R 1) \<mapsto> {|Geq (Num 100)|}\<rbrakk> vends"
proof-
  have consistent: "consistent (\<lambda>r. if r = V (R 1) then {|Geq (Num 100)|} else \<lbrakk>\<rbrakk> r)"
    apply (simp add: consistent_def)
    apply (rule_tac x="<R 1 := Num 100>" in exI)
    apply (simp add: cval_def gval.simps ValueGt_def)
    apply (rule allI)
    apply (case_tac r)
       apply (simp add: gval.simps)
      apply (case_tac x2)
       apply (simp add: gval.simps)
    by (simp_all add: gval.simps ValueEq_def)
  have consistent2: "consistent
        (\<lambda>r. (if r = V (R 1) then {|Geq (Num 100)|} else \<lbrakk>\<rbrakk> r) |\<union>|
             fold (|\<union>|)
              (map snd
                (if V (R 1) = r then (V (R 1), {|Geq (Num 100)|}) # filter (\<lambda>(a, uu). a = r) [(V (R 1), {|Geq (Num 100)|})]
                 else filter (\<lambda>(a, uu). a = r) [(V (R 1), {|Geq (Num 100)|})]))
              {||})"
    apply (simp add: consistent_def)
    apply (rule_tac x="<R 1 := Num 1000>" in exI)
    apply (simp add: cval_def gval.simps ValueGt_def)
    apply (rule allI)
    apply (case_tac r)
       apply (simp add: gval.simps)
      apply (case_tac x2)
       apply (simp add: gval.simps)
    by (simp_all add: gval.simps ValueEq_def)
  show ?thesis
  apply (simp add: subsumes_def)
  apply (standard, simp add: vends_def vends_g_def)+
  apply standard
   apply (simp add: medial_def List.maps_def pairs2context_def)
  apply standard
   apply (simp add: vends_g_def posterior_def vends_def)
   apply (simp add: posterior_separate_def Let_def medial_def List.maps_def pairs2context_def cval_false)
     apply (simp add: consistent)
    apply (simp add: posterior_def vends_g_def posterior_separate_def Let_def)
    by (simp add:  medial_def List.maps_def pairs2context_def consistent inconsistent_false consistent2)
qed

definition test1 :: transition where
"test1 \<equiv> \<lparr>
        Label = (STR ''foo''),
        Arity = 1,
        Guard = [(gexp.Eq (V (I 1)) (L (Num 6)))],
        Outputs =  [(L (Num 6))],
        Updates = [(R 1, (L (Num 6)))]
      \<rparr>"

definition test2 :: transition where
"test2 \<equiv> \<lparr>
        Label = (STR ''foo''),
        Arity = 1,
        Guard = [(gexp.Gt (V (I 1)) (L (Num 0)))],
        Outputs =  [(V (I 1))],
        Updates = [(R 1, (V (I 1)))]
      \<rparr>"

lemma consistent_medial_test1: "consistent (medial empty (Guard test1))"
  apply (simp add: medial_def List.maps_def test1_def pairs2context_def consistent_def)
  apply (rule_tac x="< I 1 := (Num 6)>" in exI)
  apply (rule allI)
  apply (case_tac r)
     apply (simp add: cval_true)
    apply (case_tac x2)
  by (simp add: cval_def gval.simps ValueEq_def)+

lemma posterior_test1: "posterior \<lbrakk>\<rbrakk> test1 = \<lbrakk>V (R 1) \<mapsto> {|Eq (Num 6)|}\<rbrakk>"
  apply (simp add: posterior_def posterior_separate_def Let_def consistent_medial_test1)
  apply (simp add: test1_def remove_obsolete_constraints_def)
  apply (rule ext)
  by simp

lemma posterior_separate_test2: "posterior_separate \<lbrakk>\<rbrakk> (Guard test1 @ Guard test2) (Updates test2) = \<lbrakk>V (R 1) \<mapsto> {|Eq (Num 6), Gt (Num 0), Bc True|}\<rbrakk>"
proof-
  have consistent: "consistent (medial \<lbrakk>\<rbrakk> [gexp.Eq (V (I 1)) (L (Num 6)), GExp.Lt (L (Num 0)) (V (I 1))])"
    apply (simp add: medial_def pairs2context_def List.maps_def consistent_def)
    apply (rule_tac x="<I 1 := Num 6>" in exI)
    apply (rule allI)
    apply (simp add: cval_def gval.simps ValueEq_def ValueGt_def)
    apply (case_tac r)
       apply (simp add: gval.simps)
      apply (case_tac x2)
       apply (simp add: gval.simps)
    by (simp add: gval.simps ValueEq_def)+
  show ?thesis
    apply (simp add: posterior_separate_def test1_def test2_def Let_def consistent)
    apply (simp add: remove_obsolete_constraints_def)
    apply (rule ext)
    apply simp
    apply (case_tac a)
       apply simp
    apply (case_tac x2)
       apply simp
    apply (simp add: medial_def pairs2context_def List.maps_def consistent_def)
     apply simp
    by simp
qed

lemma consistent_posterior_test2: "consistent (posterior \<lbrakk>\<rbrakk> test2)"
proof-
  have consistent: "consistent (medial \<lbrakk>\<rbrakk> (Guard test2))"
    apply (simp add: medial_def pairs2context_def List.maps_def consistent_def test2_def)
    apply (rule_tac x="<I 1 := Num 6>" in exI)
    apply (rule allI)
    apply (simp add: cval_def gval.simps ValueEq_def ValueGt_def)
    apply (case_tac r)
       apply (simp add: gval.simps)
      apply (case_tac x2)
       apply (simp add: gval.simps)
    by (simp add: gval.simps ValueEq_def)+
  show ?thesis
    apply (simp add: posterior_def posterior_separate_def Let_def consistent)
    apply (simp add: test2_def consistent_def remove_obsolete_constraints_def)
    apply (rule_tac x="<R 1 := Num 6>" in exI)
    apply (rule allI)
    apply (simp add: medial_def pairs2context_def List.maps_def consistent_def test2_def)
    apply (simp add: cval_def gval.simps ValueEq_def ValueGt_def)
    apply (case_tac r)
       apply (simp add: gval.simps)
      apply (case_tac x2)
    by (simp add: gval.simps ValueEq_def)+
qed

lemma test2_subsumes_test1: "subsumes test2 \<lbrakk>\<rbrakk> test1"
proof-
  show ?thesis
    apply (simp add: subsumes_def)
    apply (standard, simp add: test1_def test2_def)+
     apply (simp add: medial_def List.maps_def pairs2context_def cval_def gval.simps ValueEq_def ValueGt_def)
    apply standard
     apply (simp add: test1_def test2_def gval.simps ValueEq_def)
    apply standard
     apply (simp add: test1_def test2_def)
     apply (metis input2state.simps(2))
    apply standard
     apply (simp add: posterior_test1 posterior_separate_test2)
    by (simp add: consistent_posterior_test2)
qed

end