theory Increment_Reset
  imports "../Inference" "../Enable_Logging"
begin

definition initialiseReg :: "transition \<Rightarrow> vname \<Rightarrow> transition" where
  "initialiseReg t newReg = \<lparr>Label = Label t, Arity = Arity t, Guard = Guard t, Outputs = Outputs t, Updates = ((newReg, L (Num 0))#Updates t)\<rparr>"

definition "guardMatch t1 t2  = (\<exists>n n'. Guard t1 = [gexp.Eq (V (I 1)) (L (Num n))] \<and> Guard t2 = [gexp.Eq (V (I 1)) (L (Num n'))])"
definition "outputMatch t1 t2 = (\<exists>m m'. Outputs t1 = [L (Num m)] \<and> Outputs t2 = [L (Num m')])"

lemma guard_match_commute: "guardMatch t1 t2 = guardMatch t2 t1"
  apply (simp add: guardMatch_def)
  by auto

lemma guard_match_length: "length (Guard t1) \<noteq> 1 \<or> length (Guard t2) \<noteq> 1 \<Longrightarrow> \<not> guardMatch t1 t2"
  apply (simp add: guardMatch_def)
  by auto

fun insert_increment :: update_modifier where
  "insert_increment t1ID t2ID s new old = (let
     t1 = get_by_id new t1ID;
     t2 = get_by_id new t2ID in
     if guardMatch t1 t2 \<and> outputMatch t1 t2 then let 
          r = max_reg new + 1;
          newReg = R r;
          newT1 = \<lparr>Label = Label t1, Arity = Arity t1, Guard = [], Outputs = [Plus (V newReg) (V (I 1))], Updates=((newReg, Plus (V newReg) (V (I 1)))#Updates t1)\<rparr>;
          newT2 = \<lparr>Label = Label t2, Arity = Arity t2, Guard = [], Outputs = [Plus (V newReg) (V (I 1))], Updates=((newReg, Plus (V newReg) (V (I 1)))#Updates t2)\<rparr>;
          initialised = fimage (\<lambda>(uid, (from, to), t). (uid, (from, to), (if (to = dest t1ID new \<or> to = dest t2ID new) \<and> t \<noteq> t1 \<and> t \<noteq> t2 then initialiseReg t newReg else t))) new;
          newEFSM = (replaceAll (replaceAll initialised t2 newT2) t1 newT1)
          in 
          resolve_nondeterminism (sorted_list_of_fset (nondeterministic_pairs newEFSM)) old newEFSM null_modifier (\<lambda>a. True)
     else
       None
     )"

definition struct_replace_all :: "iEFSM \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> iEFSM" where
  "struct_replace_all e old new = fimage (\<lambda>(uid, (from, dest), t). if same_structure t old then (uid, (from, dest), new) else (uid, (from, dest), t)) e"

lemma output_match_symmetry: "(outputMatch t1 t2) = (outputMatch t2 t1)"
  apply (simp add: outputMatch_def)
  by auto

lemma guard_match_symmetry: "(guardMatch t1 t2) = (guardMatch t2 t1)"
  apply (simp add: guardMatch_def)
  by auto

fun insert_increment_2 :: update_modifier where
  "insert_increment_2 t1ID t2ID s new old = (let
     t1 = get_by_id new t1ID;
     t2 = get_by_id new t2ID in
     if guardMatch t1 t2 \<and> outputMatch t1 t2 then let 
          r = max_reg new + 1;
          newReg = R r;
          newT1 = \<lparr>Label = Label t1, Arity = Arity t1, Guard = [], Outputs = [Plus (V newReg) (V (I 1))], Updates=((newReg, Plus (V newReg) (V (I 1)))#Updates t1)\<rparr>;
          newT2 = \<lparr>Label = Label t2, Arity = Arity t2, Guard = [], Outputs = [Plus (V newReg) (V (I 1))], Updates=((newReg, Plus (V newReg) (V (I 1)))#Updates t2)\<rparr>;
          initialised = fimage (\<lambda>(uid, (from, to), t). (uid, (from, to), (if (to = dest t1ID new \<or> to = dest t2ID new) \<and> t \<noteq> t1 \<and> t \<noteq> t2 then initialiseReg t newReg else t))) new ;
          newEFSM = (struct_replace_all (struct_replace_all initialised t2 newT2) t1 newT1)
          in 
          resolve_nondeterminism (sorted_list_of_fset (nondeterministic_pairs newEFSM)) old newEFSM null_modifier (\<lambda>a. True)
     else
       None
     )"

fun guardMatch_alt_2 :: "gexp list \<Rightarrow> bool" where
  "guardMatch_alt_2 [(gexp.Eq (V (I i)) (L (Num n)))] = (i = 1)" |
  "guardMatch_alt_2 _ = False"

fun outputMatch_alt_2 :: "aexp list \<Rightarrow> bool" where
  "outputMatch_alt_2 [(L (Num n))] = True" |
  "outputMatch_alt_2 _ = False"

end