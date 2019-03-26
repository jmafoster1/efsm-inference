theory Increment_Reset
  imports Inference
begin

definition initialiseReg :: "transition \<Rightarrow> vname \<Rightarrow> transition" where
  "initialiseReg t newReg = \<lparr>Label = Label t, Arity = Arity t, Guard = Guard t, Outputs = Outputs t, Updates = ((newReg, L (Num 0))#Updates t)\<rparr>"

definition "guardMatch t1 t2  = (\<exists>n n'. Guard t1 = [gexp.Eq (V (I 1)) (L (Num n))] \<and> Guard t2 = [gexp.Eq (V (I 1)) (L (Num n'))])"
definition "outputMatch t1 t2 = (\<exists>m m'. Outputs t1 = [L (Num m)] \<and> Outputs t2 = [L (Num m')])"

definition drop_transition :: "iEFSM \<Rightarrow> nat \<Rightarrow> iEFSM" where
  "drop_transition e uid = ffilter (\<lambda>x. fst x \<noteq> uid) e"

fun insert_increment :: update_modifier where
  "insert_increment t1ID t2ID s new old = (let
     t1 = get_by_id new t1ID;
     t2 = get_by_id new t2ID in
     if guardMatch t1 t2 \<and> outputMatch t1 t2 then let 
          r = max_reg new + 1;
          newReg = R r;
          newT1 = \<lparr>Label = Label t1, Arity = Arity t1, Guard = [], Outputs = [Plus (V newReg) (V (I 1))], Updates=((newReg, Plus (V newReg) (V (I 1)))#Updates t1)\<rparr>;
          newT2 = \<lparr>Label = Label t2, Arity = Arity t2, Guard = [], Outputs = [Plus (V newReg) (V (I 1))], Updates=((newReg, Plus (V newReg) (V (I 1)))#Updates t2)\<rparr>;
          initialised = fimage (\<lambda>(uid, (from, to), t). (uid, (from, to), (if (to = dest t1ID new \<or> to = dest t2ID new) \<and> t \<noteq> t1 \<and> t \<noteq> t2 then initialiseReg t newReg else t))) new 
          in 
          Some (replaceAll (replaceAll initialised t2 newT2) t1 newT1)
     else
       None
     )"

end