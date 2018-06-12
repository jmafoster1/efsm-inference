theory EFSM_LTL
imports Contexts EFSM Filesystem
begin

abbreviation neXt :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> event \<Rightarrow> (statename \<Rightarrow> event \<Rightarrow> registers \<Rightarrow> outputs \<Rightarrow> bool) \<Rightarrow> bool" where
  "neXt e s r h f \<equiv> (case step e s r (fst h) (snd h) of
      None \<Rightarrow> False |
      Some (s', o', r') \<Rightarrow> f s' h r' o'
    )"

primrec globally :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> outputs \<Rightarrow> trace \<Rightarrow> (statename \<Rightarrow> event \<Rightarrow> registers \<Rightarrow> outputs \<Rightarrow> bool) \<Rightarrow> bool" where
  "globally e s r p [] f = f s ('''', []) r p" |
  "globally e s r p (h#t) f = (case step e s r (fst h) (snd h) of
    None \<Rightarrow> False |
    Some (s', o', r') \<Rightarrow> conj (f s h r p) (globally e s' r' o' t f)
  )"

(*
noChangeOwner: THEOREM filesystem |- FORALL (user : UID): G(cfstate /= NULL_STATE) => 
G( 
  (label=write AND r_1=user AND ip_1_write_1/=accessDenied) => 
  G((cfstate=S_2 AND label=read AND r_1/=user) => 
    X(op_1_read_0 = accessDenied) 
  ) 
  );
*)

lemma state2: "e \<noteq> (''read'', []) \<Longrightarrow> e \<noteq> (''logout'', []) \<Longrightarrow> \<not> (fst e = ''write'' \<and> length (snd e) = 1) \<Longrightarrow> step filesystem 2 r (fst e) (snd e) = None"
  apply (simp add: fs_simp step_def)
  apply safe
                      apply simp_all
         apply (metis prod.collapse)
        apply (metis prod.collapse)
       apply (metis prod.collapse)
      apply (metis prod.collapse)
     apply (metis prod.collapse)
    apply (metis prod.collapse)
   apply (metis prod.collapse)
  by (metis prod.collapse)

lemma read_not_none [simp]: "step filesystem 2 r ''read'' [] \<noteq> None"
  by (simp add: fs_simp step_def)

lemma read_no_side_effects [simp]: "step filesystem 2 r ''read'' [] = Some (aa, aaa, b) \<Longrightarrow> b = r \<and> aa = 2"
  apply (simp add: fs_simp step_def)
  apply (case_tac "r ''r1'' = r ''r3''")
   apply simp
  apply (rule ext)
  by auto

 lemma "all (t) (\<lambda>e. e = (''read'', []) \<or> e = (''logout'', []) \<or> (fst e = ''write'' \<and> length (snd e) = 1)) \<Longrightarrow> 
 globally filesystem 2 r [] t (\<lambda>s e r p. (s = 2 \<and> fst e = ''write'' \<and> r ''r1'' = 1) \<longrightarrow>
  globally filesystem s' r' [] t (\<lambda>s e r p. (s = 2 \<and> fst e = ''read'' \<and> r ''r1'' \<noteq> 1)) \<longrightarrow>
    neXt filesystem s'' r'' (hd t') (\<lambda>s e r p. p = [0])
)"
proof (induction t)
  case Nil
  then show ?case by simp
next
  case (Cons a t')
  then show ?case
    apply (case_tac "a = (''read'', [])")
     apply simp




qed







    
qed

end