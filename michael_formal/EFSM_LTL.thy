theory EFSM_LTL
imports EFSM Filesystem
begin

definition step :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (statename \<times> outputs \<times> registers)" where
"step e s r l i \<equiv>
  case (possible_steps e s r l i) of
    [(s',t)] \<Rightarrow> (s', (apply_outputs (Outputs t) (join_ir i r 1)), (apply_updates (Updates t) (join_ir i r 1) r)) |
    _ \<Rightarrow> (0, [], r)"

abbreviation neXt :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> event \<Rightarrow> ((statename \<times> outputs \<times> registers) \<Rightarrow> event \<Rightarrow> bool) \<Rightarrow> bool" where
  "neXt e s r h f \<equiv> f (step e s r (fst h) (snd h)) h"

primrec globally :: "efsm \<Rightarrow> (statename \<times> outputs \<times> registers) \<Rightarrow> trace \<Rightarrow> (statename \<Rightarrow> event \<Rightarrow> registers \<Rightarrow> outputs \<Rightarrow> bool) \<Rightarrow> bool" where
  "globally e spr [] f = f (fst spr) ('''', []) (snd (snd spr)) (fst (snd spr))" |
  "globally e spr (h#t) f = conj (f (fst spr) h (snd (snd spr)) (fst (snd spr))) (globally e (step e (fst spr) (snd (snd spr)) (fst h) (snd h)) t f)"

(*
noChangeOwner: THEOREM filesystem |- FORALL (user : UID): G(cfstate /= NULL_STATE) => 
G( 
  (label=write AND r_1=user AND ip_1_write_1/=accessDenied) => 
  G((cfstate=S_2 AND label=read AND r_1/=user) => 
    X(op_1_read_0 = accessDenied) 
  ) 
  );
*)

lemma read_not_none [simp]: "\<forall>r'. step filesystem 2 r ''read'' [] \<noteq> (0, [], r')"
  by (simp add: fs_simp step_def)

lemma read_no_side_effects [simp]: "\<exists>p. step filesystem 2 r ''read'' [] = (2, p, r)"
  apply (simp add: fs_simp step_def)
  apply (case_tac "r ''r1'' = r ''r3''")
   apply simp
  apply (rule ext)
  by auto

lemma read_no_side_effects2 [simp]: "step filesystem 2 r ''read'' [] = a \<Longrightarrow> snd (snd a) = r \<and> fst a = 2"
  apply (simp add: step_def)
  apply (simp add: fs_simp)
  apply (case_tac "r ''r1'' = r ''r3''")
   apply simp
   apply safe[1]
    apply (rule ext, simp, simp)
  apply simp
  apply safe
  by (rule ext, simp, simp)

lemma truefun : "\<forall> e spr. globally e spr t (\<lambda>s e r' p. True)"
proof (induction t)
  case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case
    apply simp
    by (simp add: Cons.IH)
qed

lemma read_denied: "r ''r1'' \<noteq> 1 \<Longrightarrow> r ''r3'' = 1 \<Longrightarrow> EFSM_LTL.step filesystem 2 r ''read'' [] = (2, [0], r)"
  apply (simp add: fs_simp step_def)
  by (rule ext, simp)

lemma read_success: "r ''r1''= r ''r3'' \<Longrightarrow> EFSM_LTL.step filesystem 2 r ''read'' [] = (2, [r ''r2''], r)"
  apply (simp add: fs_simp step_def)
  by (rule ext, simp)

lemma read_denied1: "r ''r1'' \<noteq> r ''r3'' \<Longrightarrow> EFSM_LTL.step filesystem 2 r ''read'' [] = (2, [0], r)"
  apply (simp add: fs_simp step_def)
  by (rule ext, simp)

lemma aux1: "r ''r1'' = r ''r3'' \<Longrightarrow>
    (\<lambda>x. if x = ''r1'' then aval (snd (''r1'', V ''r1'')) r else apply_updates [(''r2'', V ''r2''), (''r3'', V ''r3'')] r r x) = r"
  by (rule ext, simp)

lemma read_step: "EFSM_LTL.step filesystem 2 r ''read'' [] = (2, [r ''r2''], r) \<or>
EFSM_LTL.step filesystem 2 r ''read'' [] = (2, [0], r)"
  apply (case_tac "r ''r1'' = r ''r3''")
   apply (simp add: read_success)
  by (simp add: read_denied1)

lemma "all (t) (\<lambda>e. e = (''read'', []) \<or> e = (''logout'', []) \<or> (fst e = ''write'' \<and> length (snd e) = 1)) \<Longrightarrow> 
 \<forall> outs r. globally filesystem (2, outs, r) t (\<lambda>s e r' p. (s = 2 \<and> fst e = ''write'' \<and> r' ''r1'' = 1) \<longrightarrow>
  globally filesystem (2, outs, r) t (\<lambda>s e r' p. (s = 2 \<and> fst e = ''read'' \<and> r' ''r1'' \<noteq> 1)) \<longrightarrow>
    neXt filesystem s' r'' (hd t') (\<lambda>spr e. (fst (snd spr)) = [0])
)"
proof (induction t)
  case Nil
  then show ?case by simp
next
  case (Cons a t')
  then show ?case
    apply (case_tac "a = (''read'', [])", simp)
     apply (rule allI)
     apply (case_tac "(EFSM_LTL.step filesystem 2 r ''read'' []) = (2, [0], r)", simp)
      apply (case_tac "r ''r1'' = 1")
       apply (simp add: truefun)
      apply simp
     apply (case_tac "r ''r1'' = 1")
      apply (simp add: truefun)
     apply simp
     apply (case_tac "r ''r3'' = 1")
      apply (simp add: read_denied)
    apply (case_tac "r ''r1'' = r ''r3''")
      apply (simp add: read_success)
     apply (simp add: read_denied1)

     
    



     


qed







    
qed

end