theory EFSM_LTL
imports EFSM Filesystem
begin

definition step :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (statename \<times> outputs \<times> registers)" where
"step e s r l i \<equiv>
  case (possible_steps e s r l i) of
    [(s',t)] \<Rightarrow> (s', (apply_outputs (Outputs t) (join_ir i r)), (apply_updates (Updates t) (join_ir i r) r)) |
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

lemma read_not_none : "\<forall>r'. step filesystem 2 r ''read'' [] \<noteq> (0, [], r')"
  by (simp add: fs_simp step_def)

lemma read_no_side_effects : "\<exists>p. step filesystem 2 r ''read'' [] = (2, p, r)"
  apply (simp add: fs_simp step_def)
  apply (case_tac "r ''r1'' = r ''r3''")
   apply simp
  apply (rule ext)
  by auto

lemma read_no_side_effects2 : "step filesystem 2 r ''read'' [] = a \<Longrightarrow> snd (snd a) = r \<and> fst a = 2"
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

lemma read_step: "EFSM_LTL.step filesystem 2 r ''read'' [] = (2, [r ''r2''], r) \<or>
EFSM_LTL.step filesystem 2 r ''read'' [] = (2, [0], r)"
  apply (case_tac "r ''r1'' = r ''r3''")
   apply (simp add: read_success)
  by (simp add: read_denied1)

lemma logout: "(EFSM_LTL.step filesystem 2 r ''logout'' []) = (1, [], r)"
  apply (simp add: fs_simp step_def)
  by (rule ext, simp)

lemma login_2: "fst a = ''login'' \<Longrightarrow> EFSM_LTL.step filesystem 2 r (fst a) (snd a) = (0, [], r)"
  by (simp add: fs_simp step_def)

lemma index2state_i1: "length (snd a) = Suc 0 \<Longrightarrow> index2state (snd a) 1 ''i1'' = hd (snd a)"
  by (metis Suc_length_conv i1 index2state.simps(2) list.sel(1))

lemma writes: "fst a = ''write'' \<and> length (snd a) = Suc 0 \<Longrightarrow>
                r ''r1'' \<noteq> r ''r3'' \<Longrightarrow> 
                EFSM_LTL.step filesystem 2 r ''write'' (snd a) = (2, [], (\<lambda>x. if x = ''r2'' then hd (snd a) else (if x = ''r3'' then r ''r1'' else r x)))"
  apply (simp add: fs_simp step_def)
  apply safe
  apply (rule ext)
  apply simp
  by (simp add: index2state_i1)

lemma nomoreinputs: "a \<noteq> (''read'', []) \<Longrightarrow>
         a \<noteq> (''logout'', []) \<Longrightarrow>
         fst a \<noteq> ''write'' \<Longrightarrow>
         (EFSM_LTL.step filesystem 2 r (fst a) (snd a)) = (0, [],r)"
  apply (simp add: fs_simp step_def)
  by (metis prod.collapse)

lemma dead_state: "globally filesystem (0, [], r) t (\<lambda>s e r' p. s \<noteq> 0) \<Longrightarrow> False"
proof (induction t)
case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case by simp
qed

lemma "all (t) (\<lambda>e. e = (''read'', []) \<or> e = (''login'', []) \<or> e = (''logout'', []) \<or> (fst e = ''write'' \<and> length (snd e) = 1)) \<Longrightarrow>
 \<forall> outs r. globally filesystem (state, outs, r) t (\<lambda>s e r' p. s \<noteq> 0) \<longrightarrow>
globally filesystem (state, outs, r) t (\<lambda>s e r' p. (s = 2 \<and> fst e = ''write'' \<and> r' ''r1'' = 1) \<longrightarrow>
  globally filesystem (state, outs, r) t (\<lambda>s e r' p. (s = 2 \<and> fst e = ''read'' \<and> r' ''r1'' \<noteq> 1)) \<longrightarrow>
    neXt filesystem s' r'' (hd t') (\<lambda>spr e. (fst (snd spr)) = [0])
)"
proof (induction t)
  case Nil
  then show ?case by simp
next
  case (Cons a t')
  then show ?case
    apply (case_tac "state = 2")
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

     apply (case_tac "fst a = ''write'' \<and> length (snd a) = 1", simp)
      apply (frule allI)
      apply (case_tac "r ''r1'' = r ''r3''")
    using truefun apply blast
      apply (simp add: writes truefun)

    apply (case_tac "a = (''logout'', [])", simp)
    apply (simp add: logout truefun)

     apply (rule allI, rule allI)
     apply safe
      apply (simp add: nomoreinputs)
      apply (metis (no_types, lifting) dead_state fst_conv login_2)

     apply simp
     apply (metis (no_types, lifting) dead_state fst_conv login_2)

    apply (case_tac "state = 0")
     apply simp

    apply (case_tac "state = 1")
     apply (case_tac "fst a = ''login'' \<and> length (snd a) = 1")
      apply (simp add: truefun)
     apply (simp add: truefun)
    by (simp add: truefun)
qed
end