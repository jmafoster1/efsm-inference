theory EFSM_LTL
imports EFSM Filesystem
begin

definition step :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (statename \<times> outputs \<times> registers)" where
"step e s r l i \<equiv>
  case (possible_steps e s r l i) of
    [(s',t)] \<Rightarrow> (s', (apply_outputs (Outputs t) (join_ir i r)), (apply_updates (Updates t) (join_ir i r) r)) |
    _ \<Rightarrow> (0, [], r)"

primrec step_trace :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> (statename \<times> outputs \<times> registers) list" where
"step_trace e s r [] = []" |
"step_trace e s r (h#t) = (let (s', p, r') = step e s r (fst h) (snd h) in (s', p, r')#(step_trace e s' r' t))"

abbreviation neXt :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> event \<Rightarrow> ((statename \<times> outputs \<times> registers) \<Rightarrow> event \<Rightarrow> bool) \<Rightarrow> bool" where
  "neXt e s r v f \<equiv> f (step e s r (fst v) (snd v)) v"

primrec globally :: "efsm \<Rightarrow> (statename \<times> outputs \<times> registers) \<Rightarrow> trace \<Rightarrow> ((statename \<times> outputs \<times> registers) \<Rightarrow> event \<Rightarrow> bool) \<Rightarrow> bool" where
  "globally e spr [] f = (\<exists>e. f spr e)" |
  "globally e spr (h#t) f = conj (f spr h) (globally e (step e (fst spr) (snd (snd spr)) (fst h) (snd h)) t f)"

lemma login_1: "fst a = ''login'' \<and> length (snd a) = Suc 0 \<Longrightarrow> step filesystem 1 r ''login'' (snd a) = (2, [], (\<lambda>x. if x = ''r1'' then hd (snd a) else r x))"
  apply (simp add: fs_simp step_def)
  apply (rule ext)
  apply simp
  by (metis Suc_length_conv i1 index2state.simps(2) list.sel(1))

lemma notZero: "globally filesystem (0, [], r) t (\<lambda>(s, a) a. s \<noteq> 0) \<Longrightarrow> False"
proof (induction t)
case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case by simp
qed

lemma login_2: "step filesystem 2 r ''login'' x = (0, [], r)"
  by (simp add: fs_simp step_def)

lemma contra: "\<not> globally e (s, outs, r) [] f \<Longrightarrow> \<not> globally e (s, outs, r) x f"
proof (induction x)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  then show ?case
    apply simp
    using Cons.prems globally.simps(1) by blast
qed

lemma snoc: "xs@[a, as] = xs@[a]@[as]"
  by simp

lemma "globally e (s, outs, r) (xs @ [x]) f \<Longrightarrow> globally e (s, outs, r) xs f"
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case
    using contra by blast
next
  case (snoc a xs)
  then show ?case
    apply (simp del: append.simps)
    sorry
qed

lemma login_x: "step filesystem 1 r ''login'' [x] = (2, [], (\<lambda>i. if i = ''r1'' then x else r i))"
  apply (simp add: fs_simp step_def)
  apply (rule ext)
  by simp

lemma read_1: "step filesystem 1 r ''read'' [] = (0, [], r)"
  by (simp add: fs_simp step_def)

lemma logout_1: "step filesystem 1 r ''logout'' [] = (0, [], r)"
  by (simp add: fs_simp step_def)

lemma write_1: "step filesystem 1 r ''write'' (snd h) = (0, [], r)"
  by (simp add: fs_simp step_def)

lemma noOtherInputs: "h \<noteq> (''read'', []) \<Longrightarrow>
    h \<noteq> (''logout'', []) \<Longrightarrow>
    \<not> (fst h = ''write'' \<and> length (snd h) = 1) \<Longrightarrow>
    \<not> (fst h = ''login'' \<and> length (snd h) = 1) \<Longrightarrow> \<forall>s r. step filesystem s r (fst h) (snd h) = (0, [], r)"
  apply (simp add: fs_simp step_def)
  by (smt prod.collapse)

lemma noOtherStates: "s \<noteq> 1 \<Longrightarrow>
                s \<noteq> 2 \<Longrightarrow>
                s \<noteq> 0 \<Longrightarrow> \<forall>r i l. step filesystem s r l i = (0, [], r)"
  by (simp add: fs_simp step_def)

lemma prependLogin: "\<forall>h t. (globally filesystem (s,outs,r) (h#t) (\<lambda>(s, p, r) e. s \<noteq> 0) \<longrightarrow> fst x = ''login'' \<and> length (snd x) = 1 \<longrightarrow>  \<not> globally filesystem (s,outs,r) (x#h#t) (\<lambda>(s, p, r) e. s \<noteq> 0))"
  apply (rule allI, rule allI)
  apply simp
  apply (case_tac "s=0")
   apply simp
  apply (case_tac "s=1")
   apply (simp add: login_x)
   apply (case_tac "h = (''read'', [])")
    apply (simp add: read_1 contra)
   apply (case_tac "h = (''logout'', [])")
    apply (simp add: logout_1 contra)
   apply (case_tac "fst h = ''write'' \<and> length (snd h) = 1")
    apply (simp add: write_1 contra)
   apply (case_tac "fst h = ''login'' \<and> length (snd h) = 1")
    apply (simp add: login_1 login_2 contra)
   apply (simp add: noOtherInputs contra)
  apply (case_tac "s=2")
   apply safe
   apply (simp add: login_2)
  by (simp add: noOtherStates)

lemma loginNot1: "s \<noteq> 1 \<Longrightarrow>step filesystem s r ''login'' (snd x) = (0, [], r)"
  by (simp add: fs_simp step_def)

lemma nonZeroFun: "(\<lambda>a. case a of (s, a) \<Rightarrow> case a of (p, r) \<Rightarrow> \<lambda>e. s \<noteq> 0) = (\<lambda>(s, p, r) e. s \<noteq> 0)"
  by auto

lemma notLogin_1:  "\<not> (fst x = ''login'' \<and> length (snd x) = 1) \<Longrightarrow> step filesystem 1 r (fst x) (snd x) = (0, [], r)"
  by (simp add: fs_simp step_def)

lemma read_2_neq: "r ''r1'' \<noteq> r ''r3'' \<Longrightarrow> step filesystem 2 r ''read'' [] = (2, [0], r)"
  apply (simp add: fs_simp step_def)
  apply (rule ext)
  by simp

lemma read_2_eq: "r ''r1'' = r ''r3'' \<Longrightarrow> step filesystem 2 r ''read'' [] = (2, [r ''r2''], r)"
  apply (simp add: fs_simp step_def)
  apply (rule ext)
  by simp

lemma logout_2: "step filesystem 2 r ''logout'' [] = (1, [], r)"
  apply (simp add: fs_simp step_def)
  apply (rule ext)
  by simp

lemma write_2_eq: "fst x = ''write'' \<and> length (snd x) = Suc 0 \<Longrightarrow>
    r ''r1'' = r ''r3'' \<Longrightarrow>
    step filesystem 2 r ''write'' (snd x) = (2, [], (\<lambda>i. if i = ''r2'' then hd(snd x) else (if i = ''r3'' then r ''r1'' else r i)))"
  apply (simp add: step_def fs_simp)
   apply (rule ext)
   apply simp
  by (metis Suc_length_conv i1 index2state.simps(2) list.sel(1))

lemma write_2_neq: "fst x = ''write'' \<and> length (snd x) = Suc 0 \<Longrightarrow>
    r ''r1'' = r ''r3'' \<Longrightarrow>
    step filesystem 2 r ''write'' (snd x) = (2, [0], r)"

lemma "globally filesystem (s,outs,r) t (\<lambda>(s, p, r) e. s \<noteq> 0) \<longrightarrow>
globally filesystem (s,outs,r) t (\<lambda>(s, p, r) e. (fst e = ''write'' \<and> r ''r1'' = 0 \<and> snd e \<noteq> [0]) \<longrightarrow>
  globally filesystem (s, p, r) t (\<lambda>(s', p', r') e'. (s' = 2 \<and> fst e' = ''read'' \<and> r' ''r1'' \<noteq> 0)\<longrightarrow>
    (fst (snd (step filesystem s' r' (fst e') (snd e')))) = [0]))"
proof (induction t)
case Nil
then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    apply (cases xs)
     apply simp
     apply (case_tac "s = 1")
      apply simp
      apply (case_tac "fst x = ''login'' \<and> length (snd x) = 1")
       apply (simp add: login_1)
      apply (simp add: notLogin_1)
     apply (case_tac "s = 2")
      apply simp
      apply (case_tac "x = (''read'', [])")
       apply simp
       apply (case_tac "r ''r1'' = r ''r3''")
        apply (simp add: read_2_eq)
       apply (simp add: read_2_neq)
      apply (case_tac "x = (''logout'', [])")
       apply (simp add: logout_2)
      apply (case_tac "fst x = ''write'' \<and> length (snd x) = 1")
       apply (case_tac "r ''r1'' = r ''r3''")
        apply simp
       apply (simp add: write_2_eq)






qed



end