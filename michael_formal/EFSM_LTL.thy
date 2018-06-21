theory EFSM_LTL
imports EFSM Filesystem "HOL-Library.Sublist"
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

primrec globally2 :: "(statename \<times> event \<times> registers \<times> outputs) list \<Rightarrow> ((statename \<times> event \<times> registers \<times> outputs) \<Rightarrow> bool) \<Rightarrow> bool" where
  "globally2 [] _ = True" |
  "globally2 (h#t) f = conj (f h) (globally2 t f)"

lemma globally_empty: "globally e spr [t] f \<Longrightarrow> globally e spr [] f"
    apply simp
    apply (rule_tac x="fst t" in exI)
    apply (rule_tac x="snd t" in exI)
  by simp

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

lemma todo_achim: "globally e (s, outs, r) (xs @ [x]) f \<Longrightarrow> globally e (s, outs, r) xs f"
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case
    using contra by blast
next
  case (snoc a xs)
  then show ?case
    apply (simp del: append.simps)
    apply (cases "globally e (s, outs, r) (xs @ [a]) f")
     apply simp
    apply simp
    sorry
    (* try *)
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

lemma read_2_eq: "r ''r1'' = r ''r3'' \<longrightarrow> step filesystem 2 r ''read'' [] = (2, [r ''r2''], r)"
  apply (simp add: fs_simp step_def)
  apply safe
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
    r ''r1'' \<noteq> r ''r3'' \<Longrightarrow>
    step filesystem 2 r ''write'' (snd x) = (2, [0], r)"
  by (simp add: fs_simp step_def)

lemma noMoreInputs_2: "x \<noteq> (''read'', []) \<Longrightarrow>
    x \<noteq> (''logout'', []) \<Longrightarrow>
    \<not> (fst x = ''write'' \<and> length (snd x) = 1) \<Longrightarrow> step filesystem 2 r (fst x) (snd x) = (0, [], r)"
  apply (simp add: fs_simp step_def)
  by (metis prod.collapse)

lemma step_0: "step filesystem 0 r i l = (0, [], r)"
  by (simp add: fs_simp step_def)

lemma sink: "globally filesystem (0, [], <>) xs (\<lambda>(s', p', r') e'. s' = 2 \<and> fst e' = ''read'' \<and> r' ''r1'' \<noteq> 0 \<longrightarrow> fst (snd (EFSM_LTL.step filesystem 2 r' ''read'' (snd e'))) = [0])"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (simp add: step_0)
qed

lemma aux1: "globally filesystem (1, outs, <>) xs (\<lambda>a. case a of (s, a) \<Rightarrow> \<lambda>a. s \<noteq> 0) \<Longrightarrow>  xs = a # list \<Longrightarrow>
              \<not> globally filesystem (2, [], \<lambda>i. if i = ''r1'' then hd (snd x) else 0) xs (\<lambda>(s, a) a. s \<noteq> 0)"
  apply simp
  apply (case_tac "fst a = ''login'' \<and> length (snd a) = 1")
   apply (simp add: login_1 login_2 contra)
  by (simp add: notLogin_1 contra)

lemma empty_equiv: "(\<lambda>i. if i = ''r1'' then 0 else 0) = <>"
  apply (rule ext)
  by (simp add: null_state_def)

lemma true_fun: "globally2 t (\<lambda>x. True) = True"
proof (induction t)
  case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case by simp
qed

lemma observe_prefix: "\<forall> s r. prefix (observe_temp e s r t) (observe_temp e s r (t@t'))"
  apply (rule allI, rule allI)
proof (induction t)
  case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case
    apply simp
    apply (cases "EFSM.step e s r (fst a) (snd a)")
     apply simp
    apply safe
    by simp
qed

lemma prefix_zs: "\<exists>zs. t' = t @ zs \<longrightarrow> globally2 t' f = globally2 (t@zs) f"
  by simp

lemma "prefix t t' \<longrightarrow> globally2 t' f \<longrightarrow> globally2 t f"
  apply (simp add: prefix_def)
  try
  

lemma filesystem_prefix: "\<forall>s r. prefix (observe_temp filesystem s r (t @ x)) (observe_temp filesystem s r (t @ x @ [a]))"
  apply (rule allI, rule allI)
proof (induction t)
  case Nil
  then show ?case by (simp add: observe_prefix)
next
  case (Cons a t)
  then show ?case
    apply simp
    apply (case_tac "EFSM.step filesystem s r (fst a) (snd a)")
     apply simp
    apply safe
    by simp
qed

lemma prop_aux: "prefix (observe_temp filesystem 1 <> (t @ x)) (observe_temp filesystem 1 <> (t @ x @ [a]))"
  by (simp add: filesystem_prefix)

abbreviation "fsg \<equiv> globally filesystem"

lemma "globally2 (observe_temp filesystem 1 <> (t@t')) (\<lambda>(s, e, r, p). s \<noteq> 0) \<longrightarrow>
globally2 (observe_temp filesystem 1 <> (t@t')) (\<lambda>(s, e, r, p). (fst e = ''write'' \<and> r ''r1'' = 0 \<and> snd e \<noteq> [0]) \<longrightarrow>
  globally2 (observe_temp filesystem 1 <> t') (\<lambda>(s', e', r', p'). (s' = 2 \<and> fst e' = ''read'' \<and> r' ''r1'' \<noteq> 0)\<longrightarrow>
    (fst (snd (step filesystem s' r' (fst e') (snd e')))) = [0]))"
proof (induction "t'" rule: rev_induct)
case Nil
  then show ?case by (simp add: true_fun)
next
  case (snoc a x)
  then show ?case
    apply simp
qed

lemma "fsg (1,outs,<>) t (\<lambda>(s, p, r) e. s \<noteq> 0) \<longrightarrow>
globally filesystem (1,outs,<>) t (\<lambda>(s, p, r) e. (fst e = ''write'' \<and> r ''r1'' = 0 \<and> snd e \<noteq> [0]) \<longrightarrow>
  globally filesystem (s, p, r) t (\<lambda>(s', p', r') e'. (s' = 2 \<and> fst e' = ''read'' \<and> r' ''r1'' \<noteq> 0)\<longrightarrow>
    (fst (snd (step filesystem s' r' (fst e') (snd e')))) = [0]))"
proof (induction t)
case Nil
then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    apply simp
    apply (simp add: write_1)
    apply (simp add: sink)
    apply (case_tac "EFSM_LTL.step filesystem 1 <> (fst x) (snd x) = (0, [], r)")
     apply simp
    using notZero apply blast
    apply (case_tac "EFSM_LTL.step filesystem 1 <> (fst x) (snd x) = (2, [], \<lambda>i. if i = ''r1'' then hd (snd x) else 0)")
     apply simp
     apply (cases xs)
      apply simp
    apply (case_tac "globally filesystem (1, outs, <>) xs (\<lambda>a. case a of (s, a) \<Rightarrow> \<lambda>a. s \<noteq> 0)")
    apply (simp only: aux1)
      apply simp
     apply (simp del: globally.simps)
     apply safe[1]
     apply (case_tac "hd (snd x) = 0")
    apply (simp only: empty_equiv)








qed
end