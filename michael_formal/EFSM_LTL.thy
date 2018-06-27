theory EFSM_LTL
imports EFSM Filesystem "HOL-Library.Sublist"
begin

definition step :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> event \<Rightarrow> (statename \<times> outputs \<times> registers)" where
"step e s r ev \<equiv>
  case (possible_steps e s r (fst ev) (snd ev)) of
    [(s',t)] \<Rightarrow> (s', (apply_outputs (Outputs t) (join_ir (snd ev) r)), (apply_updates (Updates t) (join_ir (snd ev) r) r)) |
    _ \<Rightarrow> (0, [], r)"

abbreviation neXt :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> event \<Rightarrow> ((statename \<times> outputs \<times> registers) \<Rightarrow> event \<Rightarrow> bool) \<Rightarrow> bool" where
  "neXt e s r v f \<equiv> f (step e s r v) v"

primrec globally :: "efsm \<Rightarrow> (statename \<times> outputs \<times> registers) \<Rightarrow> trace \<Rightarrow> ((statename \<times> outputs \<times> registers) \<Rightarrow> event \<Rightarrow> bool) \<Rightarrow> bool" where
  "globally e spr [] f = (\<exists>e. f spr e)" |
  "globally e spr (h#t) f = conj (f spr h) (globally e (step e (fst spr) (snd (snd spr)) h) t f)"

primrec globally2 :: "(statename \<times> event \<times> registers \<times> outputs) list \<Rightarrow> ((statename \<times> event \<times> registers \<times> outputs) \<Rightarrow> bool) \<Rightarrow> bool" where
  "globally2 [] _ = True" |
  "globally2 (h#t) f = conj (f h) (globally2 t f)"

lemma globally_empty: "globally e spr [t] f \<Longrightarrow> globally e spr [] f"
    apply simp
    apply (rule_tac x="fst t" in exI)
    apply (rule_tac x="snd t" in exI)
  by simp

lemma notZero: "globally filesystem (0, [], r) t (\<lambda>(s, a) a. s \<noteq> 0) \<Longrightarrow> False"
proof (induction t)
case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case by simp
qed

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

lemma true_fun[simp]: "globally2 t (\<lambda>x. True) = True"
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

lemma globally2_prefix: "globally2 (t@t') f \<Longrightarrow> globally2 t f"
proof (induction t)
  case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case by simp
qed


lemma globally2_prefix_2: "prefix t t' \<longrightarrow> globally2 t' f \<longrightarrow> globally2 t f"
proof (induct t' rule:rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  then show ?case by (simp add: globally2_prefix)
qed

lemma globally2_prefix_3: "\<exists>lst t'. (t=lst@t' \<longrightarrow> globally2 lst f \<longrightarrow> globally2 t f \<longrightarrow> globally2 t' f)"
  by auto

lemma globally2_prefix_4: "\<exists>lst t'. (t=lst@t' \<longrightarrow> globally2 lst f \<and> globally2 t' f \<longrightarrow> globally2 t f)"
  by auto



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

lemma prop_aux_2: "globally2 (observe_temp filesystem 1 <> (x @ [a])) (\<lambda>a. case a of (s, a) \<Rightarrow> s \<noteq> 0) \<Longrightarrow> globally2 (observe_temp filesystem 1 <> (x)) (\<lambda>a. case a of (s, a) \<Rightarrow> s \<noteq> 0)"
  using globally2_prefix_2 observe_prefix by blast

lemma prop_aux: "prefix (observe_temp filesystem 1 <> (t @ x)) (observe_temp filesystem 1 <> (t @ x @ [a]))"
  by (simp add: filesystem_prefix)

lemma globally2_all_elements: "globally2 (t @ x # xs) f \<Longrightarrow> f x"
proof (induct t)
  case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case by simp
qed

lemma globally2_all_elements_2: "globally2 t f \<Longrightarrow> f x \<Longrightarrow> globally2 xs f \<Longrightarrow> globally2 (t @ x # xs) f"
proof (induct t)
  case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case by simp
qed

lemma globally2_all_elements_3: "\<not> globally2 xs f \<Longrightarrow> globally2 (t @ x # xs) f \<Longrightarrow> False"
proof (induct t)
  case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case by simp
qed

lemma globally_extra_element: "globally2 t f \<Longrightarrow> globally2 (t@t') f = globally2 t' f"
proof (induct t')
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    apply simp
    apply safe
       apply (simp add: globally2_all_elements)
      apply (simp add: globally2_all_elements_2)
     apply (simp add: globally2_all_elements)
    using globally2_all_elements_3 by blast    
qed

(* primrec observe_temp :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> (statename \<times> event \<times> registers \<times> outputs) list" where *)

lemma filesystem_prefix_2: "prefix (observe_temp filesystem 1 <> x) (observe_temp filesystem 1 <> (x @ [a]))"
  by (simp add: observe_prefix)


abbreviation "fsg \<equiv> globally filesystem"

lemma "globally2 (observe_temp filesystem s r (e#t)) (\<lambda>(s, e, r, p). s \<noteq> 0) \<longrightarrow>
globally2 (observe_temp filesystem s r (e#t)) (\<lambda>(st, ev, re, p). (fst e = ''write'' \<and> r ''r1'' = 0 \<and> snd e \<noteq> [0]) \<longrightarrow>
    globally2 (observe_temp filesystem s' r' t) (\<lambda>(s', e', r', p'). (s' = 2 \<and> fst e' = ''read'' \<and> r' ''r1'' \<noteq> 0)\<longrightarrow>
    (fst (snd (step filesystem s' r' e'))) = [0]))"
proof (induction "t" rule: rev_induct)
case Nil
  then show ?case by simp
next
  case (snoc a x)
  then show ?case
    apply simp
    apply (cases "EFSM.step filesystem s r (fst e) (snd e)")
     apply simp
    apply simp
    apply (case_tac "aa")
    apply simp
    

qed

lemma "globally2 (observe_temp filesystem 1 <> t) (\<lambda>(s, e, r, p). s \<noteq> 0) \<longrightarrow>
globally2 (observe_temp filesystem 1 <> t) (\<lambda>(s, e, r, p). (fst e = ''write'' \<and> r ''r1'' = 0 \<and> snd e \<noteq> [0]) \<longrightarrow>
  globally2 (observe_temp filesystem 1 <> t) (\<lambda>(s', e', r', p'). (s' = 2 \<and> fst e' = ''read'' \<and> r' ''r1'' \<noteq> 0)\<longrightarrow>
    (fst (snd (step filesystem s' r' (fst e') (snd e')))) = [0]))"
proof (induction "t" rule: rev_induct)
case Nil
  then show ?case by simp
next
  case (snoc a x)
  then show ?case
    apply simp
    apply (cases "globally2 (observe_temp filesystem 1 <> (x @ [a])) (\<lambda>a. case a of (s, a) \<Rightarrow> s \<noteq> 0)")
     apply (simp add: prop_aux_2)
     apply (simp add: globally_extra_element filesystem_prefix_2)
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