theory EFSM_LTL
imports EFSM Filesystem "HOL-Library.Sublist"
begin

type_synonym ltl_pred2 = "(statename \<times> event \<times> registers \<times> outputs) \<Rightarrow> bool"
type_synonym ltl_pred = "((statename \<times> outputs \<times> registers) \<Rightarrow> event \<Rightarrow> bool)"
definition step :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> event \<Rightarrow> (statename \<times> outputs \<times> registers)" where
"step e s r ev \<equiv>
  case (possible_steps e s r (fst ev) (snd ev)) of
    [(s',t)] \<Rightarrow> (s', (apply_outputs (Outputs t) (join_ir (snd ev) r)), (apply_updates (Updates t) (join_ir (snd ev) r) r)) |
    _ \<Rightarrow> (0, [], r)"

fun neXt :: "efsm \<Rightarrow> (statename \<times> outputs \<times> registers) \<Rightarrow> event \<Rightarrow> ((statename \<times> outputs \<times> registers) \<Rightarrow> event \<Rightarrow> bool) \<Rightarrow> bool" where
  "neXt e spr h f = f (step e (fst spr) (snd (snd spr)) h) h"

primrec until :: "efsm \<Rightarrow> (statename \<times> outputs \<times> registers) \<Rightarrow> trace \<Rightarrow> ltl_pred \<Rightarrow> ltl_pred \<Rightarrow> bool" where
  "until e spr [] f f' = False" |
  "until e spr (h#t) f f' = disj (f' spr h) (conj (f spr h) (until e (step e (fst spr) (snd (snd spr)) h) t f f'))"

primrec until2 :: "(statename \<times> event \<times> registers \<times> outputs) list \<Rightarrow> ltl_pred2 \<Rightarrow> ltl_pred2 \<Rightarrow> bool" where
  "until2 [] _ _ = False" |
  "until2 (h#t) f f' = disj (f' h) (conj (f h) (until2 t f f'))"

primrec globally :: "efsm \<Rightarrow> (statename \<times> outputs \<times> registers) \<Rightarrow> trace \<Rightarrow> ((statename \<times> outputs \<times> registers) \<Rightarrow> event \<Rightarrow> bool) \<Rightarrow> bool" where
  "globally e spr [] f = (\<exists>e. f spr e)" |
  "globally e spr (h#t) f = conj (f spr h) (globally e (step e (fst spr) (snd (snd spr)) h) t f)"

primrec globally2 :: "(statename \<times> event \<times> registers \<times> outputs) list \<Rightarrow> ltl_pred2 \<Rightarrow> bool" where
  "globally2 [] _ = True" |
  "globally2 (h#t) f = conj (f h) (globally2 t f)"

primrec eventually :: "efsm \<Rightarrow> (statename \<times> outputs \<times> registers) \<Rightarrow> trace \<Rightarrow> ((statename \<times> outputs \<times> registers) \<Rightarrow> event \<Rightarrow> bool) \<Rightarrow> bool" where
  "eventually e spr [] f = False" |
  "eventually e spr (h#t) f = disj (f spr h) (eventually e (step e (fst spr) (snd (snd spr)) h) t f)"

primrec eventually2 :: "(statename \<times> event \<times> registers \<times> outputs) list \<Rightarrow> ltl_pred2 \<Rightarrow> bool" where
  "eventually2 [] _ = False" |
  "eventually2 (h#t) f = disj (f h) (eventually2 t f)"

primrec after2 :: "(statename \<times> event \<times> registers \<times> outputs) list \<Rightarrow> ltl_pred2 \<Rightarrow> ltl_pred2 \<Rightarrow> bool" where
  "after2 [] f f' = True" |
  "after2 (h#t) f f' = (if f h then globally2 t f' else after2 t f f')"

fun after :: "efsm \<Rightarrow> (statename \<times> outputs \<times> registers) \<Rightarrow> trace \<Rightarrow> ltl_pred \<Rightarrow> ltl_pred \<Rightarrow> bool" where
  "after _ _ [] _ _ = True" |
  "after e (s, p, r) (h#t) f f' = (if (f (s, p, r) h) then globally e (step e s r h) t f' else after e (step e s r h) t f f')"

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

abbreviation observe_fs :: "trace \<Rightarrow> (statename \<times> event \<times> registers \<times> outputs) list" where
"observe_fs t \<equiv> observe_temp filesystem 1 <> t"

fun logout2 :: ltl_pred2 where
  "logout2 (state, (label, inputs), registers, outputs) = (label = ''logout'')"

fun read :: ltl_pred2 where
  "read (state, (label, inputs), registers, outputs) = (label = ''read'')"

fun login_attacker :: ltl_pred2 where
  "login_attacker (state, (label, inputs), registers, outputs) = (label = ''login'' \<and> inputs \<noteq> [0])"

fun "write" :: ltl_pred2 where
  "write (state, (label, inputs), registers, outputs) = (label = ''write'')"

fun access_denied2 :: ltl_pred2 where
  "access_denied (state, (label, inputs), registers, outputs) = (outputs = [0])"

lemma observe_append: "\<exists>t'. (observe_fs (t @ [a])) = (observe_fs t)@t'"
  using observe_prefix prefixE by blast

lemma extra_element_2: "\<exists>t'. ts = t@t' \<longrightarrow> globally2 t f \<longrightarrow> globally2 ts f = globally2 t' f"
  by auto

(*  noChangeOwner: THEOREM filesystem |- G(cfstate /= NULL_STATE) =>
G(
    (
        (label=login AND ip_1_login_1=user) AND U(label/=logout, label=write)
    ) =>
    G(
        label=logout =>
        X(
            ((label=login AND ip_1_login_1=attacker) AND F(label=logout)) => U(label=read => X(op_1_read_0=access_denied),label=logout)
        )
    )
);*)
(* primrec globally2 :: "(statename \<times> event \<times> registers \<times> outputs) list \<Rightarrow> ltl_pred2 \<Rightarrow> bool" where *)

abbreviation "G \<equiv> globally filesystem (1, [], <>)"
abbreviation "U \<equiv> until filesystem"
abbreviation "X \<equiv> neXt filesystem"
abbreviation "F \<equiv> eventually filesystem"

fun logout :: "(statename \<times> outputs \<times> registers) \<Rightarrow> event \<Rightarrow> bool" where
"logout (s, p, r) (l, i) = (l=''logout'')"

fun access_denied :: "(statename \<times> outputs \<times> registers) \<Rightarrow> event \<Rightarrow> bool" where
"access_denied (s, p, r) (l, i) = (p=[0])"

lemma "G (e#t) (\<lambda>(s, p, r) (l, i). 
    (l=''login'' \<and> i=[0] \<and> (U (1, [], <>) (e#t) (\<lambda>(s, p, r) (l, i). l\<noteq>''logout'') (\<lambda>(s, p, r) (l, i). l=''write''))) \<longrightarrow>
    G (e#t) (\<lambda>spr e. l=''logout'' \<longrightarrow> X spr e (\<lambda>(s, p, r) (l, i).
        (l=''login'' \<and> i \<noteq> [0] \<and> (F (s, p, r) t logout)) \<longrightarrow> U (s, p, r) t (\<lambda>(s, p, r) (l, i).l=''read'' \<longrightarrow> (X (s, p, r) (l, i) access_denied)) logout
      )
    )
)"

lemma noChangeOwner: "globally2 (observe_fs t) (\<lambda>(state, (label, inputs), registers, outputs).
  (
    (label = ''login'' \<and> inputs = [0] \<and> (until2 (observe_fs t) logout2 write))
  ) \<longrightarrow>
globally2 (observe_fs t) (\<lambda>x. 
logout2 x \<longrightarrow> neXt2 (observe_fs t) (\<lambda>x. (login_attacker x \<and> eventually2 (observe_fs t) logout2)) \<longrightarrow> until2 (observe_fs t) 
(\<lambda>(s, (l, i), r, p). label = ''read'' \<longrightarrow> p = [0]) logout2 ))"
proof (induct t rule: rev_induct)
case Nil
then show ?case by simp
next
  case (snoc a t)
  then show ?case
    apply simp


  qed

(* Traces are necessarily infinite *)


end