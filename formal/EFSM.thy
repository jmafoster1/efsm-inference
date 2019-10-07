subsection \<open>Extended Finite State Machines\<close>
text\<open>
This theory defines extended finite state machines. Each EFSM takes a type variable which represents
$S$. This is a slight devaition from the definition presented in \cite{foster2018} as this
type variable may be of an infinite type such as integers, however the intended use is for custom
finite types. See the examples for details.
\<close>

theory EFSM
  imports "~~/src/HOL/Library/FSet" Transition FSet_Utils
begin

declare One_nat_def [simp del]

type_synonym cfstate = nat
type_synonym inputs = "value list"
type_synonym outputs = "value option list"

type_synonym event = "(label \<times> inputs)"
type_synonym trace = "event list"
type_synonym execution = "(label \<times> value list \<times> outputs) list"
type_synonym observation = "outputs list"
type_synonym transition_matrix = "((cfstate \<times> cfstate) \<times> transition) fset"

definition Str :: "string \<Rightarrow> value" where
  "Str s \<equiv> value.Str (String.implode s)"

lemma str_not_num: "Str s \<noteq> Num x1"
  by (simp add: Str_def)

definition S :: "transition_matrix \<Rightarrow> nat fset" where
  "S m = (fimage (\<lambda>((s, s'), t). s) m) |\<union>| fimage (\<lambda>((s, s'), t). s') m"

lemma "S e = (fst \<circ> fst) |`| e |\<union>| (snd \<circ> fst) |`| e"
  apply (simp add: comp_def S_def)
  by force

definition choice :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "choice t t' = (\<exists> i r. apply_guards (Guard t) (join_ir i r) \<and> apply_guards (Guard t') (join_ir i r))"

definition choice_alt :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "choice_alt t t' = (\<exists> i r. apply_guards (Guard t@Guard t') (join_ir i r))"

lemma choice_alt: "choice t t' = choice_alt t t'"
  by (simp add: choice_def choice_alt_def apply_guards_append)

lemma choice_symmetry: "choice x y = choice y x"
  using choice_def by auto

primrec apply_updates :: "updates \<Rightarrow> datastate \<Rightarrow> registers \<Rightarrow> registers" where
  "apply_updates [] _ new = new" |
  "apply_updates (h#t) old new = (apply_updates t old new)(fst h $:= aval (snd h) old)"

lemma apply_updates_foldr: "apply_updates u old new = foldr (\<lambda>h r. r(fst h $:= aval (snd h) old)) u new"
proof(induct u)
  case Nil
  then show ?case
    by simp
next
  case (Cons a u)
  then show ?case
    apply (simp add: eq_finfun_All_ext finfun_All_def finfun_All_except_def)
    by (simp add: Cons.hyps)
qed

lemma r_not_updated_stays_the_same: "r \<notin> fst ` set U \<Longrightarrow>
    apply_updates U c d $ r = d $ r"
proof(induct U)
  case Nil
  then show ?case
    by simp
next
  case (Cons a U)
  then show ?case
    by simp
qed

definition "ps_filter p r i l s = (\<lambda>((origin, dest::nat), t::transition). origin = s \<and> (Label t) = l \<and> (length i) = (Arity t) \<and> apply_guards (Guard t) (join_ir i r) \<and> check_outs (Outputs t) (join_ir i r) p)"

definition possible_steps :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> outputs \<Rightarrow> (cfstate \<times> transition) fset" where
  "possible_steps e s r l i p = fimage (\<lambda>((origin, dest), t). (dest, t)) (ffilter (\<lambda>((origin, dest::nat), t::transition). origin = s \<and> (Label t) = l \<and> (length i) = (Arity t) \<and> apply_guards (Guard t) (join_ir i r) \<and> check_outs (Outputs t) (join_ir i r) p) e)"

lemma in_possible_steps: "(a, bb) |\<in>| possible_steps b s r ab ba p \<Longrightarrow> \<exists>s. ((s, a), bb) |\<in>| b"
  apply (simp add: possible_steps_def fimage_def ffilter_def fmember_def Abs_fset_inverse)
  by auto

lemma possible_steps_finsert: "possible_steps (finsert x e) s r l i p = possible_steps e s r l i p |\<union>| possible_steps {|x|} s r l i p"
  by (simp add: possible_steps_def ffilter_finsert)

lemma rearrange_ffilter: "\<exists>s. ffilter f l = {|((s, d), t)|} \<Longrightarrow>
       fimage (\<lambda>((origin, dest), t). (dest, t)) (ffilter f l) = {|(d, t)|}"
  apply (simp add: fimage_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
  by force

lemma ps_filter_origin: "ps_filter p r i l s ((aa, ba), b) \<Longrightarrow> aa = s"
  by (simp add: ps_filter_def)

lemma possible_steps_alt: "(possible_steps e s r l i p = {|(d, t)|}) = (ffilter
     (\<lambda>((origin, dest), t).
         origin = s \<and>
         Label t = l \<and>
         length i = Arity t \<and>
         apply_guards (Guard t) (join_ir i r) \<and>
         check_outs (Outputs t) (join_ir i r) p
     ) e = {|((s, d), t)|})"
proof(induct e)
  case empty
  then show ?case
    apply (simp add: possible_steps_def)
    by auto
next
  case (insert x e)
  then show ?case
    apply (simp only: possible_steps_def)
    apply (simp add: ps_filter_def[symmetric] ffilter_finsert)
    apply (cases x)
    apply (case_tac a)
    apply clarify
    apply (simp add: ps_filter_origin)
    by (metis fimage_is_fempty fsubset_finsertI fsubset_fsingletonD order_refl)
qed

lemmas possible_steps_singleton = possible_steps_alt Abs_ffilter Set.filter_def
lemmas possible_steps_empty = possible_steps_def Abs_ffilter Set.filter_def

lemma singleton_dest: "fis_singleton (possible_steps e s r aa b p) \<Longrightarrow>
       fthe_elem (possible_steps e s r aa b p) = (baa, aba) \<Longrightarrow>
       ((s, baa), aba) |\<in>| e"
  apply (simp add: fis_singleton_def fthe_elem_def singleton_equiv)
  apply (simp add: possible_steps_def fmember_def)
  by auto

definition random_member :: "'a fset \<Rightarrow> 'a option" where
  "random_member f = (if f = {||} then None else Some (Eps (\<lambda>x. x |\<in>| f)))"

lemma random_member_singleton [simp]: "random_member {|a|} = Some a"
  by (simp add: random_member_def)

inductive accepts :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> bool" where
  base: "accepts e s d []" |                                         
  step: "\<exists>(s', T) |\<in>| possible_steps e s d l i p.
         accepts e s' (apply_updates (Updates T) (join_ir i d) d) t \<Longrightarrow>
         accepts e s d ((l, i, p)#t)"

lemma accepts_step: "accepts e s d ((l, i, p)#t) = (\<exists>(s', T) |\<in>| possible_steps e s d l i p.
         accepts e s' (apply_updates (Updates T) (join_ir i d) d) t)"
  apply standard
   defer
   apply (simp add: accepts.step)
  apply (rule accepts.cases)
  by auto

fun accepts_prim :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> bool" where
  "accepts_prim e s d [] = True" |
  "accepts_prim e s d ((l, i, p)#t) = (
    let poss_steps = possible_steps e s d l i p in
    if fis_singleton poss_steps then
      let (s', T) = fthe_elem poss_steps in
      accepts_prim e s' (apply_updates (Updates T) (join_ir i d) d) t
    else
      (\<exists>(s', T) |\<in>| poss_steps. accepts_prim e s' (apply_updates (Updates T) (join_ir i d) d) t)
  )"

lemma accepts_prim: "\<forall>d s. accepts e s d t = accepts_prim e s d t"
proof(induct t)
case Nil
  then show ?case
    by (simp add: accepts.base)
next
  case (Cons a t)
  then show ?case
    apply (cases a)
    apply (simp add: accepts_step Let_def fis_singleton_alt)
    by auto
qed

abbreviation "rejects e s d t \<equiv> \<not> accepts e s d t"

lemma accepts_must_be_possible_step: "accepts e s r (h # t) \<Longrightarrow> \<exists>aa ba. (aa, ba) |\<in>| possible_steps e s r (fst h) (fst (snd h)) (snd (snd h))"
  using accepts_step by fastforce

definition step :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> outputs \<Rightarrow> (transition \<times> cfstate \<times> registers) option" where
  "step e s r l i p = (case random_member (possible_steps e s r l i p) of
      None \<Rightarrow> None |
      Some (s', t) \<Rightarrow>  Some (t, s', apply_updates (Updates t) (join_ir i r) r)
  )"

lemma step_some:
  "possibilities = (possible_steps e s r l i p) \<Longrightarrow>
   random_member possibilities = Some (s', t) \<Longrightarrow>
   apply_updates (Updates t) (join_ir i r) r = r' \<Longrightarrow>
   step e s r l i p = Some (t, s', r')"
  by (simp add: step_def)

lemma no_possible_steps_1: "possible_steps e s r l i p = {||} \<Longrightarrow> step e s r l i p = None"
  by (simp add: step_def random_member_def)

primrec observe_all :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> (transition \<times> nat \<times> registers) list" where
  "observe_all _ _ _ [] = []" |
  "observe_all e s r (h#t)  =
    (case (step e s r (fst h) (fst (snd h)) (snd (snd h))) of
      (Some (transition, s', updated)) \<Rightarrow> (((transition, s', updated)#(observe_all e s' updated t))) |
      _ \<Rightarrow> []
    )"

definition state :: "(transition \<times> nat \<times> outputs \<times> datastate) \<Rightarrow> nat" where
  "state x \<equiv> fst (snd x)"

lemma accepts_must_be_step: "accepts e s d (h#ts) \<Longrightarrow> \<exists>t s' d'. step e s d (fst h) (fst (snd h)) (snd (snd h)) = Some (t, s', d')"
  using accepts_must_be_possible_step[of e s d h ts]
  apply simp
  apply clarify
  apply (simp add: step_def random_member_def fmember_not_empty)
  apply (case_tac "SOME x. x |\<in>| possible_steps e s d (fst h) (fst (snd h)) (snd (snd h))")
  by simp

lemma accepts_cons: "accepts e s d (h#t) = (\<exists>(s', T) |\<in>| possible_steps e s d (fst h) (fst (snd h)) (snd (snd h)). accepts e s' (apply_updates (Updates T) (join_ir (fst (snd h)) d) d) t)"
  apply (cases h)
  using accepts_step by auto

lemma accepts_cons_step: "accepts e s r (h # t) \<Longrightarrow> step e s r (fst h) (fst (snd h)) (snd (snd h)) \<noteq>  None"
  by (simp add: accepts_must_be_step)

abbreviation accepts_trace :: "transition_matrix \<Rightarrow> execution \<Rightarrow> bool" where
  "accepts_trace e t \<equiv> accepts e 0 <> t"

lemma no_step_none: "step e s r aa ba op = None \<Longrightarrow> rejects e s r ((aa, ba, op) # p)"
  using accepts_cons_step
  by fastforce

lemma step_none_rejects: "step e s d (fst h) (fst (snd h)) (snd (snd h)) = None \<Longrightarrow> rejects e s d (h#t)"
  using no_step_none surjective_pairing by fastforce

lemma possible_steps_not_empty_iff: 
  "step e s d a b p \<noteq> None \<Longrightarrow>
   \<exists>aa ba. (aa, ba) |\<in>| possible_steps e s d a b p"
  apply (simp add: step_def)
  apply (case_tac "possible_steps e s d a b p")
   apply (simp add: random_member_def)
  by auto

lemma trace_reject: "(possible_steps e s d a b p = {||} \<or> (\<forall>(s', T) |\<in>| possible_steps e s d a b p. rejects e s' (apply_updates (Updates T) (join_ir b d) d) t)) = (rejects e s d ((a, b, p)#t))"
  apply safe
    apply (simp add: accepts_step)
  using accepts_cons apply auto[1]
  using accepts.step by blast

lemma trace_reject_no_possible_steps: "possible_steps e s d a b p = {||} \<Longrightarrow> rejects e s d ((a, b, p)#t)"
  using trace_reject by blast

lemma trace_reject_later: "\<forall>(s', T) |\<in>| possible_steps e s d a b p. rejects e s' (apply_updates (Updates T) (join_ir b d) d) t \<Longrightarrow> rejects e s d ((a, b, p)#t)"
  by (simp add: accepts_step case_prod_unfold)

lemma trace_reject_2: "(rejects e s d ((a, b, p)#t)) = (possible_steps e s d a b p = {||} \<or> (\<forall>(s', T) |\<in>| possible_steps e s d a b p. rejects e s' (apply_updates (Updates T) (join_ir b d) d) t))"
  using trace_reject by auto

lemma rejects_prefix_all_s_d: "\<forall>s d. rejects e s d t \<longrightarrow> rejects e s d (t @ t')"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: base)
next
  case (Cons a t)
  then show ?case
    by (metis (mono_tags, lifting) accepts_cons append_Cons case_prod_unfold fBexE fBexI)
qed

lemma rejects_prefix: "rejects e s d t \<Longrightarrow> rejects e s d (t @ t')"
  by (simp add: rejects_prefix_all_s_d)

lemma prefix_closure: "accepts e s d (t@t') \<Longrightarrow> accepts e s d t"
  using rejects_prefix_all_s_d by blast

lemma accepts_head: "accepts e s d (h#t) \<Longrightarrow> accepts e s d [h]"
  using accepts_cons accepts.base by auto

inductive gets_us_to :: "nat \<Rightarrow> transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> bool" where
  base: "s = target \<Longrightarrow> gets_us_to target _ s _ []" |
  step_some: "\<exists>(s', T) |\<in>| possible_steps e s d (fst h) (fst (snd h)) (snd (snd h)). gets_us_to target e s' (apply_updates (Updates T) (join_ir i r) r) t \<Longrightarrow> gets_us_to target e s r (h#t)" |
  step_none: "step e s r (fst h) (fst (snd h)) (snd (snd h)) = None \<Longrightarrow> s = target \<Longrightarrow> gets_us_to target e s r (h#t)"

lemma no_further_steps: "s \<noteq> s' \<Longrightarrow> \<not> gets_us_to s e s' r []"
  apply safe
  apply (rule gets_us_to.cases)
  by auto

primrec accepting_sequence :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> (transition \<times> cfstate \<times> registers) list \<Rightarrow> (transition \<times> cfstate \<times> registers) list option" where
  "accepting_sequence _ _ r [] obs = Some (rev obs)" |
  "accepting_sequence e s r (a#t) obs = (let
    poss = possible_steps e s r (fst a) (fst (snd a)) (snd (snd a));
    accepting = ffilter (\<lambda>(s', T). accepts e s' (apply_updates (Updates T) (join_ir (fst (snd a)) r) r) t) poss  in
    if accepting = {||} then
      None
    else let
      (s', T) = Eps (\<lambda>x. x |\<in>| accepting);
      r' = (apply_updates (Updates T) (join_ir (fst (snd a)) r) r) in
      accepting_sequence e s' r' t ((T, s', r')#obs)
  )"

definition enumerate_strings :: "transition_matrix \<Rightarrow> String.literal set" where
  "enumerate_strings e = \<Union> (image (\<lambda>(_, t). Transition.enumerate_strings t) (fset e))"

definition enumerate_ints :: "transition_matrix \<Rightarrow> int set" where
  "enumerate_ints e = \<Union> (image (\<lambda>(_, t). Transition.enumerate_ints t) (fset e))"

definition these :: "'a option list \<Rightarrow> 'a list" where
  "these as = map (\<lambda>x. case x of Some y \<Rightarrow> y) (filter (\<lambda>x. x \<noteq> None) as)"

lemma these_cons: "these (a#as) = (case a of None \<Rightarrow> these as | Some x \<Rightarrow> x#(these as))"
  apply (cases a)
   apply (simp add: these_def)
  by (simp add: these_def)

end
