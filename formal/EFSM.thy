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

definition apply_outputs :: "aexp list \<Rightarrow> datastate \<Rightarrow> value option list" where
  "apply_outputs p s = map (\<lambda>p. aval p s) p"

lemma apply_outputs_nth: "i < length p \<Longrightarrow> apply_outputs p s ! i = aval (p ! i) s"
  by (simp add: apply_outputs_def)

lemmas apply_outputs = datastate apply_outputs_def

lemma apply_outputs_empty [simp]: "apply_outputs [] s = []"
  by (simp add: apply_outputs_def)

lemma apply_outputs_preserves_length: "length (apply_outputs p s) = length p"
  by (simp add: apply_outputs_def)

lemma apply_outputs_literal: "P ! r = L v \<Longrightarrow>
       r < length (apply_outputs P (join_ir i c)) \<Longrightarrow>
       apply_outputs P (join_ir i c) ! r = Some v"
proof(induct P)
  case Nil
  then show ?case
    by (simp add: apply_outputs_preserves_length)
next
  case (Cons a P)
  then show ?case
    apply (simp add: apply_outputs_preserves_length)
    apply (simp add: apply_outputs_def)
    using less_Suc_eq_0_disj nth_map by auto
qed

lemma apply_outputs_register:
  "c $ p = Some v \<Longrightarrow>
   r < length (apply_outputs P (join_ir i c)) \<Longrightarrow>
   apply_outputs (list_update P r (V (R p))) (join_ir i c) ! r = Some v"
proof(induct P)
  case Nil
  then show ?case
    by (simp add: apply_outputs_preserves_length)
next
  case (Cons a P)
  then show ?case
    apply (simp add: apply_outputs_preserves_length)
    apply (simp add: apply_outputs_def)
    apply (cases r)
     apply (simp add: join_ir_def)
    by (simp add: join_ir_def)
qed

lemma apply_outputs_unupdated:
  "ia \<noteq> r \<Longrightarrow> 
   ia < length (apply_outputs P j) \<Longrightarrow>
   apply_outputs P j ! ia = apply_outputs (list_update P r v)j ! ia"
proof(induct P)
case Nil
  then show ?case
    by (simp add: apply_outputs_preserves_length)
next
  case (Cons a P)
  then show ?case
    apply (simp add: apply_outputs_preserves_length)
    apply (simp add: apply_outputs_def)
    apply (cases r)
     apply simp
    by (simp add: map_update nth_Cons')
qed

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

definition possible_steps :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (cfstate \<times> transition) fset" where
  "possible_steps e s r l i = fimage (\<lambda>((origin, dest), t). (dest, t)) (ffilter (\<lambda>((origin, dest::nat), t::transition). origin = s \<and> (Label t) = l \<and> (length i) = (Arity t) \<and> apply_guards (Guard t) (join_ir i r)) e)"

lemma in_possible_steps: "(a, bb) |\<in>| possible_steps b s r ab ba \<Longrightarrow> \<exists>s. ((s, a), bb) |\<in>| b"
  apply (simp add: possible_steps_def fimage_def ffilter_def fmember_def Abs_fset_inverse)
  by auto

lemma possible_steps_alt_aux: "(\<lambda>((origin, dest), t). (dest, t)) |`|
    ffilter (\<lambda>((origin, dest), t). origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guard t) (join_ir i r)) e =
    {|(d, t)|} \<Longrightarrow>
    ffilter
     (\<lambda>((origin, dest), t).
         origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guard t) (\<lambda>x. case x of vname.I n \<Rightarrow> input2state i $ n | R n \<Rightarrow> r $ n))
     e =
    {|((s, d), t)|}"
proof(induct e)
  case empty
  then show ?case
    by auto
next
  case (insert x e)
  then show ?case
    apply (cases x)
    apply (case_tac a)
    apply clarify
    apply simp
    apply (simp add: ffilter_finsert join_ir_def)
    apply (case_tac "aa = s")
     apply simp
     apply (case_tac "Label ba = l")
      apply simp
      apply (case_tac "length i = Arity ba")
       apply simp
       apply (case_tac "apply_guards (Guard ba) (case_vname (\<lambda>n. input2state i $ n) (\<lambda>n. r $  n))")
    by auto
qed

lemma possible_steps_alt: "(possible_steps e s r l i = {|(d, t)|}) = (ffilter
     (\<lambda>((origin, dest), t).
         origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guard t) (join_ir i r))
     e =
    {|((s, d), t)|})"
  apply standard
   apply (simp add: possible_steps_def possible_steps_alt_aux join_ir_def)
  by (simp add: possible_steps_def join_ir_def)

lemmas possible_steps_singleton = possible_steps_alt Abs_ffilter Set.filter_def
lemmas possible_steps_empty = possible_steps_def Abs_ffilter Set.filter_def

lemma singleton_dest: "fis_singleton (possible_steps e s r aa b) \<Longrightarrow>
       fthe_elem (possible_steps e s r aa b) = (baa, aba) \<Longrightarrow>
       ((s, baa), aba) |\<in>| e"
  apply (simp add: fis_singleton_def fthe_elem_def singleton_equiv)
  apply (simp add: possible_steps_def fmember_def)
  by auto

definition random_member :: "'a fset \<Rightarrow> 'a option" where
  "random_member f = (if f = {||} then None else Some (Eps (\<lambda>x. x |\<in>| f)))"

lemma random_member_singleton [simp]: "random_member {|a|} = Some a"
  by (simp add: random_member_def)

inductive accepts :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> bool" where
  base: "accepts e s d []" |                                         
  step: "\<exists>(s', T) |\<in>| possible_steps e s d l i.
         accepts e s' (apply_updates (Updates T) (join_ir i d) d) t \<Longrightarrow>
         accepts e s d ((l, i)#t)"

fun accepts_prim :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> bool" where
  "accepts_prim e s d [] = True" |
  "accepts_prim e s d ((l, i)#t) = (
    let poss_steps = possible_steps e s d l i in
    if fis_singleton poss_steps then
      let (s', T) = fthe_elem poss_steps in
      accepts_prim e s' (apply_updates (Updates T) (join_ir i d) d) t
    else
      (\<exists>(s', T) |\<in>| poss_steps. accepts_prim e s' (apply_updates (Updates T) (join_ir i d) d) t)
  )"

lemma accepts_cons: "accepts e s d (h#t) = (\<exists>(s', T) |\<in>| possible_steps e s d (fst h) (snd h). accepts e s' (apply_updates (Updates T) (join_ir (snd h) d) d) t)"
  apply (cases h)
  apply simp
  apply standard
   apply (metis accepts.simps fst_conv list.distinct(1) list.inject snd_conv)
  by (simp add: accepts.step)

lemma accepts_prim: "\<forall>d s. accepts e s d t = accepts_prim e s d t"
proof(induct t)
case Nil
  then show ?case
    by (simp add: accepts.base)
next
  case (Cons a t)
  then show ?case
    apply (cases a)
    apply (simp add: accepts_cons Let_def fis_singleton_alt)
    by auto
qed

lemma accepts_single_possible_step: "possible_steps e s d l i = {|(s', t)|} \<Longrightarrow>
       accepts e s' (apply_updates (Updates t) (join_ir i d) d) trace \<Longrightarrow>
       accepts e s d ((l, i)#trace)"
  by (simp add: accepts_prim)

abbreviation "rejects e s d t \<equiv> \<not> accepts e s d t"

lemma accepts_step_equiv: "accepts e s d ((l, i)#t) = (\<exists>(s', T) |\<in>| possible_steps e s d l i.
         accepts e s' (apply_updates (Updates T) (join_ir i d) d) t)"
  apply standard
   apply (metis accepts.simps list.simps(1) list.simps(3) prod.sel(1) prod.sel(2))
  by (simp add: accepts.step)

lemma accepts_must_be_possible_step: "accepts e s r (h # t) \<Longrightarrow> \<exists>aa ba. (aa, ba) |\<in>| possible_steps e s r (fst h) (snd h)"
  using accepts_step_equiv by fastforce

definition step :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (transition \<times> cfstate \<times> outputs \<times> registers) option" where
  "step e s r l i = (case random_member (possible_steps e s r l i) of
      None \<Rightarrow> None |
      Some (s', t) \<Rightarrow>  Some (t, s', apply_outputs (Outputs t) (join_ir i r), apply_updates (Updates t) (join_ir i r) r)
  )"

lemma step_some:
  "possibilities = (possible_steps e s r l i) \<Longrightarrow>
   random_member possibilities = Some (s', t) \<Longrightarrow>
   apply_outputs (Outputs t) (join_ir i r) = p \<Longrightarrow>
   apply_updates (Updates t) (join_ir i r) r = r' \<Longrightarrow>
   step e s r l i = Some (t, s', p, r')"
  by (simp add: step_def)

lemma no_possible_steps_1: "possible_steps e s r l i = {||} \<Longrightarrow> step e s r l i = None"
  by (simp add: step_def random_member_def)

primrec observe_all :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> (transition \<times> nat \<times> outputs \<times> registers) list" where
  "observe_all _ _ _ [] = []" |
  "observe_all e s r (h#t)  =
    (case (step e s r (fst h) (snd h)) of
      (Some (transition, s', outputs, updated)) \<Rightarrow> (((transition, s', outputs, updated)#(observe_all e s' updated t))) |
      _ \<Rightarrow> []
    )"

definition state :: "(transition \<times> nat \<times> outputs \<times> datastate) \<Rightarrow> nat" where
  "state x \<equiv> fst (snd x)"

definition observe_trace :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> observation" where
  "observe_trace e s r t \<equiv> map (\<lambda>(t,x,y,z). y) (observe_all e s r t)"

lemma observe_trace_empty [simp]: "observe_trace e s r [] = []"
  by (simp add: observe_trace_def)

lemma observe_trace_step: 
  "step e s r (fst h) (snd h) = Some (t, s', p, r') \<Longrightarrow>
   observe_trace e s' r' es = obs \<Longrightarrow>
   observe_trace e s r (h#es) = p#obs"
  by (simp add: observe_trace_def)

lemma observe_trace_possible_step:
  "possible_steps e s r (fst h) (snd h) = {|(s', t)|} \<Longrightarrow>
   apply_outputs (Outputs t) (join_ir (snd h) r) = p \<Longrightarrow>
   apply_updates (Updates t) (join_ir (snd h) r) r = r' \<Longrightarrow>
   observe_trace e s' r' es = obs \<Longrightarrow>
   observe_trace e s r (h#es) = p#obs"
  apply (rule observe_trace_step)
   apply (simp add: step_def random_member_def)
  by simp

lemma observe_trace_no_possible_step:
  "possible_steps e s r (fst h) (snd h) = {||} \<Longrightarrow>
   observe_trace e s r (h#es) = []"
  by (simp add: observe_trace_def step_def random_member_def)

definition observably_equivalent :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> trace \<Rightarrow> bool" where
  "observably_equivalent e1 e2 t = ((observe_trace e1 0 <> t) = (observe_trace e2 0 <> t))"

lemma observe_trace_no_possible_steps:
  "possible_steps e1 s1 r1 (fst h) (snd h) = {||} \<Longrightarrow>
   possible_steps e2 s2 r2 (fst h) (snd h) = {||} \<Longrightarrow>
   (observe_trace e1 s1 r1 (h#t)) = (observe_trace e2 s2 r2 (h#t))"
  by (simp add: observe_trace_def step_def random_member_def)

lemma observe_trace_one_possible_step:
  "possible_steps e1 s1 r (fst h) (snd h) = {|(s1', t1)|} \<Longrightarrow>
   possible_steps e2 s2 r (fst h) (snd h) = {|(s2', t2)|} \<Longrightarrow>
   apply_outputs (Outputs t1) (join_ir (snd h) r) = apply_outputs (Outputs t2) (join_ir (snd h) r) \<Longrightarrow>
   apply_updates (Updates t1) (join_ir (snd h) r) r = r' \<Longrightarrow>
   apply_updates (Updates t2) (join_ir (snd h) r) r = r' \<Longrightarrow>
   (observe_trace e1 s1' r' t) = (observe_trace e2 s2' r' t) \<Longrightarrow>
   (observe_trace e1 s1 r (h#t)) = (observe_trace e2 s2 r (h#t))"
  by (simp add: observe_trace_def step_def)

lemma observably_equivalent_no_possible_step: 
  "possible_steps e1 s1 r1 (fst h) (snd h) = {||} \<Longrightarrow>
   possible_steps e2 s2 r2 (fst h) (snd h) = {||} \<Longrightarrow>
   observe_trace e1 s1 r1 (h#t) = observe_trace e2 s2 r2 (h#t)"
  by (simp add: observe_trace_no_possible_step)

lemma observably_equivalent_reflexive: "observably_equivalent e1 e1 t"
  by (simp add: observably_equivalent_def)

lemma observably_equivalent_symmetric: "observably_equivalent e1 e2 t = observably_equivalent e2 e1 t"
  using observably_equivalent_def by auto

lemma observably_equivalent_transitive:
  "observably_equivalent e1 e2 t \<Longrightarrow>
   observably_equivalent e2 e3 t \<Longrightarrow>
   observably_equivalent e1 e3 t"
  by (simp add: observably_equivalent_def)

lemma observe_trace_preserves_length: "length (observe_all e s r t) = length (observe_trace e s r t)"
  by (simp add: observe_trace_def)

lemma length_observation_leq_length_trace: "\<And>s r. length (observe_all e s r t) \<le> length t"
proof (induction t)
  case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case
    apply (case_tac "step e s r (fst a) (snd a)")
    by auto
qed

lemma accepts_possible_steps_not_empty: "accepts e s d (h#t) \<Longrightarrow> possible_steps e s d (fst h) (snd h) \<noteq> {||}"
  apply (rule accepts.cases)
  by auto

lemma accepts_must_be_step: "accepts e s d (h#ts) \<Longrightarrow> \<exists>t s' p d'. step e s d (fst h) (snd h) = Some (t, s', p, d')"
  apply (cases h)
  apply (simp add: accepts_step_equiv step_def)
  apply clarify
  apply (case_tac "(possible_steps e s d a b)")
   apply (simp add: random_member_def)
  apply (simp add: random_member_def)
  apply (case_tac "SOME xa. xa = x \<or> xa |\<in>| S'")
  by simp

lemma accepts_cons_step: "accepts e s r (h # t) \<Longrightarrow> step e s r (fst h) (snd h) \<noteq>  None"
  by (simp add: accepts_must_be_step)

abbreviation accepts_trace :: "transition_matrix \<Rightarrow> trace \<Rightarrow> bool" where
  "accepts_trace e t \<equiv> accepts e 0 <> t"

lemma no_step_none: "step e s r aa ba = None \<Longrightarrow> rejects e s r ((aa, ba) # p)"
  using accepts_cons_step by fastforce

lemma step_none_rejects: "step e s d (fst h) (snd h) = None \<Longrightarrow> rejects e s d (h#t)"
  using no_step_none surjective_pairing by fastforce

lemma possible_steps_not_empty_iff: 
  "step e s d a b \<noteq> None \<Longrightarrow>
   \<exists>aa ba. (aa, ba) |\<in>| possible_steps e s d a b"
  apply (simp add: step_def)
  apply (case_tac "possible_steps e s d a b")
   apply (simp add: random_member_def)
  by auto

lemma trace_reject: "(possible_steps e s d a b = {||} \<or> (\<forall>(s', T) |\<in>| possible_steps e s d a b. rejects e s' (apply_updates (Updates T) (join_ir b d) d) t)) = (rejects e s d ((a, b)#t))"
  apply safe
  using accepts_possible_steps_not_empty apply auto[1]
  using accepts_cons apply auto[1]
  using accepts.step by blast

lemma trace_reject_no_possible_steps: "possible_steps e s d a b = {||} \<Longrightarrow> rejects e s d ((a, b)#t)"
  using accepts_possible_steps_not_empty by auto

lemma trace_reject_later: "\<forall>(s', T) |\<in>| possible_steps e s d a b. rejects e s' (apply_updates (Updates T) (join_ir b d) d) t \<Longrightarrow> rejects e s d ((a, b)#t)"
  using accepts_cons by auto

lemma trace_reject_2: "(rejects e s d ((a, b)#t)) = (possible_steps e s d a b = {||} \<or> (\<forall>(s', T) |\<in>| possible_steps e s d a b. rejects e s' (apply_updates (Updates T) (join_ir b d) d) t))"
  by (metis (mono_tags, lifting) accepts_cons case_prod_unfold fBallI fBexI fst_conv snd_conv trace_reject_later trace_reject_no_possible_steps)

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

inductive gets_us_to :: "cfstate \<Rightarrow> transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> bool" where
  base: "s = target \<Longrightarrow> gets_us_to target _ s _ []" |
  step_some: "\<exists>(s', T) |\<in>| possible_steps e s d (fst h) (snd h). gets_us_to target e s' (apply_updates (Updates T) (join_ir i r) r) t \<Longrightarrow> gets_us_to target e s r (h#t)" |
  step_none: "step e s r (fst h) (snd h) = None \<Longrightarrow> s = target \<Longrightarrow> gets_us_to target e s r (h#t)"

definition "trace_gets_us_to s e = gets_us_to s e 0 <>"

lemma no_further_steps: "s \<noteq> s' \<Longrightarrow> \<not> gets_us_to s e s' r []"
  apply safe
  apply (rule gets_us_to.cases)
  by auto

primrec accepting_sequence :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> (transition \<times> cfstate \<times> outputs \<times> registers) list \<Rightarrow> (transition \<times> cfstate \<times> outputs \<times> registers) list option" where
  "accepting_sequence _ _ r [] obs = Some (rev obs)" |
  "accepting_sequence e s r (a#t) obs = (let
    poss = possible_steps e s r (fst a) (snd a);
    accepting = ffilter (\<lambda>(s', T). accepts e s' (apply_updates (Updates T) (join_ir (snd a) r) r) t) poss  in
    if accepting = {||} then
      None
    else let
      (s', T) = Eps (\<lambda>x. x |\<in>| accepting);
      r' = (apply_updates (Updates T) (join_ir (snd a) r) r) in
      accepting_sequence e s' r' t ((T, s', (apply_outputs (Outputs T) (join_ir (snd a) r)), r')#obs)
  )"

lemma observe_trace_empty_iff: "(observe_trace e s r t = []) = (observe_all e s r t = [])"
  by (simp add: observe_trace_def)

definition enumerate_strings :: "transition_matrix \<Rightarrow> String.literal set" where
  "enumerate_strings e = \<Union> (image (\<lambda>(_, t). Transition.enumerate_strings t) (fset e))"

definition enumerate_ints :: "transition_matrix \<Rightarrow> int set" where
  "enumerate_ints e = \<Union> (image (\<lambda>(_, t). Transition.enumerate_ints t) (fset e))"

definition max_reg :: "transition_matrix \<Rightarrow> nat option" where
  "max_reg e = (let maxes = (fimage (\<lambda>(_, t). Transition.max_reg t) e) in if maxes = {||} then None else fMax maxes)"

definition max_output :: "transition_matrix \<Rightarrow> nat" where
  "max_output e = fMax (fimage (\<lambda>(_, t). length (Outputs t)) e)"

definition all_regs :: "transition_matrix \<Rightarrow> nat set" where
  "all_regs e = \<Union> (image (\<lambda>(_, t). enumerate_registers t) (fset e))"

definition max_input :: "transition_matrix \<Rightarrow> nat option" where
  "max_input e = fMax (fimage (\<lambda>(_, t). Transition.max_input t) e)"

fun maxS :: "transition_matrix \<Rightarrow> nat" where
  "maxS t = (if t = {||} then 0 else fMax ((fimage (\<lambda>((origin, dest), t). origin) t) |\<union>| (fimage (\<lambda>((origin, dest), t). dest) t)))"

definition max_int :: "transition_matrix \<Rightarrow> int" where
  "max_int e = Max (insert 0 (enumerate_ints e))"
end
