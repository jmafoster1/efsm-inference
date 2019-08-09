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
    apply (simp add: ffilter_empty)
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

lemma singleton_dest: "fis_singleton (possible_steps e s r aa b) \<Longrightarrow>
       fthe_elem (possible_steps e s r aa b) = (baa, aba) \<Longrightarrow>
       ((s, baa), aba) |\<in>| e"
  apply (simp add: fis_singleton_def fthe_elem_def singleton_equiv)
  apply (simp add: possible_steps_def fmember_def)
  by auto

lemmas ffilter = ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def
lemmas possible_steps_singleton = ffilter possible_steps_alt
lemmas possible_steps_empty = ffilter possible_steps_def

definition random_member :: "'a fset \<Rightarrow> 'a option" where
  "random_member f = (if f = {||} then None else Some (Eps (\<lambda>x. x |\<in>| f)))"

inductive accepts :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> bool" where
  base: "accepts e s d []" |                                         
  step: "\<exists>(s', T) |\<in>| possible_steps e s d l i.
         accepts e s' (apply_updates (Updates T) (join_ir i d) d) t \<Longrightarrow>
         accepts e s d ((l, i)#t)"

lemma accepts_step: "\<exists>(s', T) |\<in>| possible_steps e s d (fst h) (snd h).
         accepts e s' (apply_updates (Updates T) (join_ir (snd h) d) d) t \<Longrightarrow>
         accepts e s d (h#t)"
  apply (cases h)
  by (simp add: accepts.step)

lemma accepts_step_equiv: "accepts e s d ((l, i)#t) = (\<exists>(s', T) |\<in>| possible_steps e s d l i.
         accepts e s' (apply_updates (Updates T) (join_ir i d) d) t)"
  apply standard
   apply (metis accepts.simps list.simps(1) list.simps(3) prod.sel(1) prod.sel(2))
  by (simp add: accepts.step)

definition step :: "trace \<Rightarrow> transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (transition \<times> cfstate \<times> outputs \<times> registers) option" where
  "step tr e s r l i = (let 
    poss_steps = (possible_steps e s r l i);
    possibilities = ffilter (\<lambda>(s', t). accepts e s' (apply_updates (Updates t) (join_ir i r) r) tr) poss_steps in
    case random_member possibilities of
      None \<Rightarrow> None |
      Some (s', t) \<Rightarrow>  Some (t, s', apply_outputs (Outputs t) (join_ir i r), apply_updates (Updates t) (join_ir i r) r)
  )"

lemma step_some:
  "poss_steps = (possible_steps e s r l i) \<Longrightarrow>
   possibilities = ffilter (\<lambda>(s', t). accepts e s' (apply_updates (Updates t) (join_ir i r) r) tr) poss_steps \<Longrightarrow>
   random_member possibilities = Some (s', t) \<Longrightarrow>
   apply_outputs (Outputs t) (join_ir i r) = p \<Longrightarrow>
   apply_updates (Updates t) (join_ir i r) r = r' \<Longrightarrow>
   step tr e s r l i = Some (t, s', p, r')"
  by (simp add: step_def)

(*
definition step :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (transition \<times> cfstate \<times> outputs \<times> registers) option" where
"step e s r l i = (case random_member (possible_steps e s r l i) of
                    None \<Rightarrow> None |
                     Some (s', t) \<Rightarrow>
                     Some (t, s', (apply_outputs (Outputs t) (join_ir i r)), (apply_updates (Updates t) (join_ir i r) r))
                  )"
*)

lemma no_possible_steps_1: "possible_steps e s r l i = {||} \<Longrightarrow> step t e s r l i = None"
  by (simp add: step_def ffilter_empty random_member_def)

primrec observe_all :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> (transition \<times> nat \<times> outputs \<times> registers) list" where
  "observe_all _ _ _ [] = []" |
  "observe_all e s r (h#t) =
    (case (step t e s r (fst h) (snd h)) of
      (Some (transition, s', outputs, updated)) \<Rightarrow> (((transition, s', outputs, updated)#(observe_all e s' updated t))) |
      _ \<Rightarrow> []
    )"

definition state :: "(transition \<times> nat \<times> outputs \<times> datastate) \<Rightarrow> nat" where
  "state x \<equiv> fst (snd x)"

definition observe_trace :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> observation" where
  "observe_trace e s r t \<equiv> map (\<lambda>(t,x,y,z). y) (observe_all e s r t)"

lemma observe_trace_empty [simp]: "observe_trace e s r [] = []"
  by (simp add: observe_trace_def)

lemma observe_trace_step: "
       step es e s r (fst h) (snd h) = Some (t, s', p, r') \<Longrightarrow>
       observe_trace e s' r' es = obs \<Longrightarrow>
       observe_trace e s r (h#es) = p#obs"
  by (simp add: observe_trace_def)

lemma observe_trace_possible_step:
  "possible_steps e s r (fst h) (snd h) = {|(s', t)|} \<Longrightarrow>
   accepts e s' (apply_updates (Updates t) (join_ir (snd h) r) r) es \<Longrightarrow>
   apply_outputs (Outputs t) (join_ir (snd h) r) = p \<Longrightarrow>
   apply_updates (Updates t) (join_ir (snd h) r) r = r' \<Longrightarrow>
   observe_trace e s' r' es = obs \<Longrightarrow>
   observe_trace e s r (h#es) = p#obs"
  using observe_trace_step[of es e s r h t s' p r' obs]
        step_some[of "{|(s', t)|}" e s r "fst h" "snd h" "{|(s', t)|}" es s' t p r']
  by (simp add: ffilter_singleton random_member_def)

lemma observe_trace_no_possible_step:
  "possible_steps e s r (fst h) (snd h) = {||} \<Longrightarrow>
   observe_trace e s r (h#es) = []"
  by (simp add: observe_trace_def step_def random_member_def ffilter_empty)

lemma observe_empty: "t = [] \<Longrightarrow> observe_trace e 0 <> t = []"
  by (simp add: observe_trace_def)

definition efsm_equiv :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> trace \<Rightarrow> bool" where
  "efsm_equiv e1 e2 t \<equiv> ((observe_trace e1 0 <> t) = (observe_trace e2 0 <> t))"

lemma efsm_equiv_possible_step: 
  "possible_steps e1 s1 r1 (fst h) (snd h) = {|(s1', t1)|} \<Longrightarrow>
   possible_steps e2 s2 r2 (fst h) (snd h) = {|(s2', t2)|} \<Longrightarrow>
   accepts e1 s1' (apply_updates (Updates t1) (join_ir (snd h) r1) r1) t \<Longrightarrow>
   accepts e2 s2' (apply_updates (Updates t2) (join_ir (snd h) r2) r2) t \<Longrightarrow>
   apply_outputs (Outputs t1) (join_ir (snd h) r1) = apply_outputs (Outputs t2) (join_ir (snd h) r2) \<Longrightarrow>
   apply_updates (Updates t1) (join_ir (snd h) r1) r1 = r1' \<Longrightarrow>
   apply_updates (Updates t2) (join_ir (snd h) r2) r2 = r2' \<Longrightarrow>
   observe_trace e1 s1' r1' t = observe_trace e2 s2' r2' t \<Longrightarrow>
   observe_trace e1 s1 r1 (h#t) = observe_trace e2 s2 r2 (h#t)"
  by (simp add: observe_trace_possible_step)

lemma efsm_equiv_no_possible_step: 
  "possible_steps e1 s1 r1 (fst h) (snd h) = {||} \<Longrightarrow>
   possible_steps e2 s2 r2 (fst h) (snd h) = {||} \<Longrightarrow>
   observe_trace e1 s1 r1 (h#t) = observe_trace e2 s2 r2 (h#t)"
  by (simp add: observe_trace_no_possible_step)

lemma efsm_equiv_reflexive: "efsm_equiv e1 e1 t"
  by (simp add: efsm_equiv_def)

lemma efsm_equiv_symmetric: "efsm_equiv e1 e2 t \<equiv> efsm_equiv e2 e1 t"
  apply (simp add: efsm_equiv_def)
  by argo

lemma efsm_equiv_transitive: "efsm_equiv e1 e2 t \<and> efsm_equiv e2 e3 t \<longrightarrow> efsm_equiv e1 e3 t"
  by (simp add: efsm_equiv_def)

lemmas observations = observe_trace_def step_def possible_steps_def

lemma different_observation_techniques: "length(observe_all e s r t) = length(observe_trace e s r t)"
  by (simp add: observe_trace_def)

lemma length_observe_all_restricted: "\<And>s r. length (observe_all e s r t) \<le> length t"
proof (induction t)
  case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case
  proof cases
    assume "step t e s r (fst a) (snd a) = None"
    then show ?thesis
      by simp
  next
    assume "step t e s r (fst a) (snd a) \<noteq>  None"
    with Cons show ?thesis
      by auto
  qed
qed

lemma accepts_must_be_possible_step: "accepts e s d (h#t) \<Longrightarrow> possible_steps e s d (fst h) (snd h) \<noteq> {||}"
  apply (rule accepts.cases)
  by auto

lemma accepts_must_be_step: "accepts e s d (h#ts) \<Longrightarrow> \<exists>t s' p d'. step ts e s d (fst h) (snd h) = Some (t, s', p, d')"
  apply (cases h)
  apply (simp add: accepts_step_equiv step_def)
  apply clarify
  apply (case_tac "(ffilter (\<lambda>(s', t). accepts e s' (apply_updates (Updates t) (join_ir b d) d) ts) (possible_steps e s d a b))")
   apply (simp add: random_member_def)
   apply auto[1]
  apply (simp add: random_member_def)
  by (metis (mono_tags, lifting) case_prod_conv old.prod.exhaust)

lemma accepts_cons: "accepts e s d (h#t) = (\<exists>(s', T) |\<in>| possible_steps e s d (fst h) (snd h). accepts e s' (apply_updates (Updates T) (join_ir (snd h) d) d) t)"
  apply (cases h)
  apply simp
  apply standard
   apply (metis accepts.simps fst_conv list.distinct(1) list.inject snd_conv)
  by (simp add: accepts.step)

lemma accepts_cons_step: "accepts e s r (h # t) \<Longrightarrow> step t e s r (fst h) (snd h) \<noteq>  None"
  by (simp add: accepts_must_be_step)

lemma step_some_updated: "step t e s r l i = Some (transition, s', outputs, updated) \<Longrightarrow>
       updated = (apply_updates (Updates transition) (join_ir i r) r)"
  apply (simp add: step_def random_member_def Let_def)
  apply (case_tac "(ffilter (\<lambda>(s', ta). accepts e s' (apply_updates (Updates ta) (join_ir i r) r) t) (possible_steps e s r l i)) = {||}")
   apply simp
  apply simp
  apply (case_tac "SOME x.
             x |\<in>| possible_steps e s r l i \<and>
             (case x of (s', ta) \<Rightarrow> accepts e s' (apply_updates (Updates ta) (join_ir i r) r) t)")
  by auto

lemma step_in_possible_steps:
  "step t e s r l i = Some (transition, s', outputs, updated) \<Longrightarrow>
   (s', transition) |\<in>| possible_steps e s r l i"
  apply (simp add: step_def Let_def random_member_def)
  apply (case_tac "ffilter (\<lambda>(s', ta). accepts e s' (apply_updates (Updates ta) (join_ir i r) r) t) (possible_steps e s r l i) = {||}")
   apply simp
  apply simp
  apply (case_tac " SOME x.
             x |\<in>| possible_steps e s r l i \<and>
             (case x of (s', ta) \<Rightarrow> accepts e s' (apply_updates (Updates ta) (join_ir i r) r) t)")
  apply simp
  apply clarify
  by (metis (mono_tags, lifting) equalsffemptyI ffmember_filter someI)

abbreviation accepts_trace :: "transition_matrix \<Rightarrow> trace \<Rightarrow> bool" where
  "accepts_trace e t \<equiv> accepts e 0 <> t"

lemma no_step_none: "step p e s r aa ba = None \<Longrightarrow> \<not>accepts e s r ((aa, ba) # p)"
  apply clarify
  apply (rule accepts.cases)
    apply simp
   apply simp
  apply clarify
  apply (simp add: step_def)
  apply (case_tac "(possible_steps e s r aa ba) = {||}")
   apply (simp add: ffilter_empty random_member_def)
  apply (case_tac "(ffilter (\<lambda>(s', t). accepts e s' (apply_updates (Updates t) (join_ir ba r) r) p)
                    (possible_steps e s r aa ba)) = {||}")
   apply (simp add: random_member_def)
  apply auto[1]
  apply (simp add: random_member_def)
  apply (case_tac "SOME x.
                    x |\<in>| possible_steps e s r aa ba \<and>
                    (case x of (s', t) \<Rightarrow> accepts e s' (apply_updates (Updates t) (join_ir ba r) r) p)")
  by simp

lemma step_none_inaccepts: "((step t e s d (fst h) (snd h)) = None) \<Longrightarrow> \<not> (accepts e s d (h#t))"
  using no_step_none surjective_pairing by fastforce

lemma accepts_head: "accepts e s d (h#t) \<Longrightarrow> accepts e s d [h]"
  apply (case_tac h)
  apply simp
  apply (rule accepts.step)
  apply (simp add: accepts.base)
  using accepts_cons by auto

lemma accepts_possible_steps: 
"step t e s d a b \<noteq> None \<Longrightarrow>
 \<exists>aa ba. (aa, ba) |\<in>| possible_steps e s d a b"
  apply (simp add: step_def)
  apply (case_tac "possible_steps e s d a b")
   apply (simp add: ffilter_empty random_member_def)
  by auto

lemma accepts_single_event: 
  assumes prem: "step [] e s d a b \<noteq> None"
  shows "accepts e s d [(a, b)]"
proof-
  have pair_true: "(\<lambda>(s', t). True) = (\<lambda>x. True)"
    apply (rule ext)
    by simp
  show ?thesis
    apply (rule accepts.step)
    apply (simp add: accepts.base pair_true)
    using accepts_possible_steps prem by blast
qed

lemma inaccepts_single_event: "\<not> accepts e s d [(a, b)] \<Longrightarrow> step [] e s d a b = None"
  using accepts_single_event by blast

lemma single_event_reject: "\<not> accepts e s d [(a, b)] = (step [] e s d a b = None)"
  using accepts_single_event no_step_none by blast

lemma trace_reject: "(possible_steps e s d a b = {||} \<or> (\<forall>(s', T) |\<in>| possible_steps e s d a b. \<not>accepts e s' (apply_updates (Updates T) (join_ir b d) d) t)) = (\<not> accepts e s d ((a, b)#t))"
  apply safe
  using accepts_must_be_possible_step apply auto[1]
  using accepts_cons apply auto[1]
  using accepts.step by blast

lemma trace_reject_2: "(\<not> accepts e s d ((a, b)#t)) = (possible_steps e s d a b = {||} \<or> (\<forall>(s', T) |\<in>| possible_steps e s d a b. \<not>accepts e s' (apply_updates (Updates T) (join_ir b d) d) t))"
  using trace_reject 
  by simp

lemma rejects_prefix_all_s_d: "\<forall>s d. \<not>accepts e s d t \<longrightarrow> \<not>accepts e s d (t @ t')"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: base)
next
  case (Cons a t)
  then show ?case
    apply (cases a)
    apply (simp add: trace_reject_2)
    by blast
qed

lemma rejects_prefix: " \<not>accepts e s d t \<Longrightarrow> \<not>accepts e s d (t @ t')"
  by (simp add: rejects_prefix_all_s_d)

lemma step_none_inaccepts_append: "step t e s d (fst a) (snd a) = None \<Longrightarrow> \<not>accepts e s d (a # t) \<and> \<not>accepts e s d (a # t @ t')"
  by (metis rejects_prefix Cons_eq_appendI step_none_inaccepts)

lemma prefix_closure: "accepts e s d (t@t') \<Longrightarrow> accepts e s d t"
  using rejects_prefix_all_s_d by blast

lemma inaccepts_prefix: "\<not>accepts e s d t \<Longrightarrow> \<not>accepts e s d (t@t')"
  apply (rule ccontr)
  by (simp add: prefix_closure)

lemma length_observe_empty_trace: "length (observe_all e aa b []) = 0"
  by simp

lemma step_length_suc: "step t e 0 <> (fst a) (snd a) = Some (tr, aa, ab, b) \<Longrightarrow> length (observe_all e 0 <> (a # t)) = Suc (length (observe_all e aa b t))"
  by simp

inductive gets_us_to :: "nat \<Rightarrow> transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> bool" where
  base: "s = target \<Longrightarrow> gets_us_to target _ s _ []" |
  step_some: "\<exists>(s', T) |\<in>| possible_steps e s d (fst h) (snd h). gets_us_to target e s' (apply_updates (Updates T) (join_ir i r) r) t \<Longrightarrow> gets_us_to target e s r (h#t)" |
  step_none: "step t e s r (fst h) (snd h) = None \<Longrightarrow> s = target \<Longrightarrow> gets_us_to target e s r (h#t)"

lemma "gets_us_to target e s r t \<Longrightarrow> accepts e s r t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: accepts.base)
next
  case (Cons a t)
  then show ?case sorry
qed

lemma no_further_steps: "s \<noteq> s' \<Longrightarrow> \<not> gets_us_to s e s' r []"
  apply safe
  apply (rule gets_us_to.cases)
  by auto

lemma empty_gets_us_to_state: "gets_us_to s e s' r [] \<Longrightarrow> s = s'"
  using no_further_steps by blast

definition incoming_transition_to :: "transition_matrix \<Rightarrow> nat \<Rightarrow> bool" where
  "incoming_transition_to t s = ((ffilter (\<lambda>((from, to), t). to = s) t) \<noteq> {||})"

lemma incoming_transition_alt_def: "incoming_transition_to e n = (\<exists>t from. ((from, n), t) |\<in>| e)"
  apply (simp add: incoming_transition_to_def)
  apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse)
  apply (simp add: fmember_def)
  apply (simp add: Set.filter_def)
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

end
