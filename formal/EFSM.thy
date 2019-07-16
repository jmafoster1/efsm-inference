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
type_synonym transition_matrix = "((nat \<times> nat) \<times> transition) fset"

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

lemmas apply_outputs = datastate apply_outputs_def

lemma apply_outputs_empty [simp]: "apply_outputs [] s = []"
  by (simp add: apply_outputs_def)

lemma apply_outputs_preserves_length: "length (apply_outputs p s) = length p"
  by (simp add: apply_outputs_def)

definition apply_guards :: "gexp list \<Rightarrow> datastate \<Rightarrow> bool" where
  "apply_guards G s = (\<forall>g \<in> set (map (\<lambda>g. gval g s) G). g = true)"

lemmas apply_guards = datastate apply_guards_def gval.simps ValueEq_def ValueGt_def

lemma apply_guards_empty [simp]: "apply_guards [] s"
  by (simp add: apply_guards_def)

lemma apply_guards_cons: "apply_guards (a # G) c = (gval a c = true \<and> apply_guards G c)"
  by (simp add: apply_guards_def)

lemma apply_guards_append: "apply_guards (a@a') s = (apply_guards a s \<and> apply_guards a' s)"
  apply (simp add: apply_guards_def)
  by auto

lemma apply_guards_foldr: "apply_guards G s = (gval (foldr gAnd G (Bc True)) s = true)"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: apply_guards_def gval.simps)
next
  case (Cons a G)
  then show ?case
    apply (simp only: foldr.simps comp_def)
    by (simp add: apply_guards_cons gval_gAnd maybe_and_true)
qed

lemma apply_guards_rev: "apply_guards G s = apply_guards (rev G) s"
  by (simp add: apply_guards_def)

lemma apply_guards_fold: "apply_guards G s = (gval (fold gAnd G (Bc True)) s = true)"
  using apply_guards_rev
  by (simp add: foldr_conv_fold apply_guards_foldr)

lemma fold_apply_guards: "(gval (fold gAnd G (Bc True)) s = true) = apply_guards G s"
  by (simp add: apply_guards_fold)

lemma foldr_apply_guards: "(gval (foldr gAnd G (Bc True)) s = true) = apply_guards G s"
  by (simp add: apply_guards_foldr)

lemma apply_guards_subset: "set g' \<subseteq> set g \<Longrightarrow> apply_guards g c \<longrightarrow> apply_guards g' c"
proof(induct g)
  case Nil
  then show ?case
    by simp
next
  case (Cons a g)
  then show ?case
    apply (simp add: apply_guards_def)
    by auto
qed

primrec apply_updates :: "updates \<Rightarrow> datastate \<Rightarrow> registers \<Rightarrow> registers" where
  "apply_updates [] _ new = new" |
  "apply_updates (h#t) old new = (\<lambda>x. if x = (fst h) then (aval (snd h) old) else (apply_updates t old new) x)"

lemma r_not_updated_stays_the_same: "r \<notin> fst ` set U \<Longrightarrow>
    apply_updates U c d r = d r"
proof(induct U)
  case Nil
  then show ?case
    by simp
next
  case (Cons a U)
  then show ?case
    by simp
qed

definition possible_steps :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (cfstate \<times> transition) fset" where
  "possible_steps e s r l i = fimage (\<lambda>((origin, dest), t). (dest, t)) (ffilter (\<lambda>((origin, dest::nat), t::transition). origin = s \<and> (Label t) = l \<and> (length i) = (Arity t) \<and> apply_guards (Guard t) (join_ir i r)) e)"

lemma possible_steps_alt_aux: "(\<lambda>((origin, dest), t). (dest, t)) |`|
    ffilter (\<lambda>((origin, dest), t). origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guard t) (join_ir i r)) e =
    {|(d, t)|} \<Longrightarrow>
    ffilter
     (\<lambda>((origin, dest), t).
         origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guard t) (\<lambda>x. case x of vname.I n \<Rightarrow> input2state i n | R n \<Rightarrow> r n))
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
       apply (case_tac "apply_guards (Guard ba) (case_vname (\<lambda>n. input2state i n) (\<lambda>n. r n))")
    by auto
qed

lemma possible_steps_alt: "(possible_steps e s r l i = {|(d, t)|}) = (ffilter
     (\<lambda>((origin, dest), t).
         origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guard t) (\<lambda>x. case x of vname.I n \<Rightarrow> input2state i n | R n \<Rightarrow> r n))
     e =
    {|((s, d), t)|})"
  apply standard
   apply (simp add: possible_steps_def possible_steps_alt_aux)
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

definition step :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (transition \<times> cfstate \<times> outputs \<times> registers) option" where
"step e s r l i = (let possibilities = possible_steps e s r l i in
                   if possibilities = {||} then None
                   else
                     let (s', t) = Eps (\<lambda>x. x |\<in>| possibilities) in
                     Some (t, s', (apply_outputs (Outputs t) (join_ir i r)), (apply_updates (Updates t) (join_ir i r) r))
                  )"

lemma no_possible_steps_1: "possible_steps e s r l i = {||} \<Longrightarrow> step e s r l i = None"
  by (simp add: step_def)

lemma no_possible_steps_2: "step e s r l i = None \<Longrightarrow> possible_steps e s r l i = {||}"
  apply (simp add: step_def Let_def)
  apply (case_tac "possible_steps e s r l i = {||}")
   apply simp
  apply (case_tac "SOME x. x |\<in>| possible_steps e s r l i")
  by simp

lemma no_possible_steps_3: "(possible_steps e s r l i = {||}) = (step e s r l i = None)"
  using no_possible_steps_1 no_possible_steps_2 by blast

lemma no_possible_steps_4: "(step e s r l i = None) = (possible_steps e s r l i = {||})"
  using no_possible_steps_1 no_possible_steps_2 by blast

lemma one_possible_step: "possible_steps e s r l i = {|(s', t)|} \<Longrightarrow>
       apply_outputs (Outputs t) (join_ir i r) = p \<Longrightarrow>
       apply_updates (Updates t) (join_ir i r) r = u \<Longrightarrow>
       step e s r l i = Some (t, s', p, u)"
  by (simp add: step_def)

lemma step_empty[simp]:"step {||} s r l i = None"
  by (simp add: step_def possible_steps_def ffilter_empty)

primrec observe_all :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> (transition \<times> nat \<times> outputs \<times> registers) list" where
  "observe_all _ _ _ [] = []" |
  "observe_all e s r (h#t) =
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

lemma observe_trace_step: "
       step e s r (fst h) (snd h) = Some (t, s', p, r') \<Longrightarrow>
       observe_trace e s' r' es = obs \<Longrightarrow>
       observe_trace e s r (h#es) = p#obs"
  by (simp add: observe_trace_def)

lemma observe_trace_possible_step: "possible_steps e s r (fst h) (snd h) = {|(s', t)|} \<Longrightarrow>
       apply_outputs (Outputs t) (join_ir (snd h) r) = p \<Longrightarrow>
       apply_updates (Updates t) (join_ir (snd h) r) r = r' \<Longrightarrow>
       observe_trace e s' r' es = obs \<Longrightarrow>
       observe_trace e s r (h#es) = p#obs"
  using observe_trace_step one_possible_step
  by simp

lemma observe_trace_no_possible_step: "possible_steps e s r (fst h) (snd h) = {||} \<Longrightarrow>
       observe_trace e s r (h#es) = []"
  by (simp add: observe_trace_def step_def)

lemma observe_empty: "t = [] \<Longrightarrow> observe_trace e 0 <> t = []"
  by (simp add: observe_trace_def)

definition efsm_equiv :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> trace \<Rightarrow> bool" where
  "efsm_equiv e1 e2 t \<equiv> ((observe_trace e1 0 <> t) = (observe_trace e2 0 <> t))"

lemma efsm_equiv_possible_step: 
  "possible_steps e1 s1 r1 (fst h) (snd h) = {|(s1', t1)|} \<Longrightarrow>
   possible_steps e2 s2 r2 (fst h) (snd h) = {|(s2', t2)|} \<Longrightarrow>
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
    assume "step e s r (fst a) (snd a) = None"
    then show ?thesis by simp
  next
    assume "step e s r (fst a) (snd a) \<noteq>  None"
    with Cons show ?thesis by(auto)
  qed
qed

inductive accepts :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> bool" where
  base: "accepts e s d []" |                                         
  step: "\<exists>(s', T) |\<in>| possible_steps e s d (fst h) (snd h). accepts e s' (apply_updates (Updates T) (join_ir (snd h) d) d) t \<Longrightarrow>
         accepts e s d (h#t)"

lemma accepts_cons: "accepts e s d (h#t) = (\<exists>(s', T) |\<in>| possible_steps e s d (fst h) (snd h). accepts e s' (apply_updates (Updates T) (join_ir (snd h) d) d) t)"
  apply standard
  apply (metis (mono_tags) accepts.simps list.distinct(1) list.inject)
  by (simp add: accepts.step)

lemma accepts_cons_step: "accepts e s r (a # t) \<Longrightarrow> step e s r (fst a) (snd a) \<noteq>  None"
  using accepts_cons no_possible_steps_4 by auto

lemma step_some_updated: "step e s r l i = Some (transition, s', outputs, updated) \<Longrightarrow>
       updated = (apply_updates (Updates transition) (join_ir i r) r)"
  apply (simp add: step_def Let_def)
  apply (case_tac "possible_steps e s r l i = {||}")
   apply simp
  apply simp
  apply (case_tac "SOME x. x |\<in>| possible_steps e s r l i")
  by auto

lemma step_in_possible_steps:
  "step e s r l i = Some (transition, s', outputs, updated) \<Longrightarrow>
   (s', transition) |\<in>| possible_steps e s r l i"
  apply (simp add: step_def Let_def)
  apply (case_tac "possible_steps e s r l i = {||}")
   apply simp
  apply simp
  apply (case_tac "SOME x. x |\<in>| possible_steps e s r l i")
  apply simp
  apply clarify
  by (metis equalsffemptyI verit_sko_ex')

lemma accepts_step: "step e s r l i = Some (transition, s', outputs, updated) \<Longrightarrow>
                     accepts e s' updated t \<Longrightarrow>
                     accepts e s r ((l, i)#t)"
  apply (rule accepts.step)
  apply (rule_tac x="(s', transition)" in FSet.fBexI)
  using step_some_updated apply simp
  by (simp add: step_in_possible_steps)

abbreviation accepts_trace :: "transition_matrix \<Rightarrow> trace \<Rightarrow> bool" where
  "accepts_trace e t \<equiv> accepts e 0 <> t"

lemma no_step_none: "step e s r aa ba = None \<Longrightarrow> \<not>accepts e s r ((aa, ba) # p)"
  apply safe
  apply (rule accepts.cases)
    apply simp
   apply simp
  apply clarify
  apply (simp add: step_def Let_def)
  apply (case_tac "possible_steps e s r aa ba")
   apply simp
  apply (case_tac "SOME xa. xa = x \<or> xa |\<in>| S'")
  by simp

lemma step_none_inaccepts: "((step e s d (fst h) (snd h)) = None) \<Longrightarrow> \<not> (accepts e s d (h#t))"
  using no_step_none surjective_pairing by fastforce

lemma accepts_head: "accepts e s d (h#t) \<Longrightarrow> accepts e s d [h]"
  apply (rule accepts.cases)
    apply simp
   apply simp
  apply (rule accepts.step)
  apply (simp add: accepts.base)
  by auto

lemma accepts_single_event: "step e s d a b \<noteq> None \<Longrightarrow> accepts e s d [(a, b)]"
  apply (rule accepts.step)
  apply (simp add: step_def Let_def)
  apply (case_tac "possible_steps e s d a b = {||}")
   apply simp
  apply (case_tac "SOME x. x |\<in>| possible_steps e s d a b")
  apply (simp add: accepts.base)
  by auto

lemma inaccepts_single_event: "\<not> accepts e s d [(a, b)] \<Longrightarrow> step e s d a b = None"
  using accepts_single_event by blast

lemma single_event_reject: "\<not> accepts e s d [(a, b)] = (step e s d a b = None)"
  using accepts_single_event no_step_none by blast

lemma trace_reject: "(possible_steps e s d a b = {||} \<or> (\<forall>(s', T) |\<in>| possible_steps e s d a b. \<not>accepts e s' (apply_updates (Updates T) (join_ir b d) d) t)) = (\<not> accepts e s d ((a, b)#t))"
  apply safe
    apply (simp add: no_possible_steps_4 no_step_none)
   apply (rule accepts.cases)
     apply simp
    apply simp
   apply clarify
   apply simp
   apply auto[1]
  using accepts.intros(2) by fastforce

lemma trace_reject_2: "\<not> accepts e s d ((a, b)#t) = (possible_steps e s d a b = {||} \<or> (\<forall>(s', T) |\<in>| possible_steps e s d a b. \<not>accepts e s' (apply_updates (Updates T) (join_ir b d) d) t))"
  using trace_reject 
  by simp

lemma step_none_inaccepts_append: "step e s d (fst a) (snd a) = None \<Longrightarrow> \<not>accepts e s d (a # t) \<and> \<not>accepts e s d (a # t @ t')"
  by (simp add: step_none_inaccepts)

lemma aux1: "\<forall> s d. accepts e s d (t@t') \<longrightarrow> accepts e s d t"
proof (induction t)
  case Nil
  then show ?case by (simp add: base)
next
  case (Cons a t)
  then show ?case
    apply safe
    apply (rule accepts.cases)
      apply simp
     apply simp
    using accepts.step by blast
qed

lemma prefix_closure: "accepts e s d (t@t') \<Longrightarrow> accepts e s d t"
proof (induction "t")
  case Nil
  then show ?case by (simp add: base)
next
  case (Cons x xs)
  then show ?case
    apply simp
    apply (case_tac "step e s d (fst x) (snd x) = None")
     apply (simp add: step_none_inaccepts)
    apply safe
    using aux1 by force
qed

lemma inaccepts_prefix: "\<not>accepts e s d t \<Longrightarrow> \<not>accepts e s d (t@t')"
  apply (rule ccontr)
  by (simp add: prefix_closure)

lemma length_observe_empty_trace: "length (observe_all e aa b []) = 0"
  by simp

lemma step_length_suc: "step e 0 <> (fst a) (snd a) = Some (tr, aa, ab, b) \<Longrightarrow> length (observe_all e 0 <> (a # t)) = Suc (length (observe_all e aa b t))"
  by simp

inductive gets_us_to :: "nat \<Rightarrow> transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> bool" where
  base: "s = target \<Longrightarrow> gets_us_to target _ s _ []" |
  step_some: "\<exists>(s', T) |\<in>| possible_steps e s d (fst h) (snd h). gets_us_to target e s' (apply_updates (Updates T) (join_ir i r) r) t \<Longrightarrow> gets_us_to target e s r (h#t)" |
  step_none: "step e s r (fst h) (snd h) = None \<Longrightarrow> s = target \<Longrightarrow> gets_us_to target e s r (h#t)"

lemma no_further_steps: "s \<noteq> s' \<Longrightarrow> \<not> gets_us_to s e s' r []"
  apply safe
  apply (rule gets_us_to.cases)
  by auto

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
