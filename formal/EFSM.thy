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
type_synonym registers = "nat \<Rightarrow> value option"

type_synonym event = "(label \<times> inputs)"
type_synonym trace = "event list"
type_synonym observation = "outputs list"
type_synonym transition_matrix = "((nat \<times> nat) \<times> transition) fset"

definition Str :: "string \<Rightarrow> value" where
  "Str s \<equiv> value.Str (String.implode s)"

definition input2state :: "value list \<Rightarrow> registers" where
  "input2state n = map_of (enumerate 1 n)"

lemma input2state_0: "input2state i 0 = None"
  apply (simp add: input2state_def)
  by (metis in_set_enumerate_eq le_numeral_extra(2) map_of_SomeD not_Some_eq prod.sel(1))

lemma input2state_out_of_bounds: "i > length ia \<Longrightarrow> input2state ia i = None"
  apply (simp add: input2state_def)
  by (metis (no_types, lifting) One_nat_def Suc_leI add.right_neutral add_Suc_right imageE in_set_enumerate_eq map_of_eq_None_iff not_less)

lemma input2state_nth: "i < length ia \<Longrightarrow> input2state ia (i+1) = Some (ia ! i)"
proof(induct ia)
  case Nil
  then show ?case
    by simp
next
  case (Cons a ia)
  then show ?case
    apply (simp add: input2state_def)
    apply clarify
    by (simp add: add.commute in_set_enumerate_eq plus_1_eq_Suc)
qed

lemma input2state_nth_pred: "0 < i \<Longrightarrow> i \<le> length ia \<Longrightarrow> input2state ia i = Some (ia ! (i-1))"
proof(induct ia)
  case Nil
  then show ?case
    by simp
next
  case (Cons a ia)
  then show ?case
    apply (simp add: input2state_def)
    by (simp add: add.commute in_set_enumerate_eq plus_1_eq_Suc)
qed

definition join_ir :: "value list \<Rightarrow> registers \<Rightarrow> datastate" where
  "join_ir i r \<equiv> (\<lambda>x. case x of
    R n \<Rightarrow> r n |
    I n \<Rightarrow> (input2state i) n
  )"

definition S :: "transition_matrix \<Rightarrow> nat fset" where
  "S m = (fimage (\<lambda>((s, s'), t). s) m) |\<union>| fimage (\<lambda>((s, s'), t). s') m"

definition apply_outputs :: "aexp list \<Rightarrow> datastate \<Rightarrow> value option list" where
  "apply_outputs p s = map (\<lambda>p. aval p s) p"

lemma apply_outputs_preserves_length: "length (apply_outputs p s) = length p"
  by (simp add: apply_outputs_def)

definition apply_guards :: "gexp list \<Rightarrow> datastate \<Rightarrow> bool" where
  "apply_guards G s = (\<forall>g \<in> set (map (\<lambda>g. gval g s) G). g = true)"

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

definition possible_steps :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (nat \<times> transition) fset" where
  "possible_steps e s r l i = fimage (\<lambda>((origin, dest), t). (dest, t)) (ffilter (\<lambda>((origin, dest::nat), t::transition). origin = s \<and> (Label t) = l \<and> (length i) = (Arity t) \<and> apply_guards (Guard t) (join_ir i r)) e)"

lemma singleton_dest: "fis_singleton (possible_steps e s r aa b) \<Longrightarrow>
       fthe_elem (possible_steps e s r aa b) = (baa, aba) \<Longrightarrow>
       ((s, baa), aba) |\<in>| e"
  apply (simp add: fis_singleton_def fthe_elem_def singleton_equiv)
  apply (simp add: possible_steps_def fmember_def)
  by auto

definition step :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (transition \<times> nat \<times> outputs \<times> registers) option" where
"step e s r l i = (let possibilities = possible_steps e s r l i in
                   if possibilities = {||} then None
                   else
                     let (s', t) = Eps (\<lambda>x. x |\<in>| possibilities) in
                     Some (t, s', (apply_outputs (Outputs t) (join_ir i r)), (apply_updates (Updates t) (join_ir i r) r))
                  )"

lemma no_possible_steps: "possible_steps e s r l i = {||} \<Longrightarrow> step e s r l i = None"
  by (simp add: step_def)

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

lemma observe_trace_step: "lst \<noteq> [] \<Longrightarrow>
       step e s r (fst (hd lst)) (snd (hd lst)) = Some (t, s', p, r') \<Longrightarrow>
       observe_trace e s' r' (tl lst) = obs \<Longrightarrow>
       observe_trace e s r lst = p#obs"
proof(induct lst)
  case Nil
  then show ?case by simp
next
  case (Cons a lst)
  then show ?case
    by (simp add: observe_trace_def)
qed

lemma observe_empty: "t = [] \<Longrightarrow> observe_trace e 0 <> t = []"
  by (simp add: observe_trace_def)

definition efsm_equiv :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> trace \<Rightarrow> bool" where
  "efsm_equiv e1 e2 t \<equiv> ((observe_trace e1 0 <> t) = (observe_trace e2 0 <> t))"

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
  step: "step e s d (fst h) (snd h) = Some (tr, s', p', d') \<Longrightarrow> accepts e s' d' t \<Longrightarrow> accepts e s d (h#t)"

abbreviation accepts_trace :: "transition_matrix \<Rightarrow> trace \<Rightarrow> bool" where
  "accepts_trace e t \<equiv> accepts e 0 <> t"

lemma no_step_none: "step e s r aa ba = None \<Longrightarrow> \<not>accepts e s r ((aa, ba) # p)"
  apply safe
  apply (rule accepts.cases)
    apply simp
   apply simp
  by auto

lemma inaccepts_conditions: "\<not>accepts e s d (h # t) \<Longrightarrow> step e s d (fst h) (snd h) = None \<or> (\<exists>tr s' p' d'. step e s d (fst h) (snd h) =  Some (tr, s', p', d') \<and> \<not>accepts e s' d' t)"
  apply (rule accepts.cases)
  using accepts.base
    apply auto[1]
   apply (metis option.exhaust prod_cases4 accepts.step)
  by simp

lemma step_none_inaccepts: "((step e s d (fst h) (snd h)) = None) \<Longrightarrow> \<not> (accepts e s d (h#t))"
  apply(clarify)
  apply(cases rule:accepts.cases)
    apply(simp)
   apply simp
  by(auto)

lemma inaccepts_future_inaccepts: "(\<exists>tr s' p' d'. step e s d (fst h) (snd h) =  Some (tr, s', p', d') \<and> \<not>accepts e s' d' t) \<Longrightarrow> \<not>accepts e s d (h#t)"
  apply clarify
    apply(cases rule: accepts.cases)
    apply simp
   apply simp
  by auto

lemma conditions_inaccepts: "step e s d (fst h) (snd h) = None \<or> (\<exists>tr s' p' d'. step e s d (fst h) (snd h) =  Some (tr, s', p', d') \<and> \<not>accepts e s' d' t) \<Longrightarrow> \<not> accepts e s d (h # t)"
  apply clarify
    apply(cases rule:accepts.cases)
    apply simp
   apply simp
  by auto

lemma accepts_head: "accepts e s d (h#t) \<Longrightarrow> accepts e s d [h]"
  by (meson base conditions_inaccepts inaccepts_conditions)

lemma inaccepts_single_event: "\<not> accepts e s d [(a, b)] \<Longrightarrow> step e s d (fst (a, b)) (snd (a, b)) = None"
  by (metis (mono_tags, lifting) base inaccepts_conditions)

lemma step_inaccepts: "\<not> accepts e s d ((a, b) # t) \<Longrightarrow> step e s d (fst (a, b)) (snd (a, b)) = Some (tr, s', p', d') \<Longrightarrow> \<not> accepts e s' d' t"
  using inaccepts_conditions by force

lemma step_none_inaccepts_append: "step e s d (fst a) (snd a) = None \<Longrightarrow> \<not>accepts e s d (a # t) \<and> \<not>accepts e s d (a # t @ t')"
  by (simp add: step_none_inaccepts)

lemma step_some: "step e s d (fst a) (snd a) = Some (tr, aa, ab, b) \<Longrightarrow> accepts e s d (a # t) = accepts e aa b t"
  apply safe
  using conditions_inaccepts apply fastforce
  by (simp add: accepts.step)

lemma aux1: "\<forall> s d. accepts e s d (t@t') \<longrightarrow> accepts e s d t"
  proof (induction t)
    case Nil
    then show ?case by (simp add: base)
  next
    case (Cons a t)
    then show ?case
      apply safe
      apply simp
      apply (case_tac "step e s d (fst a) (snd a) = None")
       apply (simp add: step_none_inaccepts)
      apply safe
      by (simp add: step_some)
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
      apply (simp add: step_some)
      using aux1 by force
  qed

lemma inaccepts_prefix: "\<not>accepts e s d t \<Longrightarrow> \<not>accepts e s d (t@t')"
  apply (rule ccontr)
  by (simp add: prefix_closure)

lemma length_observe_empty_trace: "length (observe_all e aa b []) = 0"
  by simp

lemma step_length_suc: "step e 0 <> (fst a) (snd a) = Some (tr, aa, ab, b) \<Longrightarrow> length (observe_all e 0 <> (a # t)) = Suc (length (observe_all e aa b t))"
  by simp

lemma accepts_trace_obs_equal_length: "accepts e 0 <> t \<Longrightarrow> (length t = length (observe_all e 0 <> t))"
  proof (induction t rule: accepts.induct)
    case (base e s d)
    then show ?case
      by simp
  next
    case (step e s d h tr s' p' d' t)
    then show ?case
      by simp
  qed

lemma aux3: "\<forall>s d. (length t = length (observe_all e s d t)) \<longrightarrow> accepts e s d t"
  proof (induction t)
    case Nil
    then show ?case by (simp add: accepts.base)
  next
    case (Cons a t)
    then show ?case
      apply safe
      apply simp
      apply (case_tac "step e s d (fst a) (snd a)")
       apply simp
      apply simp
      apply (case_tac aa)
      apply simp
      by (simp only: step_length_suc step_some)
  qed

inductive gets_us_to :: "nat \<Rightarrow> transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> bool" where
  base: "s = target \<Longrightarrow> gets_us_to target _ s _ []" |
  step_some: "step e s r (fst h) (snd h) =  Some (_, s', _, r') \<Longrightarrow> gets_us_to target e s' r' t \<Longrightarrow> gets_us_to target e s r (h#t)" |
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

end
