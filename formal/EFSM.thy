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

type_synonym label = string
type_synonym arity = nat
type_synonym inputs = "value list"
type_synonym outputs = "value option list"
type_synonym updates = "update_function list"
type_synonym event = "(label \<times> inputs)"
type_synonym trace = "event list"
type_synonym observation = "outputs list"

type_synonym transition_matrix = "((nat \<times> nat) \<times> transition) fset"

primrec input2state :: "value list \<Rightarrow> nat \<Rightarrow> datastate" where
  "input2state [] _ = <>" |
  "input2state (h#t) i = (\<lambda>x. if x = I i then Some h else (input2state t (i+1)) x)"

lemma hd_input2state: "length i \<ge> 1 \<Longrightarrow> input2state i 1 (I 1) = Some (hd i)"
  by (metis hd_Cons_tl input2state.simps(2) le_numeral_extra(2) length_0_conv)

definition join_ir :: "value list \<Rightarrow> datastate \<Rightarrow> datastate" where
  "join_ir i r \<equiv> (\<lambda>x. case x of
    R n \<Rightarrow> r (R n) |
    I n \<Rightarrow> (input2state i 1) (I n)
  )"
declare join_ir_def [simp]

definition S :: "transition_matrix \<Rightarrow> nat fset" where
  "S m = (fimage (\<lambda>((s, s'), t). s) m) |\<union>| fimage (\<lambda>((s, s'), t). s') m"

primrec apply_outputs :: "output_function list \<Rightarrow> datastate \<Rightarrow> outputs" where
  "apply_outputs [] _ = []" |
  "apply_outputs (h#t) s = (aval h s)#(apply_outputs t s)"

definition apply_guards :: "guards \<Rightarrow> datastate \<Rightarrow> bool" where
  "apply_guards G s = (\<forall>g. g |\<in>| G \<longrightarrow> (gval g s) = Some True)"

definition apply_update :: "update_function \<Rightarrow> datastate \<Rightarrow> datastate \<Rightarrow> datastate" where
  "apply_update u old new = (\<lambda>x. if x = (fst u) then (aval (snd u) old) else new x)"

definition apply_updates :: "update_functions \<Rightarrow> datastate \<Rightarrow> datastate \<Rightarrow> datastate" where
  "apply_updates U old new = ffold (\<lambda>u n. apply_update u old n) old U"

definition possible_steps :: "transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (nat \<times> transition) fset" where
  "possible_steps e s r l i = fimage (\<lambda>((origin, dest), t). (dest, t)) (ffilter (\<lambda>((origin, dest::nat), t::transition). origin = s \<and> (Label t) = l \<and> (length i) = (Arity t) \<and> apply_guards (Guard t) (join_ir i r)) e)"

definition step :: "transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (transition \<times> nat \<times> outputs \<times> datastate) option" where
"step e s r l i =
(if fis_singleton (possible_steps e s r l i) then (let (s', t) =  (fthe_elem (possible_steps e s r l i)) in Some (t, s', (apply_outputs (Outputs t) (join_ir i r)), (apply_updates (Updates t) (join_ir i r) r))) else None)"

lemma step_empty[simp]:"step {||} s r l i = None"
proof-
  have ffilter_empty: "ffilter
       (\<lambda>((origin, dest), t).
           origin = s \<and>
           Label t = l \<and> length i = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))))
       {||} = {||}"
    by auto
  show ?thesis
    by (simp add: step_def possible_steps_def ffilter_empty)
qed

primrec observe_all :: "transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> (transition \<times> nat \<times> outputs \<times> datastate) list" where
  "observe_all _ _ _ [] = []" |
  "observe_all e s r (h#t) =
    (case (step e s r (fst h) (snd h)) of
      (Some (transition, s', outputs, updated)) \<Rightarrow> (((transition, s', outputs, updated)#(observe_all e s' updated t))) |
      _ \<Rightarrow> []
    )"

definition state :: "(transition \<times> nat \<times> outputs \<times> datastate) \<Rightarrow> nat" where
  "state x \<equiv> fst (snd x)"

definition observe_trace :: "transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> observation" where
  "observe_trace e s r t \<equiv> map (\<lambda>(t,x,y,z). y) (observe_all e s r t)"

lemma observe_empty: "t = [] \<Longrightarrow> observe_trace e 0 <> t = []"
  by (simp add: observe_trace_def)

definition state_trace :: "transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> nat list" where
  "state_trace e s r t \<equiv> map (\<lambda>(t,x,y,z). x) (observe_all e s r t)"

definition transition_trace :: "transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> transition list" where
  "transition_trace e s r t \<equiv> map (\<lambda>(t,x,y,z). t) (observe_all e s r t)"

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

inductive accepts :: "transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> bool" where
  base: "accepts e s d []" |
  step: "step e s d (fst h) (snd h) = Some (tr, s', p', d') \<Longrightarrow> accepts e s' d' t \<Longrightarrow> accepts e s d (h#t)"

definition accepts_trace :: "transition_matrix \<Rightarrow> trace \<Rightarrow> bool" where
  "accepts_trace e t = accepts e 0 <> t"

lemma no_step_none: "step e s r aa ba = None \<Longrightarrow> \<not>accepts e s r ((aa, ba) # p)"
  apply safe
  apply (rule accepts.cases)
    apply simp
   apply simp
  by auto

lemma accepts_steps: "fthe_elem (possible_steps e s d (fst h) (snd h)) = (a, b) \<Longrightarrow>
       fis_singleton (possible_steps e s d (fst h) (snd h)) \<Longrightarrow>
       accepts e a (apply_updates (Updates b) (case_vname (\<lambda>n. input2state (snd h) (Suc 0) (I n)) (\<lambda>n. d (R n))) d) t \<Longrightarrow>
       accepts e s d (h#t)"
  by (simp add: observations accepts.step)

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

lemma not_single_step_none:  "\<not> fis_singleton (possible_steps e 0 Map.empty (fst a) (snd a)) \<Longrightarrow> (step e 0 <> (fst a) (snd a) = None)"
  by (simp add: observations)

lemma accepts_singleton_first_step: "accepts e 0 Map.empty (a # t) \<Longrightarrow> fis_singleton (possible_steps e 0 Map.empty (fst a) (snd a))"
  by (meson step_none_inaccepts observations)

lemma step_length_suc: "step e 0 <> (fst a) (snd a) = Some (tr, aa, ab, b) \<Longrightarrow> length (observe_all e 0 <> (a # t)) = Suc (length (observe_all e aa b t))"
  by simp

lemma aux2: "\<forall>s d. accepts e s d t \<longrightarrow> (length t = length (observe_all e s d t))"
  proof (induction t)
    case Nil
    then show ?case by simp
  next
    case (Cons a t)
    then show ?case
      apply safe
      apply (simp add: step_def)
      apply (case_tac "fthe_elem (possible_steps e s d (fst a) (snd a))")
      apply simp
      apply safe
      using step_some observations
       apply (simp add: step_some)
      using step_none_inaccepts observations
      by metis
  qed

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

lemma obs_equal_length_accepts: "(length t = length (observe_all e 0 <> t)) \<Longrightarrow> accepts e 0 <> t"
  proof (induction t)
    case Nil
    then show ?case by (simp add: accepts.base)
  next
    case (Cons a t)
    then show ?case
      apply (case_tac "step e 0 <> (fst a) (snd a) = None")
       apply simp
      apply (simp add: step_def)
      apply (case_tac "fis_singleton (possible_steps e 0 Map.empty (fst a) (snd a))")
      apply (case_tac "fthe_elem (possible_steps e 0 Map.empty (fst a) (snd a))")
       apply simp
      using observations aux3 apply fastforce
      by simp
  qed

lemma length_equal_accepts: "(length t = length (observe_all e 0 <> t)) = accepts e 0 <> t"
  apply safe
  using obs_equal_length_accepts apply auto[1]
  by (simp add: accepts_trace_obs_equal_length)

type_synonym simulation_relation = "nat \<Rightarrow> nat"

inductive simulates_trace :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> bool" where
  base: "simulates_trace e1 e2 s1 s2 d1 d2 []" |
  step: "step e1 s1 d1 (fst h) (snd h) = Some (tr1, s1', p', d1') \<Longrightarrow>
         step e2 s2 d2 (fst h) (snd h) = Some (tr2, s2', p', d2') \<Longrightarrow>
         simulates_trace e1 e2 s1' s2' d1' d2' t \<Longrightarrow> simulates_trace e1 e2 s1 s2 d1 d2 (h#t)"

definition simulates :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> bool" where
  "simulates m1 m2 = (\<forall>t. simulates_trace m1 m2 0 0 <> <> t)"

inductive gets_us_to :: "nat \<Rightarrow> transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> bool" where
  base: "s = target \<Longrightarrow> gets_us_to target _ s _ []" |
  step_some: "step e s r (fst h) (snd h) =  Some (_, s', _, r') \<Longrightarrow> gets_us_to target e s' r' t \<Longrightarrow> gets_us_to target e s r (h#t)" |
  step_none: "step e s r (fst h) (snd h) = None \<Longrightarrow> s=target \<Longrightarrow> gets_us_to target e s r (h#t)"

lemma no_further_steps: "s \<noteq> s' \<Longrightarrow> \<not> gets_us_to s e s' r []"
  apply safe
  apply (rule gets_us_to.cases)
  by auto
end
