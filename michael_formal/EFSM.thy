subsection {* Extended Finite State Machines *}
text{*
This theory defines extended finite state machines. Each EFSM takes a type variable which represents
$S$. This is a slight devaition from the definition presented in \cite{foster2018} as this
type variable may be of an infinite type such as integers, however the intended use is for custom
finite types. See the examples for details.
*}

theory EFSM
  imports "~~/src/HOL/Library/FSet" AExp GExp
begin

type_synonym label = string
type_synonym arity = nat
type_synonym inputs = "value list"
type_synonym outputs = "value list"
type_synonym guard = "gexp"
type_synonym output_function = "aexp"
type_synonym update_function = "(vname \<times> aexp)"
type_synonym event = "(label \<times> inputs)"
type_synonym trace = "event list"
type_synonym observation = "outputs list"

record transition =
  Label :: label
  Arity :: arity
  Guard :: "guard list"
  Outputs :: "output_function list"
  Updates :: "update_function list"

record 'statename::finite efsm =
  s0 :: 'statename
  T :: "('statename \<times> 'statename) \<Rightarrow> transition set"

primrec input2state :: "value list \<Rightarrow> nat \<Rightarrow> datastate" where
  "input2state [] _ = <>" |
  "input2state (h#t) i = (\<lambda>x. if x = I i then Some h else (input2state t (i+1)) x)"

lemma hd_input2state: "length i \<ge> 1 \<Longrightarrow> input2state i 1 (I 1) = Some (hd i)"
  by (metis hd_Cons_tl input2state.simps(2) le_numeral_extra(2) length_0_conv)

abbreviation join_ir :: "value list \<Rightarrow> datastate \<Rightarrow> datastate" where
  "join_ir i r \<equiv> (\<lambda>x. case x of
    R n \<Rightarrow> r (R n) |
    I n \<Rightarrow> (input2state i 1) (I n)
  )"

definition S :: "'statename::finite efsm \<Rightarrow> 'statename set" where
  "S m = {a. (\<exists>x. (T m) (a, x) \<noteq> {} \<or> (T m) (x, a) \<noteq> {})}"

lemma finite_S: "finite (S m)"
  by (simp add: S_def)

primrec apply_outputs :: "output_function list \<Rightarrow> datastate \<Rightarrow> outputs" where
  "apply_outputs [] _ = []" |
  "apply_outputs (h#t) s = (case aval h s of None \<Rightarrow> [] | Some p \<Rightarrow> p#(apply_outputs t s))"

primrec apply_guards :: "guard list \<Rightarrow> datastate \<Rightarrow> bool" where
  "apply_guards [] _ = True" |
  "apply_guards (h#t) s =  ((gval h s) = Some True \<and> (apply_guards t s))"

primrec apply_updates :: "(vname \<times> aexp) list \<Rightarrow> datastate \<Rightarrow> datastate \<Rightarrow> datastate" where
  "apply_updates [] _ new = new" |
  "apply_updates (h#t) old new = (\<lambda>x. if x = (fst h) then (aval (snd h) old) else (apply_updates t old new) x)"

abbreviation is_possible_step :: "'statename::finite efsm \<Rightarrow> 'statename \<Rightarrow> 'statename \<Rightarrow> transition \<Rightarrow> datastate \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> bool" where
"is_possible_step e s s' t r l i \<equiv> (((Label t) = l) \<and> (t \<in> T e (s,s')) \<and> ((length i) = (Arity t)) \<and> (apply_guards (Guard t) (join_ir i r)))"

definition possible_steps :: "'statename::finite efsm \<Rightarrow> 'statename \<Rightarrow> datastate \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> ('statename \<times> transition) set" where
"possible_steps e s r l i \<equiv> {(s',t). is_possible_step e s s' t r l i}"

abbreviation step :: "'statename::finite efsm \<Rightarrow> 'statename \<Rightarrow> datastate \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> ('statename \<times> outputs \<times> datastate) option" where
"step e s r l i \<equiv>
(if is_singleton (possible_steps e s r l i) then (let (s', t) =  (the_elem (possible_steps e s r l i)) in Some (s', (apply_outputs (Outputs t) (join_ir i r)), (apply_updates (Updates t) (join_ir i r) r))) else None)"

primrec observe_all :: "'statename::finite efsm \<Rightarrow> 'statename \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> ('statename \<times> outputs \<times> datastate) list" where
  "observe_all _ _ _ [] = []" |
  "observe_all e s r (h#t) =
    (case (step e s r (fst h) (snd h)) of
      (Some (s', outputs, updated)) \<Rightarrow> (((s', outputs, updated)#(observe_all e s' updated t))) |
      _ \<Rightarrow> []
    )"

abbreviation observe_trace :: "'statename::finite efsm \<Rightarrow> 'statename \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> observation" where
  "observe_trace e s r t \<equiv> map (\<lambda>(x,y,z). y) (observe_all e s r t)"

definition efsm_equiv :: "'statename::finite efsm \<Rightarrow> 'statename'::finite efsm \<Rightarrow> trace \<Rightarrow> bool" where
  "efsm_equiv e1 e2 t \<equiv> ((observe_trace e1 (s0 e1) <> t) = (observe_trace e2 (s0 e2) <> t))"

lemma efsm_equiv_reflexive: "efsm_equiv e1 e1 t"
  by (simp add: efsm_equiv_def)

lemma efsm_equiv_symmetric: "efsm_equiv e1 e2 t \<equiv> efsm_equiv e2 e1 t"
  apply (simp add: efsm_equiv_def)
  by argo

lemma efsm_equiv_transitive: "efsm_equiv e1 e2 t \<and> efsm_equiv e2 e3 t \<longrightarrow> efsm_equiv e1 e3 t"
  by (simp add: efsm_equiv_def)

lemma different_observation_techniques:
  shows "length(observe_all e s r t) = length(observe_trace e s r t)"
  by simp

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

inductive valid :: "'statename::finite efsm \<Rightarrow> 'statename \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> bool" where
  base: "valid e s d []" |
  step: "step e s d (fst h) (snd h) = Some (s', p', d') \<Longrightarrow> valid e s' d' t \<Longrightarrow> valid e s d (h#t)"

abbreviation valid_trace :: "'statename::finite efsm \<Rightarrow> trace \<Rightarrow> bool" where
  "valid_trace e t \<equiv> valid e (s0 e) <> t"

lemma valid_steps: "the_elem (possible_steps e s d (fst h) (snd h)) = (a, b) \<Longrightarrow>
       is_singleton (possible_steps e s d (fst h) (snd h)) \<Longrightarrow>
       valid e a (apply_updates (Updates b) (case_vname (\<lambda>n. input2state (snd h) (Suc 0) (I n)) (\<lambda>n. d (R n))) d) t \<Longrightarrow>
       valid e s d (h#t)"
  by (simp add: valid.step)

lemma invalid_conditions: "\<not>valid e s d (h # t) \<Longrightarrow> step e s d (fst h) (snd h) = None \<or> (\<exists>s' p' d'. step e s d (fst h) (snd h) =  Some (s', p', d') \<and> \<not>valid e s' d' t)"
  apply simp
  apply (case_tac "the_elem (possible_steps e s d (fst h) (snd h))")
  apply simp
  apply safe
  by (simp add: valid_steps)

lemma step_none_invalid: "((step e s d (fst h) (snd h)) = None) \<Longrightarrow> \<not> (valid e s d (h#t))"
  apply(clarify)
  apply(cases rule:valid.cases)
    apply(simp)
   apply simp
  by(auto)

lemma invalid_future_invalid: "(\<exists>s' p' d'. step e s d (fst h) (snd h) =  Some (s', p', d') \<and> \<not>valid e s' d' t) \<Longrightarrow> \<not>valid e s d (h#t)"
  apply clarify
    apply(cases rule:valid.cases)
    apply simp
   apply simp
  by auto

lemma conditions_invalid: "step e s d (fst h) (snd h) = None \<or> (\<exists>s' p' d'. step e s d (fst h) (snd h) =  Some (s', p', d') \<and> \<not>valid e s' d' t) \<Longrightarrow> \<not> valid e s d (h # t)"
  apply clarify
    apply(cases rule:valid.cases)
    apply simp
   apply simp
  by auto

lemma valid_head: "valid e s d (h#t) \<Longrightarrow> valid e s d [h]"
  by (meson base conditions_invalid invalid_conditions)

lemma invalid_single_event: "\<not> valid e s d [(a, b)] \<Longrightarrow> step e s d (fst (a, b)) (snd (a, b)) = None"
  by (metis (mono_tags, lifting) base case_prod_beta' invalid_conditions option.simps(3))

lemma step_invalid: "\<not> valid e s d ((a, b) # t) \<Longrightarrow> step e s d (fst (a, b)) (snd (a, b)) = Some (s', p', d') \<Longrightarrow> \<not> valid e s' d' t"
  using invalid_conditions by force

lemma step_none_invalid_append: "step e s d (fst a) (snd a) = None \<Longrightarrow> \<not>valid e s d (a # t) \<and> \<not>valid e s d (a # t @ t')"
  by (simp add: step_none_invalid)

lemma step_some: "step e s d (fst a) (snd a) = Some (aa, ab, b) \<Longrightarrow> valid e s d (a # t) = valid e aa b t"
  apply safe
  using conditions_invalid apply fastforce
  by (simp add: valid.step)

lemma aux1: "\<forall> s d. valid e s d (t@t') \<longrightarrow> valid e s d t"
  proof (induction t)
    case Nil
    then show ?case by (simp add: base)
  next
    case (Cons a t)
    then show ?case
      apply safe
      apply simp
      apply (case_tac "step e s d (fst a) (snd a) = None")
       apply (simp add: step_none_invalid)
      apply safe
      by (simp add: step_some)
  qed

lemma prefix_closure: "valid e s d (t@t') \<Longrightarrow> valid e s d t"
  proof (induction "t")
    case Nil
    then show ?case by (simp add: base)
  next
    case (Cons x xs)
    then show ?case
      apply simp
      apply (case_tac "step e s d (fst x) (snd x) = None")
       apply (simp add: step_none_invalid)
      apply safe
      apply (simp add: step_some)
      using aux1 by force
  qed

lemma invalid_prefix: "\<not>valid e s d t \<Longrightarrow> \<not>valid e s d (t@t')"
  apply (rule ccontr)
  by (simp add: prefix_closure)

lemma length_observe_empty_trace: "length (observe_all e aa b []) = 0"
  by simp

lemma not_single_step_none:  "\<not> is_singleton (possible_steps e (s0 e) Map.empty (fst a) (snd a)) \<Longrightarrow> (step e (s0 e) <> (fst a) (snd a) = None)"
  by simp

lemma valid_singleton_first_step: "valid e (s0 e) Map.empty (a # t) \<Longrightarrow> is_singleton (possible_steps e (s0 e) Map.empty (fst a) (snd a))"
  by (meson step_none_invalid)

lemma step_length_suc: "step e (s0 e) <> (fst a) (snd a) = Some (aa, ab, b) \<Longrightarrow> length (observe_all e (s0 e) <> (a # t)) = Suc (length (observe_all e aa b t))"
  apply simp
  apply (case_tac "is_singleton (possible_steps e (s0 e) Map.empty (fst a) (snd a))")
   apply simp
  by simp

lemma aux2: "\<forall>s d. valid e s d t \<longrightarrow> (length t = length (observe_all e s d t))"
  proof (induction t)
    case Nil
    then show ?case by simp
  next
    case (Cons a t)
    then show ?case
      apply safe
      apply simp
      apply (case_tac "the_elem (possible_steps e s d (fst a) (snd a))")
      apply simp
      apply safe
       apply (simp add: step_some)
      by (meson step_none_invalid)
  qed

lemma valid_trace_obs_equal_length: "valid e (s0 e) <> t \<Longrightarrow> (length t = length (observe_all e (s0 e) <> t))"
  proof (induction t)
    case Nil
    then show ?case by simp
  next
    case (Cons a t)
    then show ?case
      apply (case_tac "step e (s0 e) <> (fst a) (snd a) = None")
       apply simp
       apply (case_tac "is_singleton (possible_steps e (s0 e) Map.empty (fst a) (snd a))")
        apply (case_tac "the_elem (possible_steps e (s0 e) Map.empty (fst a) (snd a))")
        apply simp
       apply (simp add: valid_singleton_first_step)
      apply safe
      apply (simp only: step_length_suc step_some)
      by (simp add: aux2)
  qed

lemma aux3: "\<forall>s d. (length t = length (observe_all e s d t)) \<longrightarrow> valid e s d t"
  proof (induction t)
    case Nil
    then show ?case by (simp add: valid.base)
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

lemma obs_equal_length_valid: "(length t = length (observe_all e (s0 e) <> t)) \<Longrightarrow> valid e (s0 e) <> t"
  proof (induction t)
    case Nil
    then show ?case by (simp add: valid.base)
  next
    case (Cons a t)
    then show ?case
      apply (case_tac "step e (s0 e) <> (fst a) (snd a) = None")
       apply simp
       apply (case_tac "is_singleton (possible_steps e (s0 e) Map.empty (fst a) (snd a))")
        apply simp
       apply simp
      apply safe
      apply (simp only: step_length_suc step_some)
      by (simp add: aux3)
  qed

lemma length_equal_valid: "(length t = length (observe_all e (s0 e) <> t)) = valid e (s0 e) <> t"
  apply safe
  using obs_equal_length_valid apply auto[1]
  by (simp add: valid_trace_obs_equal_length)

end
