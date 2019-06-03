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

type_synonym event = "(label \<times> inputs)"
type_synonym trace = "event list"
type_synonym observation = "outputs list"
type_synonym transition_matrix = "((nat \<times> nat) \<times> transition) fset"

definition Str :: "string \<Rightarrow> value" where
  "Str s \<equiv> value.Str (String.implode s)"

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

lemma apply_outputs_alt: "apply_outputs p s = map (\<lambda>p. aval p s) p"
proof(induct p)
  case Nil
  then show ?case by simp
next
  case (Cons a p)
  then show ?case
    by simp
qed

lemma apply_outputs_preserves_length: "length (apply_outputs p s) = length p"
  by (simp add: apply_outputs_alt)

primrec apply_guards :: "guard list \<Rightarrow> datastate \<Rightarrow> bool" where
  "apply_guards [] _ = True" |
  "apply_guards (h#t) s =  ((gval h s) = true \<and> (apply_guards t s))"

lemma apply_guards_alt: "apply_guards G s = (\<forall>g \<in> set (map (\<lambda>g. gval g s) G). g = true)"
proof(induct G)
case Nil
  then show ?case 
    by simp
next
  case (Cons a G)
  then show ?case
    by simp
qed

primrec apply_updates :: "(vname \<times> aexp) list \<Rightarrow> datastate \<Rightarrow> datastate \<Rightarrow> datastate" where
  "apply_updates [] _ new = new" |
  "apply_updates (h#t) old new = (\<lambda>x. if x = (fst h) then (aval (snd h) old) else (apply_updates t old new) x)"

definition possible_steps :: "transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (nat \<times> transition) fset" where
  "possible_steps e s r l i = fimage (\<lambda>((origin, dest), t). (dest, t)) (ffilter (\<lambda>((origin, dest::nat), t::transition). origin = s \<and> (Label t) = l \<and> (length i) = (Arity t) \<and> apply_guards (Guard t) (join_ir i r)) e)"

lemma possible_steps_alt_aux: "(\<lambda>((origin, dest), t). (dest, t)) |`|
    ffilter
     (\<lambda>((origin, dest), t).
         origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guard t) (\<lambda>x. case x of I n \<Rightarrow> input2state i 1 (I n) | R n \<Rightarrow> r (R n)))
     e =
    {|(d, t)|} \<Longrightarrow>
    ffilter
     (\<lambda>((origin, dest), t).
         origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guard t) (\<lambda>x. case x of I n \<Rightarrow> input2state i 1 (I n) | R n \<Rightarrow> r (R n)))
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
    apply (simp add: ffilter_finsert)
    apply (case_tac "aa = s")
     apply simp
     apply (case_tac "Label ba = l")
      apply simp
      apply (case_tac "length i = Arity ba")
       apply simp
       apply (case_tac "apply_guards (Guard ba) (case_vname (\<lambda>n. input2state i (Suc 0) (I n)) (\<lambda>n. r (R n)))")
    by auto
qed

lemma possible_steps_alt: "(possible_steps e s r l i = {|(d, t)|}) = (ffilter
     (\<lambda>((origin, dest), t).
         origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guard t) (\<lambda>x. case x of I n \<Rightarrow> input2state i 1 (I n) | R n \<Rightarrow> r (R n)))
     e =
    {|((s, d), t)|})"
  apply standard
   apply (simp add: possible_steps_def possible_steps_alt_aux)
  by (simp add: possible_steps_def)

lemma possible_steps_singleton: "(ffilter
     (\<lambda>((origin, dest), t).
         origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guard t) (\<lambda>x. case x of I n \<Rightarrow> input2state i 1 (I n) | R n \<Rightarrow> r (R n)))
     e =
    {|((s, d), t)|}) \<Longrightarrow> (possible_steps e s r l i = {|(d, t)|})"
  by (simp add: possible_steps_alt)

lemma singleton_dest: "fis_singleton (possible_steps e s r aa b) \<Longrightarrow>
       fthe_elem (possible_steps e s r aa b) = (baa, aba) \<Longrightarrow>
       ((s, baa), aba) |\<in>| e"
  apply (simp add: fis_singleton_def fthe_elem_def singleton_equiv)
  apply (simp add: possible_steps_def fmember_def)
  by auto

definition step :: "transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (transition \<times> nat \<times> outputs \<times> datastate) option" where
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
  apply (simp add: step_def)
  apply standard
  using One_nat_def apply presburger
  using One_nat_def by presburger

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

inductive gets_us_to :: "nat \<Rightarrow> transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> bool" where
  base: "s = target \<Longrightarrow> gets_us_to target _ s _ []" |
  step_some: "step e s r (fst h) (snd h) =  Some (_, s', _, r') \<Longrightarrow> gets_us_to target e s' r' t \<Longrightarrow> gets_us_to target e s r (h#t)" |
  step_none: "step e s r (fst h) (snd h) = None \<Longrightarrow> s=target \<Longrightarrow> gets_us_to target e s r (h#t)"

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
