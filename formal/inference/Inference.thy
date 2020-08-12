section \<open>Extended Finite State Machine Inference\<close>
text\<open>This theory sets out the key definitions for the inference of EFSMs from system traces.\<close>

theory Inference
  imports
    "EFSM.Contexts"
    "EFSM.Transition_Lexorder"
    "HOL-Library.Product_Lexorder"
begin

declare One_nat_def [simp del]

subsection\<open>Transition Identifiers\<close>

text\<open>We first need to define the 'a iEFSM data type which assigns each 'a transition a unique identity.
This is necessary because 'a transitions may not be unique in an EFSM. Assigning 'a transitions a unique
identifier enables us to look up the origin and destination states of 'a transitions without having to
pass them around in the inference functions.\<close>

type_synonym tid = nat
type_synonym tids = "tid list"
type_synonym 'a iEFSM = "(tids \<times> (cfstate \<times> cfstate) \<times> 'a transition) fset"

definition origin :: "tids \<Rightarrow> 'a iEFSM \<Rightarrow> nat" where
  "origin uid t = fst (fst (snd (fthe_elem (ffilter (\<lambda>x. set uid \<subseteq> set (fst x)) t))))"

definition dest :: "tids \<Rightarrow> 'a iEFSM \<Rightarrow> nat" where
  "dest uid t = snd (fst (snd (fthe_elem (ffilter (\<lambda>x. set uid \<subseteq> set (fst x)) t))))"

definition get_by_id :: "'a iEFSM \<Rightarrow> tid \<Rightarrow> 'a transition" where
  "get_by_id e uid = (snd \<circ> snd) (fthe_elem (ffilter (\<lambda>(tids, _). uid \<in> set tids) e))"

definition get_by_ids :: "'a iEFSM \<Rightarrow> tids \<Rightarrow> 'a transition" where
  "get_by_ids e uid = (snd \<circ> snd) (fthe_elem (ffilter (\<lambda>(tids, _). set uid \<subseteq> set tids) e))"

definition uids :: "'a iEFSM \<Rightarrow> nat fset" where
  "uids e = ffUnion (fimage (fset_of_list \<circ> fst) e)"

definition max_uid :: "'a iEFSM \<Rightarrow> nat option" where
  "max_uid e = (let uids = uids e in if uids = {||} then None else Some (fMax uids))"

definition tm :: "'a iEFSM \<Rightarrow> 'a transition_matrix" where
  "tm e = fimage snd e"

definition all_regs :: "'a iEFSM \<Rightarrow> nat set" where
  "all_regs e = EFSM.all_regs (tm e)"

definition max_reg :: "'a iEFSM \<Rightarrow> nat option" where
  "max_reg e = EFSM.max_reg (tm e)"

definition "max_reg_total e = (case max_reg e of None \<Rightarrow> 0 | Some r \<Rightarrow> r)"

definition max_output :: "'a iEFSM \<Rightarrow> nat" where
  "max_output e = EFSM.max_output (tm e)"

definition max_int :: "('a::aexp_value) iEFSM \<Rightarrow> int" where
  "max_int e = EFSM.max_int (tm e)"

definition S :: "'a iEFSM \<Rightarrow> nat fset" where
  "S m = (fimage (\<lambda>(uid, (s, s'), t). s) m) |\<union>| fimage (\<lambda>(uid, (s, s'), t). s') m"

lemma S_alt: "S t = EFSM.S (tm t)"
  apply (simp add: S_def EFSM.S_def tm_def)
  by force

lemma to_in_S:
  "(\<exists>to from uid. (uid, (from, to), t) |\<in>| xb \<longrightarrow> to |\<in>| S xb)"
  apply (simp add: S_def)
  by blast

lemma from_in_S:
  "(\<exists>to from uid. (uid, (from, to), t) |\<in>| xb \<longrightarrow> from |\<in>| S xb)"
  apply (simp add: S_def)
  by blast

subsection\<open>Building the PTA\<close>
text\<open>The first step in EFSM inference is to construct a PTA from the observed traces in the same way
as for classical FSM inference. Beginning with the empty EFSM, we iteratively attempt to walk each
observed trace in the model. When we reach a point where there is no available 'a transition, one is
added. For classical FSMs, this is simply an atomic label. EFSMs deal with data, so we need to add
guards which test for the observed input values and outputs which produce the observed values.\<close>

primrec make_guard :: "'b list \<Rightarrow> nat \<Rightarrow> (vname, 'b) gexp list" where
"make_guard [] _ = []" |
"make_guard (h#t) n = (gexp.Eq (V (vname.I n)) (L h))#(make_guard t (n+1))"

primrec make_outputs :: "'a list \<Rightarrow> 'a output_function list" where
  "make_outputs [] = []" |
  "make_outputs (h#t) = (L h)#(make_outputs t)"

definition max_uid_total :: "'a iEFSM \<Rightarrow> nat" where
  "max_uid_total e = (case max_uid e of None \<Rightarrow> 0 | Some u \<Rightarrow> u)"

definition add_transition :: "'a iEFSM \<Rightarrow> cfstate \<Rightarrow> label \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a iEFSM" where
  "add_transition e s label inputs outputs = finsert ([max_uid_total e + 1], (s, (maxS (tm e))+1), \<lparr>Label=label, Arity=length inputs, Guards=(make_guard inputs 0), Outputs=(make_outputs outputs), Updates=[]\<rparr>) e"

fun make_branch :: "('a::aexp_value) iEFSM \<Rightarrow> cfstate \<Rightarrow> 'a registers \<Rightarrow> 'a trace \<Rightarrow> 'a iEFSM" where
  "make_branch e _ _ [] = e" |
  "make_branch e s r ((label, inputs, outputs)#t) =
    (case (step (tm e) s r label inputs) of
      Some (transition, s', outputs', updated) \<Rightarrow>
        if outputs' = (map Some outputs) then
          make_branch e s' updated t
        else
          make_branch (add_transition e s label inputs outputs) ((maxS (tm e))+1) r t  |
      None \<Rightarrow>
          make_branch (add_transition e s label inputs outputs) ((maxS (tm e))+1) r t
    )"

primrec make_pta_aux :: "('a::{aexp_value,order}) log \<Rightarrow> 'a iEFSM \<Rightarrow> 'a iEFSM" where
  "make_pta_aux [] e = e" |
  "make_pta_aux (h#t) e = make_pta_aux t (make_branch e 0 <> h)"

definition "make_pta log = make_pta_aux log {||}"

lemma make_pta_aux_fold [code]:
  "make_pta_aux l e = fold (\<lambda>h e. make_branch e 0 <> h) l e"
  by(induct l arbitrary: e, auto)

subsection\<open>Integrating Heuristics\<close>
text\<open>A key contribution of the inference technique presented in \cite{foster2019} is the ability to
introduce \emph{internal variables} to the model to generalise behaviours and allow 'a transitions to
be merged. This is done by providing the inference technique with a set of \emph{heuristics}. The
aim here is not to create a ``one size fits all'' magic oracle, rather to recognise particular
\emph{data usage patterns} which can be abstracted.\<close>

type_synonym 'a update_modifier = "tids \<Rightarrow> tids \<Rightarrow> cfstate \<Rightarrow> 'a iEFSM \<Rightarrow> 'a iEFSM \<Rightarrow> 'a iEFSM \<Rightarrow> ('a transition_matrix \<Rightarrow> bool) \<Rightarrow> 'a iEFSM option"

definition null_modifier :: "'a update_modifier" where
  "null_modifier f _ _ _ _ _ _ = None"

definition replace_transition :: "'a iEFSM \<Rightarrow> tids \<Rightarrow> 'a transition \<Rightarrow> 'a iEFSM" where
  "replace_transition e uid new = (fimage (\<lambda>(uids, (from, to), t). if set uid \<subseteq> set uids then (uids, (from, to), new) else (uids, (from, to), t)) e)"

definition replace_all :: "'a iEFSM \<Rightarrow> tids list \<Rightarrow> 'a transition \<Rightarrow> 'a iEFSM" where
  "replace_all e ids new = fold (\<lambda>id acc. replace_transition acc id new) ids e"

definition replace_transitions :: "'a iEFSM \<Rightarrow> (tids \<times> 'a transition) list \<Rightarrow> 'a iEFSM" where
  "replace_transitions e ts = fold (\<lambda>(uid, new) acc. replace_transition acc uid new) ts e"

primrec try_heuristics_check :: "('a transition_matrix \<Rightarrow> bool) \<Rightarrow> 'a update_modifier list \<Rightarrow> 'a update_modifier" where
  "try_heuristics_check _ [] = null_modifier" |
  "try_heuristics_check check (h#t) = (\<lambda>a b c d e f ch.
    case h a b c d e f ch of
      Some e' \<Rightarrow> Some e' |
      None \<Rightarrow> (try_heuristics_check check t) a b c d e f ch
    )"

subsection\<open>Scoring State Merges\<close>
text\<open>To tackle the state merging challenge, we need some means of determining which states are
compatible for merging. Because states are merged pairwise, we additionally require a way of
ordering the state merges. The potential merges are then sorted highest to lowest according to this
score such that we can merge states in order of their merge score.

We want to sort first by score (highest to lowest) and then by state pairs (lowest to highest) so we
endup merging the states with the highest scores first and then break ties by those state pairs
which are closest to the origin.\<close>

record score =
  Score :: nat
  S1 :: cfstate
  S2 :: cfstate

instantiation score_ext :: (linorder) linorder begin
definition less_score_ext :: "'a::linorder score_ext \<Rightarrow> 'a score_ext \<Rightarrow> bool" where
"less_score_ext t1 t2 = ((Score t2, S1 t1, S2 t1, more t1) < (Score t1, S1 t2, S2 t2, more t2) )"

definition less_eq_score_ext :: "'a::linorder score_ext \<Rightarrow> 'a::linorder score_ext \<Rightarrow> bool" where
 "less_eq_score_ext s1 s2 = (s1 < s2 \<or> s1 = s2)"

instance
  apply standard prefer 5
  unfolding less_score_ext_def less_eq_score_ext_def
  using score.equality apply fastforce
  by auto
end

type_synonym scoreboard = "score fset"
type_synonym 'a strategy = "tids \<Rightarrow> tids \<Rightarrow> 'a iEFSM \<Rightarrow> nat"

definition outgoing_transitions :: "cfstate \<Rightarrow> 'a iEFSM \<Rightarrow> (cfstate \<times> 'a transition \<times> tids) fset" where
  "outgoing_transitions s e = fimage (\<lambda>(uid, (from, to), t'). (to, t', uid)) ((ffilter (\<lambda>(uid, (origin, dest), t). origin = s)) e)"

primrec paths_of_length :: "nat \<Rightarrow> 'a iEFSM \<Rightarrow> cfstate \<Rightarrow> tids list fset" where
  "paths_of_length 0 _ _ = {|[]|}" |
  "paths_of_length (Suc m) e s = (
    let
      outgoing = outgoing_transitions s e;
      paths = ffUnion (fimage (\<lambda>(d, t, id). fimage (\<lambda>p. id#p) (paths_of_length m e d)) outgoing)
    in
      ffilter (\<lambda>l. length l = Suc m) paths
  )"

lemma paths_of_length_1: "paths_of_length 1 e s = fimage (\<lambda>(d, t, id). [id]) (outgoing_transitions s e)"
  apply (simp add: One_nat_def)
  apply (simp add: outgoing_transitions_def comp_def One_nat_def[symmetric])
  apply (rule fBall_ffilter2)
   defer
   apply (simp add: ffilter_def ffUnion_def fBall_def Abs_fset_inverse)
   apply auto[1]
  apply (simp add: ffilter_def ffUnion_def fBall_def Abs_fset_inverse fset_both_sides)
  by force

fun step_score :: "(tids \<times> tids) list \<Rightarrow> 'a iEFSM \<Rightarrow> 'a strategy \<Rightarrow> nat" where
  "step_score [] _ _ = 0" |
  "step_score ((id1, id2)#t) e s = (
    let score = s id1 id2 e in
    if score = 0 then
      0
    else
      score + (step_score t e s)
  )"

lemma step_score_foldr [code]:
  "step_score xs e s = foldr (\<lambda>(id1, id2) acc. let score = s id1 id2 e in
    if score = 0 then
      0
    else
      score + acc) xs 0"
proof(induct xs)
case Nil
  then show ?case
    by simp
next
  case (Cons a xs)
  then show ?case
    apply (cases a, clarify)
    by (simp add: Let_def)
qed

definition score_from_list :: "tids list fset \<Rightarrow> tids list fset \<Rightarrow> 'a iEFSM \<Rightarrow> 'a strategy \<Rightarrow> nat" where
  "score_from_list P1 P2 e s = (
    let
      pairs = fimage (\<lambda>(l1, l2). zip l1 l2) (P1 |\<times>| P2);
      scored_pairs = fimage (\<lambda>l. step_score l e s) pairs
    in
    fSum scored_pairs
  )"

definition k_score :: "nat \<Rightarrow> 'a iEFSM \<Rightarrow> 'a strategy \<Rightarrow> scoreboard" where
  "k_score k e strat = (
    let
      states = S e;
      pairs_to_score = (ffilter (\<lambda>(x, y). x < y) (states |\<times>| states));
      paths = fimage (\<lambda>(s1, s2). (s1, s2, paths_of_length k e s1, paths_of_length k e s2)) pairs_to_score;
      scores = fimage (\<lambda>(s1, s2, p1, p2). \<lparr>Score = score_from_list p1 p2 e strat, S1 = s1, S2 = s2\<rparr>) paths
    in
    ffilter (\<lambda>x. Score x > 0) scores
)"

definition score_state_pair :: "'a strategy \<Rightarrow> 'a iEFSM \<Rightarrow> cfstate \<Rightarrow> cfstate \<Rightarrow> nat" where
  "score_state_pair strat e s1 s2 = (
    let
      T1 = outgoing_transitions s1 e;
      T2 = outgoing_transitions s2 e
    in
      fSum (fimage (\<lambda>((_, _, t1), (_, _, t2)). strat t1 t2 e) (T1 |\<times>| T2))
  )"

definition score_1 :: "'a iEFSM \<Rightarrow> 'a strategy \<Rightarrow> scoreboard" where
  "score_1 e strat = (
    let
      states = S e;
      pairs_to_score = (ffilter (\<lambda>(x, y). x < y) (states |\<times>| states));
      scores = fimage (\<lambda>(s1, s2). \<lparr>Score = score_state_pair strat e s1 s2, S1 = s1, S2 = s2\<rparr>) pairs_to_score
    in
      ffilter (\<lambda>x. Score x > 0) scores
  )"

lemma score_1: "score_1 e s = k_score 1 e s"
proof-
  have fprod_fimage:
  "\<And>a b. ((\<lambda>(_, _, id). [id]) |`| a |\<times>| (\<lambda>(_, _, id). [id]) |`| b) =
       fimage (\<lambda>((_, _, id1), (_, _, id2)). ([id1], [id2])) (a |\<times>| b)"
    apply (simp add: fimage_def fprod_def Abs_fset_inverse fset_both_sides)
    by force
  show ?thesis
    apply (simp add: score_1_def k_score_def Let_def comp_def)
    apply (rule arg_cong[of _ _ "ffilter (\<lambda>x. 0 < Score x)"])
    apply (rule fun_cong[of _ _ "(Inference.S e |\<times>| Inference.S e)"])
    apply (rule ext)
    subgoal for x
      apply (rule fun_cong[of _ _ "ffilter (\<lambda>a. case a of (a, b) \<Rightarrow> a < b) x"])
      apply (rule arg_cong[of _ _ fimage])
      apply (rule ext)
      apply (case_tac x)
      apply simp
      apply (simp add: paths_of_length_1)
      apply (simp add: score_state_pair_def Let_def score_from_list_def comp_def)
      subgoal for x a b
        apply (rule arg_cong[of _ _ fSum])
        apply (simp add: fprod_fimage)
        apply (rule fun_cong[of _ _ "(outgoing_transitions a e |\<times>| outgoing_transitions b e)"])
        apply (rule arg_cong[of _ _ fimage])
        apply (rule ext)
        apply clarify
        by (simp add: Let_def)
    done
  done
qed

fun bool2nat :: "bool \<Rightarrow> nat" where
  "bool2nat True = 1" |
  "bool2nat False = 0"

definition score_transitions :: "'a transition \<Rightarrow> 'a transition \<Rightarrow> nat" where
  "score_transitions t1 t2 = (
    if Label t1 = Label t2 \<and> Arity t1 = Arity t2 \<and> length (Outputs t1) = length (Outputs t2) then
      1 + bool2nat (t1 = t2) + card ((set (Guards t2)) \<inter> (set (Guards t2))) + card ((set (Updates t2)) \<inter> (set (Updates t2))) + card ((set (Outputs t2)) \<inter> (set (Outputs t2)))
    else
      0
  )"

subsection\<open>Direct Subsumption\<close>
text\<open>When merging EFSM 'a transitions, one must \emph{account for} the behaviour of the other. The
\emph{subsumption in context} relation formalises the intuition that, in certain contexts, a
transition $t_2$ reproduces the behaviour of, and updates the data state in a manner consistent
with, another 'a transition $t_1$, meaning that $t_2$ can be used in place of $t_1$ with no observable
difference in behaviour.

The subsumption in context relation requires us to supply a context in which to test subsumption,
but there is a problem when we try to apply this to inference: Which context should we use? The
\emph{direct subsumption} relation works at EFSM level to determine when and whether one 'a transition
is able to account for the behaviour of another such that we can use one in place of another without
adversely effecting observable behaviour.\<close>

definition directly_subsumes :: "('a::{order,aexp_value}) iEFSM \<Rightarrow> 'a iEFSM \<Rightarrow> cfstate \<Rightarrow> cfstate \<Rightarrow> 'a transition \<Rightarrow> 'a transition \<Rightarrow> bool" where
  "directly_subsumes e1 e2 s s' t1 t2 \<equiv> (\<forall>p. recognises (tm e1) p \<and> gets_us_to s (tm e1) 0 <>  p \<longrightarrow>
                                             recognises (tm e2) p \<and> gets_us_to s' (tm e2) 0 <>  p \<longrightarrow>
                                             (\<forall>c. anterior_context (tm e2) p = Some c \<longrightarrow> subsumes t1 c t2)) \<and>
                                         (\<exists>c. subsumes t1 c t2)"

lemma directly_subsumes_reflexive: "directly_subsumes e1 e2 s s' t t"
  apply (simp add: directly_subsumes_def)
  by (simp add: transition_subsumes_self)

lemma subsumes_in_all_contexts_directly_subsumes:
  "(\<And>c. subsumes t2 c t1) \<Longrightarrow> directly_subsumes e1 e2 s s' t2 t1"
  by (simp add: directly_subsumes_def)

lemma gets_us_to_and_not_subsumes:
  "\<exists>p. recognises (tm e1) p \<and>
       gets_us_to s (tm e1) 0 (<>) p \<and>
       recognises (tm e2) p \<and>
       gets_us_to s' (tm e2) 0 (<>) p \<and>
       (anterior_context (tm e2) p) = Some a \<and>
       \<not> subsumes t1 a t2 \<Longrightarrow>
   \<not> directly_subsumes e1 e2 s s' t1 t2"
  unfolding directly_subsumes_def by auto

lemma cant_directly_subsume:
  "(\<And>c. \<not> subsumes t c t') \<Longrightarrow> \<not> directly_subsumes m m' s s' t t'"
  by (simp add: directly_subsumes_def)

definition insert_transition :: "tids \<Rightarrow> cfstate \<Rightarrow> cfstate \<Rightarrow> 'a transition \<Rightarrow> 'a iEFSM \<Rightarrow> 'a iEFSM" where
  "insert_transition uid from to t e = (
    if \<nexists>(uid, (from', to'), t') |\<in>| e. from = from' \<and> to = to' \<and> t = t' then
      finsert (uid, (from, to), t) e
    else
      fimage (\<lambda>(uid', (from', to'), t').
        if from = from' \<and> to = to' \<and> t = t' then
          (List.union uid' uid, (from', to'), t')
        else
          (uid', (from', to'), t')
      ) e
  )"

lemma guard_implication: "Label t1 = Label t2 \<Longrightarrow>
  Arity t1 = Arity t2 \<Longrightarrow>
  Outputs t1 = Outputs t2 \<Longrightarrow>
  Updates t1 = Updates t2 \<Longrightarrow>
  (\<forall>s. apply_guards (Guards t1) s \<longrightarrow> apply_guards (Guards t2) s) \<Longrightarrow>
  subsumes t2 c t1"
  apply (rule subsumption)
  unfolding can_take_transition_def can_take_def
  using can_take_transition_def can_take_def posterior_def posterior_separate_def can_take_def by auto

definition guard_implication_subsumption :: "('a::aexp_value) transition \<Rightarrow> 'a transition \<Rightarrow> bool" where
  "guard_implication_subsumption t1 t2 = (
    Label t1 = Label t2 \<and>
    Arity t1 = Arity t2 \<and>
    Outputs t1 = Outputs t2 \<and>
    Updates t1 = Updates t2 \<and>
    gexp_implies (fold gAnd (Guards t1) (Bc True)) (fold gAnd (Guards t2) (Bc True))
  )"

lemma guard_implication_subsumption:
  "guard_implication_subsumption t1 t2 \<Longrightarrow> directly_subsumes m1 m2 s1 s2 t2 t1"
  apply (rule subsumes_in_all_contexts_directly_subsumes)
  apply (rule subsumption)
  unfolding guard_implication_subsumption_def can_take_transition_def can_take_def
     apply simp
    apply (simp add: fold_apply_guards gexp_implies_def)
   apply simp
  by simp

subsection\<open>Merging States\<close>
definition merge_states_aux :: "nat \<Rightarrow> nat \<Rightarrow> 'a iEFSM \<Rightarrow> 'a iEFSM" where
  "merge_states_aux s1 s2 e = fimage (\<lambda>(uid, (origin, dest), t). (uid, (if origin = s1 then s2 else origin , if dest = s1 then s2 else dest), t)) e"

definition merge_states :: "nat \<Rightarrow> nat \<Rightarrow> 'a iEFSM \<Rightarrow> 'a iEFSM" where
  "merge_states x y t = (if x > y then merge_states_aux x y t else merge_states_aux y x t)"

lemma merge_states_symmetry: "merge_states x y t = merge_states y x t"
  by (simp add: merge_states_def)

lemma merge_state_self: "merge_states s s t = t"
  apply (simp add: merge_states_def merge_states_aux_def)
  by force

lemma merge_states_self_simp [code]:
  "merge_states x y t = (if x = y then t else if x > y then merge_states_aux x y t else merge_states_aux y x t)"
  apply (simp add: merge_states_def merge_states_aux_def)
  by force

subsection\<open>Resolving Nondeterminism\<close>
text\<open>Because EFSM 'a transitions are not simply atomic actions, duplicated behaviours cannot be
resolved into a single 'a transition by simply merging destination states, as it can in classical FSM
inference. It is now possible for attempts to resolve the nondeterminism introduced by merging
states to fail, meaning that two states which initially seemed compatible cannot actually be merged.
This is not the case in classical FSM inference.\<close>

type_synonym 'a nondeterministic_pair = "(cfstate \<times> (cfstate \<times> cfstate) \<times> (('a transition \<times> tids) \<times> ('a transition \<times> tids)))"

definition state_nondeterminism :: "nat \<Rightarrow> (cfstate \<times> 'a transition \<times> tids) fset \<Rightarrow> 'a nondeterministic_pair fset" where
  "state_nondeterminism og nt = (if size nt < 2 then {||} else ffUnion (fimage (\<lambda>x. let (dest, t) = x in fimage (\<lambda>y. let (dest', t') = y in (og, (dest, dest'), (t, t'))) (nt - {|x|})) nt))"

lemma state_nondeterminism_empty [simp]: "state_nondeterminism a {||} = {||}"
  by (simp add: state_nondeterminism_def ffilter_def Set.filter_def)

lemma state_nondeterminism_singledestn [simp]: "state_nondeterminism a {|x|} = {||}"
  by (simp add: state_nondeterminism_def ffilter_def Set.filter_def)

(* For each state, get its outgoing 'a transitions and see if there's any nondeterminism there *)
definition nondeterministic_pairs :: "('a::aexp_value) iEFSM \<Rightarrow> 'a nondeterministic_pair fset" where
  "nondeterministic_pairs t = ffilter (\<lambda>(_, _, (t, _), (t', _)). Label t = Label t' \<and> Arity t = Arity t' \<and> choice t t') (ffUnion (fimage (\<lambda>s. state_nondeterminism s (outgoing_transitions s t)) (S t)))"

definition nondeterministic_pairs_labar_dest :: "('a::aexp_value) iEFSM \<Rightarrow> 'a nondeterministic_pair fset" where
  "nondeterministic_pairs_labar_dest t = ffilter
     (\<lambda>(_, (d, d'), (t, _), (t', _)).
      Label t = Label t' \<and> Arity t = Arity t' \<and> (choice t t' \<or> (Outputs t = Outputs t' \<and> d = d')))
     (ffUnion (fimage (\<lambda>s. state_nondeterminism s (outgoing_transitions s t)) (S t)))"

definition nondeterministic_pairs_labar :: "('a::aexp_value) iEFSM \<Rightarrow> 'a nondeterministic_pair fset" where
  "nondeterministic_pairs_labar t = ffilter
     (\<lambda>(_, (d, d'), (t, _), (t', _)).
      Label t = Label t' \<and> Arity t = Arity t' \<and> (choice t t' \<or> Outputs t = Outputs t'))
     (ffUnion (fimage (\<lambda>s. state_nondeterminism s (outgoing_transitions s t)) (S t)))"

definition deterministic :: "'a iEFSM \<Rightarrow> ('a iEFSM \<Rightarrow> 'a nondeterministic_pair fset) \<Rightarrow> bool" where
  "deterministic t np = (np t = {||})"

definition nondeterministic :: "'a iEFSM \<Rightarrow> ('a iEFSM \<Rightarrow> 'a nondeterministic_pair fset) \<Rightarrow> bool" where
  "nondeterministic t np = (\<not> deterministic t np)"

definition make_distinct :: "('a::linorder) iEFSM \<Rightarrow> 'a iEFSM" where
  "make_distinct e = ffold_ord (\<lambda>(uid, (from, to), t) acc. insert_transition uid from to t acc) e {||}"

\<comment> \<open>When we replace one 'a transition with another, we need to merge their uids to keep track of which\<close>
\<comment> \<open>transition accounts for which action in the original traces                                     \<close>
definition merge_transitions_aux :: "('a::linorder) iEFSM \<Rightarrow> tids \<Rightarrow> tids \<Rightarrow> 'a iEFSM" where
  "merge_transitions_aux e oldID newID = (let
    (uids1, (origin, dest), old) = fthe_elem (ffilter (\<lambda>(uids, _). oldID = uids) e);
    (uids2, (origin, dest), new) = fthe_elem (ffilter (\<lambda>(uids, _). newID = uids) e) in
    make_distinct (finsert (List.union uids1 uids2, (origin, dest), new) (e - {|(uids1, (origin, dest), old), (uids2, (origin, dest), new)|}))
  )"

(* merge_transitions - Try dest merge 'a transitions t\<^sub>1 and t\<^sub>2 dest help resolve nondeterminism in
                       newEFSM. If either subsumes the other directly then the subsumed 'a transition
                       can simply be replaced with the subsuming one, else we try dest apply the
                       modifier function dest resolve nondeterminism that way.                    *)
(* @param oldEFSM   - the EFSM before merging the states which caused the nondeterminism          *)
(* @param preDestMerge   - the EFSM after merging the states which caused the nondeterminism      *)
(* @param newEFSM   - the current EFSM with nondeterminism                                        *)
(* @param t\<^sub>1        - a 'a transition dest be merged with t\<^sub>2                                         *)
(* @param u\<^sub>1        - the unique identifier of t\<^sub>1                                                 *)
(* @param t\<^sub>2        - a 'a transition dest be merged with t\<^sub>1                                         *)
(* @param u\<^sub>2        - the unique identifier of t\<^sub>2                                                 *)
(* @param modifier  - an update modifier function which tries dest generalise 'a transitions         *)
definition merge_transitions :: "(cfstate \<times> cfstate) set \<Rightarrow> ('a::{aexp_value, linorder}) iEFSM \<Rightarrow> 'a iEFSM \<Rightarrow> 'a iEFSM \<Rightarrow> 'a transition \<Rightarrow> tids \<Rightarrow> 'a transition \<Rightarrow> tids \<Rightarrow> 'a update_modifier \<Rightarrow> ('a transition_matrix \<Rightarrow> bool) \<Rightarrow> 'a iEFSM option" where
  "merge_transitions failedMerges oldEFSM preDestMerge destMerge t\<^sub>1 u\<^sub>1 t\<^sub>2 u\<^sub>2 modifier check = (
     if \<forall>id \<in> set u\<^sub>1. directly_subsumes oldEFSM destMerge (origin [id] oldEFSM) (origin u\<^sub>1 destMerge) t\<^sub>2 t\<^sub>1 then
       \<comment> \<open>Replace t1 with t2\<close>
       Some (merge_transitions_aux destMerge u\<^sub>1 u\<^sub>2)
     else if \<forall>id \<in> set u\<^sub>2. directly_subsumes oldEFSM destMerge (origin [id] oldEFSM) (origin u\<^sub>2 destMerge) t\<^sub>1 t\<^sub>2 then
       \<comment> \<open>Replace t2 with t1\<close>
       Some (merge_transitions_aux destMerge u\<^sub>2 u\<^sub>1)
     else
        case modifier u\<^sub>1 u\<^sub>2 (origin u\<^sub>1 destMerge) destMerge preDestMerge oldEFSM check of
          None \<Rightarrow> None |
          Some e \<Rightarrow> Some (make_distinct e)
   )"

definition outgoing_transitions_from :: "'a iEFSM \<Rightarrow> cfstate \<Rightarrow> 'a transition fset" where
  "outgoing_transitions_from e s = fimage (\<lambda>(_, _, t). t) (ffilter (\<lambda>(_, (orig, _), _). orig = s) e)"

definition order_nondeterministic_pairs :: "('a::linorder) nondeterministic_pair fset \<Rightarrow> 'a nondeterministic_pair list" where
  "order_nondeterministic_pairs s = map snd (sorted_list_of_fset (fimage (\<lambda>s. let (_, _, (t1, _), (t2, _)) = s in (score_transitions t1 t2, s)) s))"

(* resolve_nondeterminism - tries dest resolve nondeterminism in a given 'a iEFSM                      *)
(* @param ((from, (dest\<^sub>1, dest\<^sub>2), ((t\<^sub>1, u\<^sub>1), (t\<^sub>2, u\<^sub>2)))#ss) - a list of nondeterministic pairs where
          from - nat - the state from which t\<^sub>1 and t\<^sub>2 eminate
          dest\<^sub>1  - nat - the destination state of t\<^sub>1
          dest\<^sub>2  - nat - the destination state of t\<^sub>2
          t\<^sub>1   - 'a transition - a 'a transition dest be merged with t\<^sub>2
          t\<^sub>2   - 'a transition - a 'a transition dest be merged with t\<^sub>1
          u\<^sub>1   - nat - the unique identifier of t\<^sub>1
          u\<^sub>2   - nat - the unique identifier of t\<^sub>2
          ss   - list - the rest of the list                                                      *)
(* @param oldEFSM - the EFSM before merging the states which caused the nondeterminism            *)
(* @param newEFSM - the current EFSM with nondeterminism                                          *)
(* @param m       - an update modifier function which tries dest generalise 'a transitions             *)
(* @param check - a function which takes an EFSM and returns a bool dest ensure that certain
                  properties hold in the new 'a iEFSM                                                *)
function resolve_nondeterminism :: "(cfstate \<times> cfstate) set \<Rightarrow> ('a::{aexp_value,linorder}) nondeterministic_pair list \<Rightarrow> 'a iEFSM \<Rightarrow> 'a iEFSM \<Rightarrow> 'a update_modifier \<Rightarrow> ('a transition_matrix \<Rightarrow> bool) \<Rightarrow> ('a iEFSM \<Rightarrow> 'a nondeterministic_pair fset) \<Rightarrow> ('a iEFSM option \<times> (cfstate \<times> cfstate) set)" where
  "resolve_nondeterminism failedMerges [] _ newEFSM _ check np = (
      if deterministic newEFSM np \<and> check (tm newEFSM) then Some newEFSM else None, failedMerges
  )" |
  "resolve_nondeterminism failedMerges ((from, (dest\<^sub>1, dest\<^sub>2), ((t\<^sub>1, u\<^sub>1), (t\<^sub>2, u\<^sub>2)))#ss) oldEFSM newEFSM m check np = (
    if (dest\<^sub>1, dest\<^sub>2) \<in> failedMerges \<or> (dest\<^sub>2, dest\<^sub>1) \<in> failedMerges then
      (None, failedMerges)
    else
    let destMerge = merge_states dest\<^sub>1 dest\<^sub>2 newEFSM in
    case merge_transitions failedMerges oldEFSM newEFSM destMerge t\<^sub>1 u\<^sub>1 t\<^sub>2 u\<^sub>2 m check of
      None \<Rightarrow> resolve_nondeterminism (insert (dest\<^sub>1, dest\<^sub>2) failedMerges) ss oldEFSM newEFSM m check np |
      Some new \<Rightarrow> (
        let newScores = order_nondeterministic_pairs (np new) in
        if (size new, size (S new), size (newScores)) < (size newEFSM, size (S newEFSM), size ss) then
          case resolve_nondeterminism failedMerges newScores oldEFSM new m check np of
            (Some new', failedMerges) \<Rightarrow> (Some new', failedMerges) |
            (None, failedMerges) \<Rightarrow> resolve_nondeterminism (insert (dest\<^sub>1, dest\<^sub>2) failedMerges) ss oldEFSM newEFSM m check np
        else
          (None, failedMerges)
      )
  )"
     apply (clarify, metis neq_Nil_conv prod_cases3 surj_pair)
  by auto
termination
  by (relation "measures [\<lambda>(_, _, _, newEFSM, _). size newEFSM,
                          \<lambda>(_, _, _, newEFSM, _). size (S newEFSM),
                          \<lambda>(_, ss, _, _, _). size ss]", auto)

subsection\<open>EFSM Inference\<close>

(* Merge - tries dest merge two states in a given 'a iEFSM and resolve the resulting nondeterminism  *)
(* @param e     - an 'a iEFSM                                                                        *)
(* @param s1    - a state dest be merged with s2                                                  *)
(* @param s2    - a state dest be merged with s1                                                  *)
(* @param m     - an update modifier function which tries dest generalise 'a transitions             *)
(* @param check - a function which takes an EFSM and returns a bool dest ensure that certain
                  properties hold in the new 'a iEFSM                                                *)
definition merge :: "(cfstate \<times> cfstate) set \<Rightarrow> ('a::{linorder,aexp_value}) iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a update_modifier \<Rightarrow> ('a transition_matrix \<Rightarrow> bool) \<Rightarrow> ('a iEFSM \<Rightarrow> 'a nondeterministic_pair fset) \<Rightarrow> ('a iEFSM option \<times> (cfstate \<times> cfstate) set)" where
  "merge failedMerges e s\<^sub>1 s\<^sub>2 m check np = (
    if s\<^sub>1 = s\<^sub>2 \<or> (s\<^sub>1, s\<^sub>2) \<in> failedMerges \<or> (s\<^sub>2, s\<^sub>1) \<in> failedMerges then
      (None, failedMerges)
    else
      let e' = make_distinct (merge_states s\<^sub>1 s\<^sub>2 e) in
      resolve_nondeterminism failedMerges (order_nondeterministic_pairs (np e')) e e' m check np
  )"

(* inference_step - attempt dest carry out a single step of the inference process by merging the  *)
(* @param e - an 'a iEFSM dest be generalised                                                        *)
(* @param ((s, s1, s2)#t) - a list of triples of the form (score, state, state) dest be merged    *)
(* @param m     - an update modifier function which tries dest generalise 'a transitions             *)
(* @param check - a function which takes an EFSM and returns a bool dest ensure that certain
                  properties hold in the new 'a iEFSM                                                *)
function inference_step :: "(cfstate \<times> cfstate) set \<Rightarrow> ('a::{linorder,aexp_value}) iEFSM \<Rightarrow> score fset \<Rightarrow> 'a update_modifier \<Rightarrow> ('a transition_matrix \<Rightarrow> bool) \<Rightarrow> ('a iEFSM \<Rightarrow> 'a nondeterministic_pair fset) \<Rightarrow> ('a iEFSM option \<times> (cfstate \<times> cfstate) set)" where
  "inference_step failedMerges e s m check np = (
     if s = {||} then (None, failedMerges) else
     let
      h = fMin s;
      t = s - {|h|}
    in
    case merge failedMerges e (S1 h) (S2 h) m check np of
      (Some new, failedMerges) \<Rightarrow> (Some new, failedMerges) |
      (None, failedMerges) \<Rightarrow> inference_step (insert ((S1 h), (S2 h)) failedMerges) e t m check np
  )"
  by auto
termination
  apply (relation "measures [\<lambda>(_, _, s, _, _, _). size s]")
   apply simp
  by (simp add: card_minus_fMin)

(* Takes an 'a iEFSM and iterates inference_step until no further states can be successfully merged  *)
(* @param e - an 'a iEFSM dest be generalised                                                        *)
(* @param r - a 'a strategy dest identify and prioritise pairs of states dest merge                  *)
(* @param m     - an update modifier function which tries dest generalise 'a transitions             *)
(* @param check - a function which takes an EFSM and returns a bool dest ensure that certain
                  properties hold in the new 'a iEFSM                                                *)
function infer :: "(cfstate \<times> cfstate) set \<Rightarrow> nat \<Rightarrow> ('a::{linorder,aexp_value}) iEFSM \<Rightarrow> 'a strategy \<Rightarrow> 'a update_modifier \<Rightarrow> ('a transition_matrix \<Rightarrow> bool) \<Rightarrow> ('a iEFSM \<Rightarrow> 'a nondeterministic_pair fset) \<Rightarrow> 'a iEFSM" where
  "infer failedMerges k e r m check np = (
    let scores = if k = 1 then score_1 e r else (k_score k e r) in
    case inference_step failedMerges e (ffilter (\<lambda>s. (S1 s, S2 s) \<notin> failedMerges \<and> (S2 s, S1 s) \<notin> failedMerges) scores) m check np of
      (None, _) \<Rightarrow> e |
      (Some new, failedMerges) \<Rightarrow> if (S new) |\<subset>| (S e) then infer failedMerges k new r m check np else e
  )"
  by auto
termination
  apply (relation "measures [\<lambda>(_, _, e, _). size (S e)]")
   apply simp
  by (metis (no_types, lifting) case_prod_conv measures_less size_fsubset)

fun get_ints :: "('a::aexp_value) trace \<Rightarrow> int list" where
  "get_ints [] = []" |
  "get_ints ((_, inputs, outputs)#t) = (map (\<lambda>x. getNum x) (filter (\<lambda> x. isNum x) (inputs@outputs)))"

definition learn :: "nat \<Rightarrow> ('a::{aexp_value,linorder}) iEFSM \<Rightarrow> 'a log \<Rightarrow> 'a strategy \<Rightarrow> 'a update_modifier \<Rightarrow> ('a iEFSM \<Rightarrow> 'a nondeterministic_pair fset) \<Rightarrow> 'a iEFSM" where
  "learn n pta l r m np = (
     let check = accepts_log (set l) in
         (infer {} n pta r m check np)
   )"

subsection\<open>Evaluating Inferred Models\<close>
text\<open>We need a function to test the EFSMs we infer. The \texttt{test\_trace} function executes a
trace in the model and outputs a more comprehensive trace such that the expected outputs and actual
outputs can be compared. If a point is reached where the model does not recognise an action, the
remainder of the trace forms the second element of the output pair such that we know the exact point
at which the model stopped processing.\<close>

definition i_possible_steps :: "('a::aexp_value) iEFSM \<Rightarrow> cfstate \<Rightarrow> 'a registers \<Rightarrow> label \<Rightarrow> 'a inputs \<Rightarrow> (tids \<times> cfstate \<times> 'a transition) fset" where
  "i_possible_steps e s r l i = fimage (\<lambda>(uid, (origin, dest), t). (uid, dest, t))
  (ffilter (\<lambda>(uid, (origin, dest), t).
      origin = s
      \<and> (Label t) = l
      \<and> (length i) = (Arity t)
      \<and> apply_guards (Guards t) (join_ir i r)
     )
    e)"

fun test_trace :: "('a::aexp_value) trace \<Rightarrow> 'a iEFSM \<Rightarrow> cfstate \<Rightarrow> 'a registers \<Rightarrow> ((label \<times> 'a inputs \<times> cfstate \<times> cfstate \<times> 'a registers \<times> tids \<times> 'a list \<times> 'a outputs) list \<times> 'a trace)" where
  "test_trace [] _ _ _ = ([], [])" |
  "test_trace ((l, i, expected)#es) e s r = (
    let
      ps = i_possible_steps e s r l i
    in
      if fis_singleton ps then
        let
          (id, s', t) = fthe_elem ps;
          r' = evaluate_updates t i r;
          actual = evaluate_outputs t i r;
          (est, fail) = (test_trace es e s' r')
        in
        ((l, i, s, s', r, id, expected, actual)#est, fail)
      else
        ([], (l, i, expected)#es)
  )"

text\<open>The \texttt{test\_'a log} function executes the \texttt{test\_trace} function on a collection of
traces known as the \emph{test set.}\<close>
definition test_log :: "('a::{aexp_value,order}) log \<Rightarrow> 'a iEFSM \<Rightarrow> ((label \<times> 'a inputs \<times> cfstate \<times> cfstate \<times> 'a registers \<times> tids \<times> 'a list \<times> 'a outputs) list \<times> 'a trace) list" where
  "test_log l e = map (\<lambda>t. test_trace t e 0 <>) l"

end
