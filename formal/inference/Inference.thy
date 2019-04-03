subsection \<open>Extended Finite State Machine Inference\<close>
text\<open>
This theory sets out the key definitions for the inference of extended finite state machines from
system traces.
\<close>

theory Inference
  imports "../EFSM" "../Contexts" Transition_Ordering
          "~~/src/HOL/Library/Product_Lexorder"
begin

text\<open>
We first need dest define the iEFSM data type which assigns each transition a unique identity. This is
necessary because transitions may not be unique in an EFSM. Assigning transitions a unique
identifier enables us dest look up the origin and destination states of transitions without having dest
pass them around in the inference functions.
\<close>
type_synonym iEFSM = "(nat \<times> (nat \<times> nat) \<times> transition) fset"

definition get_by_id :: "iEFSM \<Rightarrow> nat \<Rightarrow> transition" where
  "get_by_id e u = snd (snd (fthe_elem (ffilter (\<lambda>(uid, _). uid = u) e)))"

definition max_uid :: "iEFSM \<Rightarrow> nat" where
  "max_uid e = fMax (fimage fst e)"

primrec toiEFSM_aux :: "nat \<Rightarrow> ((nat \<times> nat) \<times> transition) list \<Rightarrow> (nat \<times> (nat \<times> nat) \<times> transition) list" where
  "toiEFSM_aux _ [] = []" |
  "toiEFSM_aux n (h#t) = (n, h)#(toiEFSM_aux (n+1) t)"

definition toiEFSM :: "transition_matrix \<Rightarrow> iEFSM" where
  "toiEFSM e = fset_of_list (toiEFSM_aux 0 (sorted_list_of_fset e))"

definition tm :: "iEFSM \<Rightarrow> transition_matrix" where
  "tm t = fimage (\<lambda>x. snd x) t"

definition maxUID :: "iEFSM \<Rightarrow> nat" where
  "maxUID e = fMax (fimage (\<lambda>x. fst x) e)"

definition merge_states_aux :: "nat \<Rightarrow> nat \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "merge_states_aux x y t = (fimage (\<lambda>(uid, (origin, dest), t). (uid, (if origin = x then y else origin , if dest = x then y else dest), t)) t)"

definition merge_states :: "nat \<Rightarrow> nat \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "merge_states x y t = (if x > y then merge_states_aux x y t else merge_states_aux y x t)"

lemma merge_states_reflexive: "merge_states x x t = t"
  apply (simp add: merge_states_def merge_states_aux_def)
  apply (simp add: fimage_def)
  apply (simp add: fset_both_sides Abs_fset_inverse)
  by force

lemma merge_states_symmetry: "merge_states x y t = merge_states y x t"
  by (simp add: merge_states_def merge_states_aux_def)

(* declare[[show_types,show_sorts]] *)

definition choice :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "choice t t' = ((Label t) = (Label t') \<and> (Arity t) = (Arity t') \<and> (\<exists> s. apply_guards (Guard t) s \<and> apply_guards (Guard t') s))"

lemma choice_symmetry: "choice x y = choice y x"
  using choice_def by auto

definition outgoing_transitions :: "nat \<Rightarrow> iEFSM \<Rightarrow> (nat \<times> transition \<times> nat) fset" where
  "outgoing_transitions n t = fimage (\<lambda>(uid, x, t'). (snd x, t', uid)) (ffilter (\<lambda>(uid, (origin, dest), t). origin = n) t)"

type_synonym nondeterministic_pair = "(nat \<times> (nat \<times> nat) \<times> ((transition \<times> nat) \<times> (transition \<times> nat)))"

definition state_nondeterminism :: "nat \<Rightarrow> (nat \<times> transition \<times> nat) fset \<Rightarrow> nondeterministic_pair fset" where
  "state_nondeterminism origin nt = (if size nt < 2 then {||} else ffUnion (fimage (\<lambda>x. let (dest, t) = x in fimage (\<lambda>y. let (dest', t') = y in (origin, (dest, dest'), (t, t'))) (nt - {|x|})) nt))"

lemma state_nondeterminism_empty[simp]: "state_nondeterminism a {||} = {||}"
  by (simp add: state_nondeterminism_def ffilter_def Set.filter_def)

lemma state_nondeterminism_singledestn[simp]: "state_nondeterminism a {|x|} = {||}"
  by (simp add: state_nondeterminism_def ffilter_def Set.filter_def)

definition S :: "iEFSM \<Rightarrow> nat fset" where
  "S m = (fimage (\<lambda>(uid, (s, s'), t). s) m) |\<union>| fimage (\<lambda>(uid, (s, s'), t). s') m"

lemma S_alt: "S t = EFSM.S (fimage snd t)"
  apply (simp add: S_def EFSM.S_def)
  by force

(* For each state, get its outgoing transitions and see if there's any nondeterminism there *)
definition nondeterministic_pairs :: "iEFSM \<Rightarrow> nondeterministic_pair fset" where
  "nondeterministic_pairs t = ffilter (\<lambda>(_, (d1, d2), t, t'). choice (fst t) (fst t')) (ffUnion (fimage (\<lambda>s. state_nondeterminism s (outgoing_transitions s t)) (S t)))"

definition nondeterministic_transitions :: "iEFSM \<Rightarrow> nondeterministic_pair option" where
  "nondeterministic_transitions t = (if nondeterministic_pairs t = {||} then None else Some (fMax (nondeterministic_pairs t)))"

definition deterministic :: "iEFSM \<Rightarrow> bool" where
  "deterministic t = (nondeterministic_pairs t = {||})"

definition nondeterministic :: "iEFSM \<Rightarrow> bool" where
  "nondeterministic t = (\<not> deterministic t)"

definition replace_transition :: "iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> iEFSM" where
  "replace_transition t uid from dest orig new = (ffilter (\<lambda>x. snd x \<noteq> ((from, dest), orig) \<and> snd x \<noteq> ((from, dest), new)) t) |\<union>| {|(uid, (from, dest), new)|}"

definition exits_state :: "iEFSM \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> bool" where
  "exits_state e t from = (\<exists>dest uid. (uid, (from, dest), t) |\<in>| e)"

primrec make_guard :: "value list \<Rightarrow> nat \<Rightarrow> guard list" where
"make_guard [] _ = []" |
"make_guard (h#t) n = (gexp.Eq (V (I n)) (L h))#(make_guard t (n+1))"

primrec make_outputs :: "value list \<Rightarrow> output_function list" where
  "make_outputs [] = []" |
  "make_outputs (h#t) = (L h)#(make_outputs t)"

fun maxS :: "transition_matrix \<Rightarrow> nat" where
  "maxS t = (if t = {||} then 0 else fMax ((fimage (\<lambda>((origin, dest), t). origin) t) |\<union>| (fimage (\<lambda>((origin, dest), t). dest) t)))"

fun make_branch :: "transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> (label \<times> value list \<times> value list) list \<Rightarrow> transition_matrix" where
  "make_branch e _ _ [] = e" |
  "make_branch e s r ((label, inputs, outputs)#t) =
    (case (step e s r label inputs) of
      (Some (transition, s', outputs, updated)) \<Rightarrow> (make_branch e s' updated t) |
      None \<Rightarrow> make_branch (finsert ((s, (maxS e)+1), \<lparr>Label=label, Arity=length inputs, Guard=(make_guard inputs 1), Outputs=(make_outputs outputs), Updates=[]\<rparr>) e) ((maxS e)+1) r t
    )"

(* An execution represents a run of the software and has the form [(label, inputs, outputs)]*)
type_synonym execution = "(label \<times> value list \<times> value list) list"
type_synonym log = "execution list"

primrec make_pta :: "log \<Rightarrow> transition_matrix \<Rightarrow> transition_matrix" where
  "make_pta [] e = e" |
  "make_pta (h#t) e = (make_pta t (make_branch e 0 <> h))"

type_synonym update_modifier = "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> iEFSM option"

definition null_modifier :: update_modifier where
  "null_modifier a b c d e = None"

type_synonym scoreboard = "(nat \<times> (nat \<times> nat)) fset"
type_synonym strategy = "transition fset \<Rightarrow> transition fset \<Rightarrow> nat"

definition score :: "iEFSM \<Rightarrow> strategy \<Rightarrow> scoreboard" where
  "score t rank = ffilter (\<lambda>(score, _). score > 0) (fimage (\<lambda>(s1, s2). (rank (fimage (\<lambda>(_, t, _). t) (outgoing_transitions s1 t)) (fimage (\<lambda>(_, t, _). t) (outgoing_transitions s2 t)), (s1, s2))) (ffilter (\<lambda>(x, y). x < y) ((S t) |\<times>| (S t))))"

definition origin :: "nat \<Rightarrow> iEFSM \<Rightarrow> nat" where
  "origin uid t = fst (fst (snd (fthe_elem (ffilter (\<lambda>x. (\<exists>s. x = (uid, s))) t))))"

lemma origin_code: "origin uid t = fst (fst (snd (fthe_elem (ffilter (\<lambda>x. fst x = uid) t))))"
  apply (simp add: origin_def)
  by (metis fst_eqD surj_pair)

definition dest :: "nat \<Rightarrow> iEFSM \<Rightarrow> nat" where
  "dest uid t = snd (fst (snd (fthe_elem (ffilter (\<lambda>x. (\<exists>s. x = (uid, s))) t))))"

lemma exists_is_fst: "(\<lambda>x. (\<exists>s. x = (uid, s))) = (\<lambda>x. fst x = uid)"
  apply (rule ext)
  apply clarify
  by simp

lemma dest_code: "dest uid t = snd (fst (snd (fthe_elem (ffilter (\<lambda>x. fst x = uid) t))))"
  apply (simp add: dest_def)
  by (metis fst_eqD surj_pair)

inductive satisfies_trace :: "execution \<Rightarrow> transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> bool" where
  base: "satisfies_trace [] e s d" |
  step: "step e s d l i = Some (t, s', (map (\<lambda>x. Some x) p), d') \<Longrightarrow>
         satisfies_trace ex e s' d' \<Longrightarrow>
         satisfies_trace ((l, i, p)#ex) e s d"

definition satisfies :: "execution set \<Rightarrow> transition_matrix \<Rightarrow> bool" where
  "satisfies T e = (\<forall>t \<in> T. satisfies_trace t e 0 <>)"

definition directly_subsumes :: "iEFSM \<Rightarrow> iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> bool" where
  "directly_subsumes e1 e2 s s' t1 t2 \<equiv> (\<forall>p. accepts_trace (tm e1) p \<and> gets_us_to s (tm e1) 0 <>  p \<longrightarrow>
                                          accepts_trace (tm e2) p \<and> gets_us_to s' (tm e2) 0 <>  p \<longrightarrow>
                                          subsumes t1 (anterior_context (tm e2) p) t2) \<and>
                                     (\<exists>c. subsumes t1 c t2)"

lemma directly_subsumes_self: "directly_subsumes e1 e2 s s' t t"
  by (simp add: directly_subsumes_def posterior_def posterior_separate_append_self subsumes_def)

lemma gets_us_to_and_not_subsumes: "\<exists>p. accepts_trace (tm e1) p \<and> gets_us_to s (tm e1) 0 Map.empty p \<and> accepts_trace (tm e2) p \<and> gets_us_to s' (tm e2) 0 Map.empty p \<and> \<not> subsumes t1 (anterior_context (tm e2) p) t2 \<Longrightarrow> \<not> directly_subsumes e1 e2 s s' t1 t2"
  by (simp add: directly_subsumes_def)

lemma cant_directly_subsume: "\<forall>c. \<not> subsumes t c t' \<Longrightarrow> \<not> directly_subsumes m m' s s' t t'"
  by (simp add: directly_subsumes_def)

(* merge_transitions - Try dest merge transitions t\<^sub>1 and t\<^sub>2 dest help resolve nondeterminism in
                       newEFSM. If either subsumes the other directly then the subsumed transition
                       can simply be replaced with the subsuming one, else we try dest apply the
                       modifier function dest resolve nondeterminism that way.                      *)
(* @param oldEFSM   - the EFSM before merging the states which caused the nondeterminism          *)
(* @param newEFSM   - the current EFSM with nondeterminism                                        *)
(* @param t\<^sub>1        - a transition dest be merged with t\<^sub>2                                           *)
(* @param u\<^sub>1        - the unique identifier of t\<^sub>1                                                 *)
(* @param t\<^sub>2        - a transition dest be merged with t\<^sub>1                                           *)
(* @param u\<^sub>2        - the unique identifier of t\<^sub>2                                                 *)
(* @param modifier  - an update modifier function which tries dest generalise transitions           *)
definition merge_transitions :: "iEFSM \<Rightarrow> iEFSM \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> update_modifier \<Rightarrow> iEFSM option" where
  "merge_transitions oldEFSM destMerge t\<^sub>1 u\<^sub>1 t\<^sub>2 u\<^sub>2 modifier = (
     if directly_subsumes oldEFSM destMerge (origin u\<^sub>1 oldEFSM) (origin u\<^sub>1 destMerge) t\<^sub>2 t\<^sub>1 then
       Some (replace_transition destMerge u\<^sub>1 (origin u\<^sub>1 destMerge) (dest u\<^sub>2 destMerge) t\<^sub>1 t\<^sub>2)
     else if directly_subsumes oldEFSM destMerge (origin u\<^sub>2 oldEFSM) (origin u\<^sub>2 destMerge) t\<^sub>1 t\<^sub>2 then
       Some (replace_transition destMerge u\<^sub>1 (origin u\<^sub>1 destMerge) (dest u\<^sub>1 destMerge) t\<^sub>2 t\<^sub>1)
     else
        modifier u\<^sub>1 u\<^sub>2 (origin u\<^sub>1 destMerge) destMerge oldEFSM
   )"

fun make_distinct_aux :: "(nat \<times> (nat \<times> nat) \<times> transition) list \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "make_distinct_aux [] e = e" |
  "make_distinct_aux (h#t) e = (if snd h |\<in>| fimage snd e then make_distinct_aux t e else make_distinct_aux t (finsert h e))"

(* This removes duplicate transitions (i.e. identical transitions with the same origin and        *)
(* destination states but with different uids                                                     *)
definition make_distinct :: "iEFSM option \<Rightarrow> iEFSM option" where
  "make_distinct e = (case e of None \<Rightarrow> None | Some e \<Rightarrow> Some (make_distinct_aux (sorted_list_of_fset e) {||}))"

(* resolve_nondeterminism - tries dest resolve nondeterminism in a given iEFSM                      *)
(* @param ((from, (dest\<^sub>1, dest\<^sub>2), ((t\<^sub>1, u\<^sub>1), (t\<^sub>2, u\<^sub>2)))#ss) - a list of nondeterministic pairs where
          from - nat - the state from which t\<^sub>1 and t\<^sub>2 eminate
          dest\<^sub>1  - nat - the destination state of t\<^sub>1
          dest\<^sub>2  - nat - the destination state of t\<^sub>2
          t\<^sub>1   - transition - a transition dest be merged with t\<^sub>2
          t\<^sub>2   - transition - a transition dest be merged with t\<^sub>1
          u\<^sub>1   - nat - the unique identifier of t\<^sub>1
          u\<^sub>2   - nat - the unique identifier of t\<^sub>2
          ss   - list - the rest of the list                                                      *)
(* @param oldEFSM - the EFSM before merging the states which caused the nondeterminism            *)
(* @param newEFSM - the current EFSM with nondeterminism                                          *)
(* @param m       - an update modifier function which tries dest generalise transitions             *)
(* @param check - a function which takes an EFSM and returns a bool dest ensure that certain
                  properties hold in the new iEFSM                                                *)
function resolve_nondeterminism :: "nondeterministic_pair list \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> iEFSM option" where
  "resolve_nondeterminism [] _ new _ check = (if deterministic new \<and> check (tm new) then Some new else None)" |
  "resolve_nondeterminism ((from, (dest\<^sub>1, dest\<^sub>2), ((t\<^sub>1, u\<^sub>1), (t\<^sub>2, u\<^sub>2)))#ss) oldEFSM newEFSM m check = (let
     destMerge = merge_states (dest u\<^sub>1 newEFSM) (dest u\<^sub>2 newEFSM) newEFSM
     in
     case make_distinct (merge_transitions oldEFSM destMerge t\<^sub>1 u\<^sub>1 t\<^sub>2 u\<^sub>2 m) of
       None \<Rightarrow> resolve_nondeterminism ss oldEFSM newEFSM m check |
       Some new \<Rightarrow>
         let newScores = (sorted_list_of_fset (nondeterministic_pairs new)) in 
         if length (newScores) + size new < length (ss) + 1 + size newEFSM then
           case resolve_nondeterminism newScores oldEFSM new m check of
             Some new' \<Rightarrow> Some new' |
             None \<Rightarrow> resolve_nondeterminism ss oldEFSM newEFSM m check
         else
          None
   )"
     apply clarify
     apply simp
     apply (metis neq_Nil_conv prod_cases3 surj_pair)
  by auto
termination
  by (relation "measures [\<lambda>(ss, oldEFSM, newEFSM, m, check). length ss + size newEFSM]") auto

(* Merge - tries dest merge two states in a given iEFSM and resolve the resulting nondeterminism    *)
(* @param e     - an iEFSM                                                                        *)
(* @param s1    - a state dest be merged with s2                                                    *)
(* @param s2    - a state dest be merged with s1                                                    *)
(* @param m     - an update modifier function which tries dest generalise transitions               *)
(* @param check - a function which takes an EFSM and returns a bool dest ensure that certain
                  properties hold in the new iEFSM                                                *)
definition merge :: "iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> iEFSM option" where
  "merge e s\<^sub>1 s\<^sub>2 m check = (
    if s\<^sub>1 = s\<^sub>2 then
      None 
    else 
      let e' = (merge_states s\<^sub>1 s\<^sub>2 e) in
      resolve_nondeterminism (sorted_list_of_fset (nondeterministic_pairs e')) e e' m check
  )"

(* inference_step - attempt dest carry out a single step of the inference process by merging the    *)
(* @param e - an iEFSM dest be generalised                                                          *)
(* @param ((s, s1, s2)#t) - a list of triples of the form (score, state, state) dest be merged      *)
(* @param m     - an update modifier function which tries dest generalise transitions               *)
(* @param check - a function which takes an EFSM and returns a bool dest ensure that certain
                  properties hold in the new iEFSM                                                *)
fun inference_step :: "iEFSM \<Rightarrow> (nat \<times> nat \<times> nat) list \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> iEFSM option" where
  "inference_step _ [] _ _ = None" |
  "inference_step e ((s, s\<^sub>1, s\<^sub>2)#t) m check = (
    if s > 0 then
       case merge e s\<^sub>1 s\<^sub>2 m check of
         Some new \<Rightarrow> Some new |
         None \<Rightarrow> inference_step e t m check
     else None
  )"

(* Takes an iEFSM and iterates inference_step until no further states can be successfully merged  *)
(* @param e - an iEFSM dest be generalised                                                          *)
(* @param r - a strategy dest identify and prioritise pairs of states dest merge                      *)
(* @param m     - an update modifier function which tries dest generalise transitions               *)
(* @param check - a function which takes an EFSM and returns a bool dest ensure that certain
                  properties hold in the new iEFSM                                                *)
fun infer :: "iEFSM \<Rightarrow> strategy \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> iEFSM" where
  "infer e r m check = (
    case inference_step e (rev (sorted_list_of_fset (score e r))) m check of
      None \<Rightarrow> e |
      Some new \<Rightarrow> if size new < size e then infer new r m check else e
  )"

primrec iterative_learn_aux :: "log \<Rightarrow> log \<Rightarrow> iEFSM \<Rightarrow> strategy \<Rightarrow> (log \<Rightarrow> update_modifier) \<Rightarrow> (log \<Rightarrow> transition_matrix \<Rightarrow> bool) \<Rightarrow> iEFSM" where
  "iterative_learn_aux [] _ e _ _ _ = e" |
  "iterative_learn_aux (h#t) l e r m s = iterative_learn_aux t (h#l) (infer (toiEFSM (make_branch (tm e) 0 <> h)) r (m (h#l)) (s (h#l))) r m s"

definition iterative_learn :: "log \<Rightarrow> strategy \<Rightarrow> (log \<Rightarrow> update_modifier) \<Rightarrow> transition_matrix" where
  "iterative_learn l r m = tm (iterative_learn_aux l [] {||} r m (\<lambda>l. satisfies (set l)))"

definition learn :: "log \<Rightarrow> strategy \<Rightarrow> update_modifier \<Rightarrow> transition_matrix" where
  "learn l r m = tm (infer (toiEFSM (make_pta l {||})) r m (satisfies (set l)))"

definition uids :: "iEFSM \<Rightarrow> nat fset" where
  "uids e = fimage fst e"

lemma dest_from_in_S_uid_in_uids: "(uid, (from, to), t) |\<in>| e \<Longrightarrow> to |\<in>| S e \<and> from |\<in>| S e \<and> uid |\<in>| uids e"
  apply (simp add: S_def uids_def)
  by force

fun enumerate_aexp_regs :: "aexp \<Rightarrow> nat set" where
  "enumerate_aexp_regs (L _) = {}" |
  "enumerate_aexp_regs (V (R n)) = {n}" |
  "enumerate_aexp_regs (V (I _)) = {}" |
  "enumerate_aexp_regs (Plus v va) = enumerate_aexp_regs v \<union> enumerate_aexp_regs va" |
  "enumerate_aexp_regs (Minus v va) = enumerate_aexp_regs v \<union> enumerate_aexp_regs va"

fun enumerate_gexp_regs :: "gexp \<Rightarrow> nat set" where
  "enumerate_gexp_regs (GExp.Bc _) = {}" |
  "enumerate_gexp_regs (GExp.Null v) = enumerate_aexp_regs v" |
  "enumerate_gexp_regs (GExp.Eq v va) = enumerate_aexp_regs v \<union> enumerate_aexp_regs va" |
  "enumerate_gexp_regs (GExp.Lt v va) = enumerate_aexp_regs v \<union> enumerate_aexp_regs va" |
  "enumerate_gexp_regs (GExp.Nor v va) = enumerate_gexp_regs v \<union> enumerate_gexp_regs va"

definition enumerate_t_regs :: "transition \<Rightarrow> nat set" where
  "enumerate_t_regs t = (\<Union> set (map enumerate_gexp_regs (Guard t))) \<union>
                                (\<Union> set (map enumerate_aexp_regs (Outputs t))) \<union>
                                (\<Union> set (map (\<lambda>(_, u). enumerate_aexp_regs u) (Updates t))) \<union>
                                (\<Union> set (map (\<lambda>(r, _). enumerate_aexp_regs (V r)) (Updates t)))"

definition get_by_id_biggest_t_reg :: "transition \<Rightarrow> nat" where
  "get_by_id_biggest_t_reg t = Max ({0} \<union> enumerate_t_regs t)"

definition max_reg :: "iEFSM \<Rightarrow> nat" where
  "max_reg e = fMax (fimage (\<lambda>(_, _, t). get_by_id_biggest_t_reg t) e)"

definition max_output :: "iEFSM \<Rightarrow> nat" where
  "max_output e = fMax (fimage (\<lambda>(_, _, t). length (Outputs t)) e)"

primrec try_heuristics :: "update_modifier list \<Rightarrow> update_modifier" where
  "try_heuristics [] = null_modifier" |
  "try_heuristics (h#t) = (\<lambda>a b c d e. case h a b c d e of Some e' \<Rightarrow> Some e' | None \<Rightarrow> try_heuristics t a b c d e)"

primrec iterative_try_heuristics :: "(log \<Rightarrow> update_modifier) list \<Rightarrow> log \<Rightarrow> update_modifier" where
  "iterative_try_heuristics [] l = null_modifier" |
  "iterative_try_heuristics (h#t) l = (\<lambda>a b c d e. case (h l) a b c d e of
                                        Some e' \<Rightarrow> Some e' |
                                        None \<Rightarrow>  iterative_try_heuristics t l a b c d e
                                      )"

definition replaceAll :: "iEFSM \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> iEFSM" where
  "replaceAll e old new = fimage (\<lambda>(uid, (from, dest), t). if t = old then (uid, (from, dest), new) else (uid, (from, dest), t)) e"

definition all_regs :: "iEFSM \<Rightarrow> nat set" where
  "all_regs e = \<Union> image (\<lambda>(_, _, t). enumerate_t_regs t) (fset e)"
end
