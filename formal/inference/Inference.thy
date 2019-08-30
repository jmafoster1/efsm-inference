subsection \<open>Extended Finite State Machine Inference\<close>
text\<open>
This theory sets out the key definitions for the inference of extended finite state machines from
system traces.
\<close>

theory Inference
  imports "../EFSM" "../Contexts" Transition_Ordering
          "~~/src/HOL/Library/Product_Lexorder"
begin

declare One_nat_def [simp del]

text\<open>
We first need dest define the iEFSM data type which assigns each transition a unique identity. This is
necessary because transitions may not be unique in an EFSM. Assigning transitions a unique
identifier enables us dest look up the origin and destination states of transitions without having dest
pass them around in the inference functions.
\<close>
type_synonym tid = nat
type_synonym iEFSM = "(tid \<times> (cfstate \<times> cfstate) \<times> transition) fset"

definition get_by_id :: "iEFSM \<Rightarrow> nat \<Rightarrow> transition" ("(_|_|)" [20, 20] 40) where
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

lemma in_tm: "\<exists>s. ((s, a), bb) |\<in>| tm b \<Longrightarrow> \<exists>s id. (id, (s, a), bb) |\<in>| b"
  apply (simp add: tm_def fimage_def fmember_def Abs_fset_inverse)
  by fastforce

definition maxUID :: "iEFSM \<Rightarrow> nat" where
  "maxUID e = fMax (fimage (\<lambda>x. fst x) e)"

definition merge_states_aux :: "nat \<Rightarrow> nat \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "merge_states_aux x y t = (fimage (\<lambda>(uid, (origin, dest), t). (uid, (if origin = x then y else origin , if dest = x then y else dest), t)) t)"

definition merge_states :: "nat \<Rightarrow> nat \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "merge_states x y t = (if x > y then merge_states_aux x y t else merge_states_aux y x t)"

lemma merge_states_same: "merge_states x x t = t"
  apply (simp add: merge_states_def merge_states_aux_def)
  apply (simp add: fimage_def)
  apply (simp add: fset_both_sides Abs_fset_inverse)
  by force

lemma merge_states_symmetry: "merge_states x y t = merge_states y x t"
  by (simp add: merge_states_def merge_states_aux_def)

(* declare[[show_types,show_sorts]] *)

definition outgoing_transitions :: "cfstate \<Rightarrow> iEFSM \<Rightarrow> (cfstate \<times> transition \<times> tid) fset" where
  "outgoing_transitions n t = fimage (\<lambda>(uid, (from, to), t'). (to, t', uid)) (ffilter (\<lambda>(uid, (origin, dest), t). origin = n) t)"

type_synonym nondeterministic_pair = "(nat \<times> (nat \<times> nat) \<times> ((transition \<times> nat) \<times> (transition \<times> nat)))"

definition state_nondeterminism :: "nat \<Rightarrow> (nat \<times> transition \<times> nat) fset \<Rightarrow> nondeterministic_pair fset" where
  "state_nondeterminism origin nt = (if size nt < 2 then {||} else ffUnion (fimage (\<lambda>x. let (dest, t) = x in fimage (\<lambda>y. let (dest', t') = y in (origin, (dest, dest'), (t, t'))) (nt - {|x|})) nt))"

lemma state_nondeterminism_empty[simp]: "state_nondeterminism a {||} = {||}"
  by (simp add: state_nondeterminism_def ffilter_def Set.filter_def)

lemma state_nondeterminism_singledestn[simp]: "state_nondeterminism a {|x|} = {||}"
  by (simp add: state_nondeterminism_def ffilter_def Set.filter_def)

definition S :: "iEFSM \<Rightarrow> nat fset" where
  "S m = (fimage (\<lambda>(uid, (s, s'), t). s) m) |\<union>| fimage (\<lambda>(uid, (s, s'), t). s') m"

lemma S_alt: "S t = EFSM.S (tm t)"
  apply (simp add: S_def EFSM.S_def tm_def)
  by force

lemma to_in_S: "(\<exists>to from uid. (uid, (from, to), t) |\<in>| xb \<longrightarrow> to |\<in>| S xb)"
  apply (simp add: S_def)
  by blast

lemma from_in_S: "(\<exists>to from uid. (uid, (from, to), t) |\<in>| xb \<longrightarrow> from |\<in>| S xb)"
  apply (simp add: S_def)
  by blast

(* For each state, get its outgoing transitions and see if there's any nondeterminism there *)
definition nondeterministic_pairs :: "iEFSM \<Rightarrow> nondeterministic_pair fset" where
  "nondeterministic_pairs t = ffilter (\<lambda>(_, _, (t, _), (t', _)). Label t = Label t' \<and> Arity t = Arity t' \<and> choice t t') (ffUnion (fimage (\<lambda>s. state_nondeterminism s (outgoing_transitions s t)) (S t)))"

definition nondeterministic_pairs_labar :: "iEFSM \<Rightarrow> nondeterministic_pair fset" where
  "nondeterministic_pairs_labar t = ffilter
     (\<lambda>(_, (d, d'), (t, _), (t', _)).
      Label t = Label t' \<and> Arity t = Arity t' \<and> (choice t t' \<or> (Outputs t = Outputs t' \<and> d = d')))
     (ffUnion (fimage (\<lambda>s. state_nondeterminism s (outgoing_transitions s t)) (S t)))"

definition deterministic :: "iEFSM \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> bool" where
  "deterministic t np = (np t = {||})"

definition nondeterministic :: "iEFSM \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> bool" where
  "nondeterministic t np = (\<not> deterministic t np)"

definition replace_transition :: "iEFSM \<Rightarrow> tid \<Rightarrow> cfstate \<Rightarrow> cfstate \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> iEFSM" where
  "replace_transition t uid from dest orig new = (ffilter (\<lambda>x. snd x \<noteq> ((from, dest), orig) \<and> snd x \<noteq> ((from, dest), new)) t) |\<union>| {|(uid, (from, dest), new)|}"

definition exits_state :: "iEFSM \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> bool" where
  "exits_state e t from = (\<exists>dest uid. (uid, (from, dest), t) |\<in>| e)"

primrec make_guard :: "value list \<Rightarrow> nat \<Rightarrow> gexp list" where
"make_guard [] _ = []" |
"make_guard (h#t) n = (gexp.Eq (V (vname.I n)) (L h))#(make_guard t (n+1))"

primrec make_outputs :: "value list \<Rightarrow> output_function list" where
  "make_outputs [] = []" |
  "make_outputs (h#t) = (L h)#(make_outputs t)"

fun maxS :: "transition_matrix \<Rightarrow> nat" where
  "maxS t = (if t = {||} then 0 else fMax ((fimage (\<lambda>((origin, dest), t). origin) t) |\<union>| (fimage (\<lambda>((origin, dest), t). dest) t)))"

(* An execution represents a run of the software and has the form [(label, inputs, outputs)]*)
type_synonym execution = "(label \<times> value list \<times> value list) list"
type_synonym log = "execution list"

fun make_branch :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> transition_matrix" where
  "make_branch e _ _ [] = e" |
  "make_branch e s r ((label, inputs, outputs)#t) =
    (case (step e s r label inputs) of
      Some (transition, s', outputs', updated) \<Rightarrow> 
        if outputs' = (map Some outputs) then
          make_branch e s' updated t
        else 
          make_branch (finsert ((s, (maxS e)+1), \<lparr>Label=label, Arity=length inputs, Guard=(make_guard inputs 0), Outputs=(make_outputs outputs), Updates=[]\<rparr>) e) ((maxS e)+1) r t  |
      None \<Rightarrow> make_branch (finsert ((s, (maxS e)+1), \<lparr>Label=label, Arity=length inputs, Guard=(make_guard inputs 0), Outputs=(make_outputs outputs), Updates=[]\<rparr>) e) ((maxS e)+1) r t
    )"

primrec make_pta :: "log \<Rightarrow> transition_matrix \<Rightarrow> transition_matrix" where
  "make_pta [] e = e" |
  "make_pta (h#t) e = make_pta t (make_branch e 0 <> h)"

lemma make_pta_fold_all_e: "\<forall>e. make_pta l e = fold (\<lambda>h e. make_branch e 0 <> h) l e"
proof(induct l)
case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
    by simp
qed

lemma make_pta_fold: "make_pta l e = fold (\<lambda>h e. make_branch e 0 <> h) l e"
  by (simp add: make_pta_fold_all_e)

type_synonym update_modifier = "tid \<Rightarrow> tid \<Rightarrow> cfstate \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM option"

definition null_modifier :: update_modifier where
  "null_modifier _ _ _ _ _ _ = None"

type_synonym scoreboard = "(nat \<times> (cfstate \<times> cfstate)) fset"
type_synonym strategy = "tid \<Rightarrow> tid \<Rightarrow> iEFSM \<Rightarrow> nat"

primrec k_outgoing :: "nat \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> (cfstate \<times> transition \<times> tid) fset" where
  "k_outgoing 0 i s = outgoing_transitions s i" |
  "k_outgoing (Suc m) i s = (let
     outgoing = outgoing_transitions s i;
     others = fimage fst outgoing in
     outgoing |\<union>| ffUnion (fimage (\<lambda>s. k_outgoing m i s) others)
  )"

definition k_score :: "nat \<Rightarrow> iEFSM \<Rightarrow> strategy \<Rightarrow> scoreboard" where
  "k_score n e rank = (let 
     states = (S e);
     pairs_to_score = (ffilter (\<lambda>(x, y). x < y) (states |\<times>| states));
     scores = fimage (\<lambda>(s1, s2). let
        outgoing_s1 = fimage (snd \<circ> snd) (k_outgoing n e s1);
        outgoing_s2 = fimage (snd \<circ> snd) (k_outgoing n e s2);
        scores = fimage (\<lambda>(x, y). rank x y e) (outgoing_s1 |\<times>| outgoing_s2) in
       (fSum scores, s1, s2 )
     ) pairs_to_score in
     ffilter (\<lambda>(score, _). score > 0) scores)"

definition origin :: "nat \<Rightarrow> iEFSM \<Rightarrow> nat" where
  "origin uid t = fst (fst (snd (fthe_elem (ffilter (\<lambda>x. (\<exists>s. x = (uid, s))) t))))"

lemma origin_code [code]: "origin uid t = fst (fst (snd (fthe_elem (ffilter (\<lambda>x. fst x = uid) t))))"
  apply (simp add: origin_def)
  by (metis fst_eqD surj_pair)

definition dest :: "nat \<Rightarrow> iEFSM \<Rightarrow> nat" where
  "dest uid t = snd (fst (snd (fthe_elem (ffilter (\<lambda>x. (\<exists>s. x = (uid, s))) t))))"

lemma dest_code [code]: "dest uid t = snd (fst (snd (fthe_elem (ffilter (\<lambda>x. fst x = uid) t))))"
  apply (simp add: dest_def)
  by (metis fst_eqD surj_pair)

inductive satisfies_trace :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> bool" where
  base: "satisfies_trace e s d []" |                                         
  step: "\<exists>(s', T) |\<in>| possible_steps e s d l i.
         apply_outputs (Outputs T) (join_ir i d) = (map Some p) \<and>
         satisfies_trace e s' (apply_updates (Updates T) (join_ir i d) d) t \<Longrightarrow>
         satisfies_trace e s d ((l, i, p)#t)"

definition satisfies :: "execution set \<Rightarrow> transition_matrix \<Rightarrow> bool" where
  "satisfies T e = (\<forall>t \<in> T. satisfies_trace e 0 <> t)"

definition directly_subsumes :: "iEFSM \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> cfstate \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> bool" where
  "directly_subsumes e1 e2 s s' t1 t2 \<equiv> (\<forall>p. accepts_trace (tm e1) p \<and> gets_us_to s (tm e1) 0 <>  p \<longrightarrow>
                                             accepts_trace (tm e2) p \<and> gets_us_to s' (tm e2) 0 <>  p \<longrightarrow>
                                             (\<forall>c. anterior_context (tm e2) p = Some c \<longrightarrow> subsumes t1 c t2)) \<and>
                                         (\<exists>c. subsumes t1 c t2)"

lemma directly_subsumes_self: "directly_subsumes e1 e2 s s' t t"
  apply (simp add: directly_subsumes_def)
  by (simp add: transition_subsumes_self)

lemma subsumes_in_all_contexts_directly_subsumes:
  "\<forall>c. subsumes t2 c t1 \<Longrightarrow> directly_subsumes e1 e2 s s' t2 t1"
  by (simp add: directly_subsumes_def)

lemma gets_us_to_and_not_subsumes: 
  "\<exists>p. accepts_trace (tm e1) p \<and>
       gets_us_to s (tm e1) 0 (K$ None) p \<and>
       accepts_trace (tm e2) p \<and>
       gets_us_to s' (tm e2) 0 (K$ None) p \<and>
       (anterior_context (tm e2) p) = Some a \<and>
       \<not> subsumes t1 a t2 \<Longrightarrow>
   \<not> directly_subsumes e1 e2 s s' t1 t2"
  unfolding directly_subsumes_def by auto

lemma cant_directly_subsume: "\<forall>c. \<not> subsumes t c t' \<Longrightarrow> \<not> directly_subsumes m m' s s' t t'"
  by (simp add: directly_subsumes_def)

definition drop_transition :: "iEFSM \<Rightarrow> nat \<Rightarrow> iEFSM" where
  "drop_transition e t = ffilter (\<lambda>(uid, _). uid \<noteq> t) e"

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
definition merge_transitions :: "iEFSM \<Rightarrow> iEFSM \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> update_modifier \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM option" where
  "merge_transitions oldEFSM destMerge t\<^sub>1 u\<^sub>1 t\<^sub>2 u\<^sub>2 modifier np = (
     if directly_subsumes oldEFSM destMerge (origin u\<^sub>1 oldEFSM) (origin u\<^sub>1 destMerge) t\<^sub>2 t\<^sub>1 then
       Some (drop_transition destMerge u\<^sub>1)
     else if directly_subsumes oldEFSM destMerge (origin u\<^sub>2 oldEFSM) (origin u\<^sub>2 destMerge) t\<^sub>1 t\<^sub>2 then
       Some (drop_transition destMerge u\<^sub>2)
     else
        modifier u\<^sub>1 u\<^sub>2 (origin u\<^sub>1 destMerge) destMerge oldEFSM np
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
function resolve_nondeterminism :: "nondeterministic_pair list \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM option" where
  "resolve_nondeterminism [] _ new _ check np = (if deterministic new np \<and> check (tm new) then Some new else None)" |
  "resolve_nondeterminism ((from, (dest\<^sub>1, dest\<^sub>2), ((t\<^sub>1, u\<^sub>1), (t\<^sub>2, u\<^sub>2)))#ss) oldEFSM newEFSM m check np = (let
     destMerge = if dest\<^sub>1 = dest\<^sub>2 then newEFSM else merge_states dest\<^sub>1 dest\<^sub>2 newEFSM
     in
     case make_distinct (merge_transitions oldEFSM destMerge t\<^sub>1 u\<^sub>1 t\<^sub>2 u\<^sub>2 m np) of
       None \<Rightarrow> resolve_nondeterminism ss oldEFSM newEFSM m check np |
       Some new \<Rightarrow>
         let newScores = (sorted_list_of_fset (np new)) in 
         if length (newScores) + size new < length (ss) + 1 + size newEFSM then
           case resolve_nondeterminism newScores oldEFSM new m check np of
             Some new' \<Rightarrow> Some new' |
             None \<Rightarrow> resolve_nondeterminism ss oldEFSM newEFSM m check np
         else
          None
   )"
     apply clarify
     apply simp
     apply (metis neq_Nil_conv prod_cases3 surj_pair)
  by auto
termination
  by (relation "measures [\<lambda>(ss, _, newEFSM, _). length ss + size newEFSM]") auto

(* Merge - tries dest merge two states in a given iEFSM and resolve the resulting nondeterminism    *)
(* @param e     - an iEFSM                                                                        *)
(* @param s1    - a state dest be merged with s2                                                    *)
(* @param s2    - a state dest be merged with s1                                                    *)
(* @param m     - an update modifier function which tries dest generalise transitions               *)
(* @param check - a function which takes an EFSM and returns a bool dest ensure that certain
                  properties hold in the new iEFSM                                                *)
definition merge :: "iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM option" where
  "merge e s\<^sub>1 s\<^sub>2 m check np = (
    if s\<^sub>1 = s\<^sub>2 then
      None 
    else 
      let e' = (merge_states s\<^sub>1 s\<^sub>2 e) in
      resolve_nondeterminism (sorted_list_of_fset (np e')) e e' m check np 
  )"

(* inference_step - attempt dest carry out a single step of the inference process by merging the    *)
(* @param e - an iEFSM dest be generalised                                                          *)
(* @param ((s, s1, s2)#t) - a list of triples of the form (score, state, state) dest be merged      *)
(* @param m     - an update modifier function which tries dest generalise transitions               *)
(* @param check - a function which takes an EFSM and returns a bool dest ensure that certain
                  properties hold in the new iEFSM                                                *)
fun inference_step :: "iEFSM \<Rightarrow> (nat \<times> nat \<times> nat) list \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM option" where
  "inference_step _ [] _ _ _ = None" |
  "inference_step e ((_, s\<^sub>1, s\<^sub>2)#t) m check np = (
     case merge e s\<^sub>1 s\<^sub>2 m check np of
       Some new \<Rightarrow> Some new |
       None \<Rightarrow> inference_step e t m check np
  )"

lemma measures_fsubset: "S x2 |\<subset>| S e \<Longrightarrow>
       ((x2, r, m, check, np), e, r, m, check, np) \<in> measures [\<lambda>(e, r, m, check, np). size (Inference.S e)]"
  using size_fsubset[of "S x2" "S e"]
  by simp

(* Takes an iEFSM and iterates inference_step until no further states can be successfully merged  *)
(* @param e - an iEFSM dest be generalised                                                          *)
(* @param r - a strategy dest identify and prioritise pairs of states dest merge                      *)
(* @param m     - an update modifier function which tries dest generalise transitions               *)
(* @param check - a function which takes an EFSM and returns a bool dest ensure that certain
                  properties hold in the new iEFSM                                                *)
function infer :: "nat \<Rightarrow> iEFSM \<Rightarrow> strategy \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM" where
  "infer n e r m check np = (
    case inference_step e (rev (sorted_list_of_fset (k_score n e r))) m check np of
      None \<Rightarrow> e |
      Some new \<Rightarrow> if (S new) |\<subset>| (S e) then infer n new r m check np else e
  )"
  by auto
termination
  apply (relation "measures [\<lambda>(n, e, _). size (S e)]")
   apply simp
  using measures_fsubset by auto

fun get_ints :: "execution \<Rightarrow> int list" where
  "get_ints [] = []" |
  "get_ints ((_, inputs, outputs)#t) = (map (\<lambda>x. case x of Num n \<Rightarrow> n) (filter is_Num (inputs@outputs)))"

fun get_smallest :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "get_smallest n s = (if n \<notin> set s then n else get_smallest (n + 1) (removeAll n s))"

definition make_smaller_aux :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "make_smaller_aux i s = (if i < 100 then i else get_smallest i s)"

fun make_smaller :: "int \<Rightarrow> nat list \<Rightarrow> int" where
  "make_smaller n s = (if n < 0 then - (int (make_smaller_aux (nat n) s)) else int (make_smaller_aux (nat n) s))"

fun make_smaller_val :: "nat list \<Rightarrow> value \<Rightarrow> value" where
  "make_smaller_val _ (value.Str s) = value.Str s" |
  "make_smaller_val s (Num n) = Num (make_smaller n s)"

definition learn :: "nat \<Rightarrow> log \<Rightarrow> strategy \<Rightarrow> update_modifier \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> transition_matrix" where
  "learn n l r m np = (
     let pta = make_pta l {||};
         check = satisfies (set l) in
         (tm (infer n (toiEFSM pta) r m check np))
   )"

definition uids :: "iEFSM \<Rightarrow> nat fset" where
  "uids e = fimage fst e"

lemma uid_in_uids: "(\<exists>to from uid. (uid, (from, to), t) |\<in>| xb \<longrightarrow> uid |\<in>| uids xb)"
  apply (simp add: uids_def)
  by blast

lemma to_from_in_S_uid_in_uids: "(uid, (from, to), t) |\<in>| e \<Longrightarrow> to |\<in>| S e \<and> from |\<in>| S e \<and> uid |\<in>| uids e"
  apply (simp add: S_def uids_def)
  by force

definition max_reg :: "iEFSM \<Rightarrow> nat option" where
  "max_reg e = (let maxes = (fimage (\<lambda>(_, _, t). Transition.max_reg t) e) in if maxes = {||} then None else fMax maxes)"

lemma fMax_None: "f \<noteq> {||} \<Longrightarrow> fMax f = None = (\<forall>x |\<in>| f. x = None)"
  apply standard
  using fMax_ge x_leq_None apply fastforce
  by (meson fBallE fMax_in)

lemma max_reg_none_no_updates: "Inference.max_reg b = None \<Longrightarrow>
       \<forall>(id, (s, s'), t) |\<in>| b.  (Updates t) = []"
  apply (simp add: Inference.max_reg_def)
  apply (case_tac "b = {||}")
   apply simp
  apply (simp add: fMax_None)
  apply clarify
  using max_reg_none_no_updates
  by force

definition total_max_reg :: "iEFSM \<Rightarrow> nat" where
  "total_max_reg e = (case fMax (fimage (\<lambda>(_, _, t). Transition.max_reg t) e) of None \<Rightarrow> 0 | Some r \<Rightarrow> r)"

definition max_output :: "iEFSM \<Rightarrow> nat" where
  "max_output e = fMax (fimage (\<lambda>(_, _, t). length (Outputs t)) e)"

primrec try_heuristics :: "update_modifier list \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> update_modifier" where
  "try_heuristics [] _ = null_modifier" |
  "try_heuristics (h#t) np = (\<lambda>a b c d e np. case h a b c d e np of Some e' \<Rightarrow> Some e' | None \<Rightarrow> (try_heuristics t np) a b c d e np)"

definition drop_transitions :: "iEFSM \<Rightarrow> nat fset \<Rightarrow> iEFSM" where
  "drop_transitions e t = ffilter (\<lambda>(uid, _). uid |\<notin>| t) e"

definition replaceAll :: "iEFSM \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> iEFSM" where
  "replaceAll e old new = fimage (\<lambda>(uid, (from, dest), t). if t = old then (uid, (from, dest), new) else (uid, (from, dest), t)) e"

definition replace :: "iEFSM \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> iEFSM" where
  "replace e tID t' = fimage (\<lambda>(uid, (from, dest), t). if uid = tID then (uid, (from, dest), t') else (uid, (from, dest), t)) e"

definition all_regs :: "iEFSM \<Rightarrow> nat set" where
  "all_regs e = \<Union> (image (\<lambda>(_, _, t). enumerate_registers t) (fset e))"

lemma no_choice_no_subsumption:
  "Label t = Label t' \<Longrightarrow>
   Arity t = Arity t' \<Longrightarrow>
   \<not> choice t t' \<Longrightarrow>
   \<exists>i. can_take_transition t' i c \<Longrightarrow>
  \<not> subsumes t c t'"
  apply (rule bad_guards)
  apply (simp add: can_take_transition_def can_take_def)
  apply clarify
  apply (rule_tac x=i in exI)
  using choice_def by blast

definition "satisfiable_list l = satisfiable (fold gAnd l (Bc True))"

definition simple_mutex :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "simple_mutex t t' = (
     max_reg_list (Guard t) = None \<and>
     max_input_list (Guard t) < Some (Arity t) \<and>
     satisfiable_list ((Guard t) @ ensure_not_null (Arity t)) \<and>
     Label t = Label t' \<and>
     Arity t = Arity t' \<and>
     \<not> choice t' t)"

lemma satisfiable_can_take:
  "max_input_list (Guard t) < Some (Arity t) \<Longrightarrow>
   satisfiable_list ((Guard t) @ ensure_not_null (Arity t)) \<Longrightarrow>
   \<exists>i r. can_take_transition t i r"
  apply (simp add: can_take_transition_def satisfiable_list_def satisfiable_def fold_apply_guards
                   apply_guards_append can_take_def del: fold_append)
  apply clarify
  apply (rule_tac x="take_or_pad i (Arity t)" in exI)
  apply standard
   apply (simp add: length_take_or_pad)
  apply (rule_tac x=r in exI)
  by (simp add: apply_guards_take_or_pad)

lemma can_take_satisfiable:
  "max_reg_list (Guard t) = None \<Longrightarrow>
   max_input_list (Guard t) < Some (Arity t) \<Longrightarrow>
   satisfiable_list ((Guard t) @ ensure_not_null (Arity t)) \<Longrightarrow>
   \<exists>i. can_take_transition t i r"
  apply (simp add: can_take_transition_def satisfiable_list_def satisfiable_def fold_apply_guards
                   apply_guards_append can_take_def del: fold_append)
  apply clarify
  apply (rule_tac x="take_or_pad i (Arity t)" in exI)
  apply standard
   apply (simp add: length_take_or_pad)
  by (simp add: apply_guards_no_reg_swap_regs)

lemma simple_mutex_direct_subsumption:
  "simple_mutex t t' \<Longrightarrow>
   \<not> directly_subsumes e e' s s' t' t"
  apply (rule cant_directly_subsume)
  apply (rule allI)
  apply (simp add: simple_mutex_def)
  by (metis can_take_satisfiable no_choice_no_subsumption)

definition max_int :: "iEFSM \<Rightarrow> int" where
  "max_int e = Max (insert 0 (EFSM.enumerate_ints (tm e)))"

end
