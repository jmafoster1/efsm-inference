theory Inference
  imports "../Nondeterministic_EFSM" "../EFSM" "../Contexts" Transition_Ordering
          "~~/src/HOL/Library/Product_Lexorder"
begin

(* I'd like to have unique uids as part of the type if I can *)

type_synonym iEFSM = "(nat \<times> (nat \<times> nat) \<times> transition) fset"

(*definition unique_uid :: "uEFSM \<Rightarrow> bool" where
  "unique_uid u = (size (fimage (\<lambda>(uid, _). uid) u) = size u)"

typedef iEFSM = "{A :: uEFSM. unique_uid A}"  morphisms iEFSM Abs_iEFSM
  apply (rule_tac x="{||}" in exI)
  by (simp add: unique_uid_def)*)

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

lemma state_nondeterminism_singleton[simp]: "state_nondeterminism a {|x|} = {||}"
  by (simp add: state_nondeterminism_def ffilter_def Set.filter_def)

definition S :: "iEFSM \<Rightarrow> nat fset" where
  "S m = (fimage (\<lambda>(uid, (s, s'), t). s) m) |\<union>| fimage (\<lambda>(uid, (s, s'), t). s') m"

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
  "replace_transition t uid from to orig new = (ffilter (\<lambda>x. snd x \<noteq> ((from, to), orig) \<and> snd x \<noteq> ((from, to), new)) t) |\<union>| {|(uid, (from, to), new)|}"

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

definition easy_merge :: "iEFSM \<Rightarrow> iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> iEFSM option" where
  "easy_merge oldEFSM newEFSM t1FromOld t2FromOld newFrom t1NewTo t2NewTo t1 u1 t2 u2 = (
    \<comment> \<open> If t1 directly subsumes t2 then replace t2 with t1 \<close>
    if directly_subsumes (tm oldEFSM) (tm newEFSM) t1FromOld t2 t1 then Some (replace_transition newEFSM u1 newFrom t2NewTo t1 t2) else
    \<comment> \<open> If t2 directly subsumes t1 then replace t1 with t2 \<close>
    if directly_subsumes (tm oldEFSM) (tm newEFSM) t2FromOld t1 t2 then Some (replace_transition newEFSM u1 newFrom t1NewTo t2 t1) else
    None
  )"

definition merge_transitions :: "iEFSM \<Rightarrow> iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> update_modifier \<Rightarrow> iEFSM option" where
  "merge_transitions oldEFSM newEFSM t1FromOld t2FromOld newFrom t1NewTo t2NewTo t1 u1 t2 u2 modifier = (
     case easy_merge oldEFSM newEFSM t1FromOld t2FromOld newFrom t1NewTo t2NewTo t1 u1 t2 u2 of
      Some x \<Rightarrow> Some x |
      \<comment> \<open> Can we modify the updates such that subsumption can occur? \<close>
      None \<Rightarrow> (
          (case modifier u1 u2 newFrom newEFSM oldEFSM of
            None \<Rightarrow> None |
            Some t' \<Rightarrow> Some t'
          )
      )
    )"

type_synonym scoreboard = "(nat \<times> (nat \<times> nat)) fset"
type_synonym strategy = "transition fset \<Rightarrow> transition fset \<Rightarrow> nat"

definition score :: "iEFSM \<Rightarrow> strategy \<Rightarrow> scoreboard" where
  "score t rank = ffilter (\<lambda>(score, _). score > 0) (fimage (\<lambda>(s1, s2). (rank (fimage (\<lambda>(_, t, _). t) (outgoing_transitions s1 t)) (fimage (\<lambda>(_, t, _). t) (outgoing_transitions s2 t)), (s1, s2))) (ffilter (\<lambda>(x, y). x < y) ((S t) |\<times>| (S t))))"

definition leaves :: "nat \<Rightarrow> iEFSM \<Rightarrow> nat" where
  "leaves uid t = fst (fst (snd (fthe_elem (ffilter (\<lambda>x. (\<exists>s. x = (uid, s))) t))))"

definition arrives :: "nat \<Rightarrow> iEFSM \<Rightarrow> nat" where
  "arrives uid t = snd (fst (snd (fthe_elem (ffilter (\<lambda>x. (\<exists>s. x = (uid, s))) t))))"

lemma exists_is_fst: "(\<lambda>x. (\<exists>s. x = (uid, s))) = (\<lambda>x. fst x = uid)"
  apply (rule ext)
  apply clarify
  by simp

inductive satisfies_trace :: "execution \<Rightarrow> transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> bool" where
  base: "satisfies_trace [] e s d" |
  step: "step e s d l i = Some (t, s', (map (\<lambda>x. Some x) p), d') \<Longrightarrow>
         satisfies_trace ex e s' d' \<Longrightarrow>
         satisfies_trace ((l, i, p)#ex) e s d"

definition satisfies :: "execution set \<Rightarrow> transition_matrix \<Rightarrow> bool" where
  "satisfies T e = (\<forall>t \<in> T. satisfies_trace t e 0 <>)"

function resolve_nondeterminism :: "nondeterministic_pair list \<Rightarrow> iEFSM \<Rightarrow> iEFSM  \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> iEFSM option" where
  "resolve_nondeterminism [] old new _ check = (if deterministic new \<and> check (tm new) then Some new else None)" |
  "resolve_nondeterminism (s#ss) oldEFSM newEFSM m check = (
      let (from, (to1, to2), ((t1, u1), (t2, u2))) = s;
          destMerge = (merge_states (arrives u1 newEFSM) (arrives u2 newEFSM) newEFSM)
      in 
      (case merge_transitions oldEFSM destMerge (leaves u1 oldEFSM) (leaves u2 oldEFSM) (leaves u1 destMerge) (arrives u1 destMerge) (arrives u2 destMerge) t1 u1 t2 u2 m of
        None \<Rightarrow> resolve_nondeterminism ss oldEFSM newEFSM m check |
        Some new \<Rightarrow> (let newScores = (rev (sorted_list_of_fset (nondeterministic_pairs new))) in 
                        (case resolve_nondeterminism newScores oldEFSM new m check of
                          Some new' \<Rightarrow> Some new' |
                          None \<Rightarrow> resolve_nondeterminism ss oldEFSM newEFSM m check
                        )
                    )
      )
  )"
  sorry
termination
sorry

(* resolve_nondeterminism: tries to resolve any nondeterminism in a given EFSM                    *)
(* @param n - The nondeterministic pairs of the form (origin, (dest1, dest2), t1, t2)             *)
(* @param e - The EFSM before states s1 and s2 were merged                                        *)
(* @param s1 - The state to be merged with s2                                                     *)
(* @param s2 - The state to be merged with s1                                                     *)
(* @param t - The nondeterministic EFSM arising from merging s1 with s2                           *)
(* @param g - A function which takes two transitions and generates one which subsumes them both   *)
(* @param m - A function which modifies the nondeterministic EFSM                                 *)
definition merge :: "iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> iEFSM option" where
"merge e s1 s2 m check = (if s1 = s2 then None else (let t' = (merge_states s1 s2 e) in
                         resolve_nondeterminism (rev (sorted_list_of_fset (nondeterministic_pairs t'))) e t' m check))"

fun inference_step :: "iEFSM \<Rightarrow> (nat \<times> nat \<times> nat) list \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> iEFSM option" where
  "inference_step _ [] _ _ = None" |
  "inference_step T ((s, s1, s2)#t) m check =
                                (if s > 0 then
                                   case merge T s1 s2 m check of
                                     Some new \<Rightarrow> Some new |
                                     None \<Rightarrow> inference_step T t m check
                                 else None)"

lemma inference_step_none: "inference_step e [] m check = None"
  by simp

function infer :: "iEFSM \<Rightarrow> strategy \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> iEFSM" where
  "infer t r m check = (case inference_step t (rev (sorted_list_of_fset (score t r))) m check of
                      None \<Rightarrow> t |
                      Some new \<Rightarrow> infer new r m check
                    )"
  by auto
termination
proof-
  show ?thesis
    apply standard
     apply auto[1]
    sorry
qed

primrec iterative_learn_aux :: "log \<Rightarrow> iEFSM \<Rightarrow> strategy \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> iEFSM" where
  "iterative_learn_aux [] e _ _ _ = e" |
  "iterative_learn_aux (h#t) e r m s = iterative_learn_aux t (infer (toiEFSM (make_branch (tm e) 0 <> h)) r m s) r m s"

definition iterative_learn :: "log \<Rightarrow> strategy \<Rightarrow> update_modifier \<Rightarrow> transition_matrix" where
  "iterative_learn l r m = tm (iterative_learn_aux l {||} r m (satisfies (set l)))"

definition learn :: "log \<Rightarrow> strategy \<Rightarrow> update_modifier \<Rightarrow> transition_matrix" where
  "learn l r m = tm (infer (toiEFSM (make_pta l {||})) r m (satisfies (set l)))"

definition uids :: "iEFSM \<Rightarrow> nat fset" where
  "uids e = fimage fst e"

lemma to_from_in_S_uid_in_uids: "(uid, (from, to), t) |\<in>| e \<Longrightarrow> to |\<in>| S e \<and> from |\<in>| S e \<and> uid |\<in>| uids e"
  apply (simp add: S_def uids_def)
  by force

end