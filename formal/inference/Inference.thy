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
  "state_nondeterminism origin nt = fimage (\<lambda>x. let (origin, (d1, d2), t, t') = x in if d1 > d2 then (origin, (d2, d1), t', t) else x) (if size nt < 2 then {||} else ffUnion (fimage (\<lambda>x. let (dest, t) = x in fimage (\<lambda>y. let (dest', t') = y in (origin, (dest, dest'), (t, t'))) (nt - {|x|})) nt))"

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

definition nondeterminism :: "iEFSM \<Rightarrow> bool" where
  "nondeterminism t = (nondeterministic_pairs t \<noteq> {||})"

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

fun make_branch :: "transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> (char list \<times> value list \<times> value list) list \<Rightarrow> transition_matrix" where
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

type_synonym generator_function = "iEFSM \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> transition option"

definition null_generator :: generator_function where
  "null_generator a b c d e = None"

type_synonym update_modifier = "transition \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> (iEFSM \<times> (nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> nat)) option"

definition null_modifier :: update_modifier where
  "null_modifier a b c d e = None"

definition easy_merge :: "iEFSM \<Rightarrow> iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> generator_function \<Rightarrow> iEFSM option" where
  "easy_merge oldEFSM newEFSM t1FromOld t2FromOld newFrom t1NewTo t2NewTo t1 u1 t2 u2 maker = (
    \<comment> \<open> If t1 directly subsumes t2 then replace t2 with t1 \<close>
    if directly_subsumes (tm oldEFSM) (tm newEFSM) t1FromOld t2 t1 then Some (replace_transition newEFSM u1 newFrom t2NewTo t1 t2) else
    \<comment> \<open> If t2 directly subsumes t1 then replace t1 with t2 \<close>
    if directly_subsumes (tm oldEFSM) (tm newEFSM) t2FromOld t1 t2 then Some (replace_transition newEFSM u1 newFrom t1NewTo t2 t1) else
    \<comment> \<open> Can we make a transition which subsumes both? \<close>
    (case maker oldEFSM t1FromOld t1 t2FromOld t2 of
    Some t' \<Rightarrow>
    if directly_subsumes (tm oldEFSM) (tm newEFSM) t1FromOld t1 t' \<and> directly_subsumes (tm oldEFSM) (tm newEFSM) t2FromOld t2 t' then
       Some (replace_transition (replace_transition newEFSM ((maxUID newEFSM) + 1) newFrom t2NewTo t2 t') ((maxUID newEFSM) + 2) newFrom t1NewTo t1 t') else
    None |
    None \<Rightarrow> None)
  )"

definition merge_transitions :: "iEFSM \<Rightarrow> iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> generator_function \<Rightarrow> update_modifier \<Rightarrow> bool \<Rightarrow> iEFSM option" where
  "merge_transitions oldEFSM newEFSM t1FromOld t2FromOld newFrom t1NewTo t2NewTo t1 u1 t2 u2 maker modifier modify = (
     case easy_merge oldEFSM newEFSM t1FromOld t2FromOld newFrom t1NewTo t2NewTo t1 u1 t2 u2 maker of
      Some x \<Rightarrow> Some x |
      \<comment> \<open> Can we modify the updates such that subsumption can occur? \<close>
      None \<Rightarrow> (
        if modify then
          (case modifier t1 t2 newFrom newEFSM oldEFSM of
            None \<Rightarrow> None |
            Some (t', H\<^sub>n\<^sub>e\<^sub>w, H\<^sub>o\<^sub>l\<^sub>d) \<Rightarrow> (
              if nondeterministic_simulates (tm t') (tm oldEFSM) H\<^sub>o\<^sub>l\<^sub>d then
                Some t'
              else None
            )
          )
        else None
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

lemma[code]: "leaves uid t = fst (fst (snd (fthe_elem (ffilter (\<lambda>x. (fst x = uid)) t))))"
  by (simp only: leaves_def exists_is_fst)

lemma[code]: "arrives uid t = snd (fst (snd (fthe_elem (ffilter (\<lambda>x. (fst x = uid)) t))))"
  by (simp only: arrives_def exists_is_fst)

lemma "(leaves uid t = n) = (\<exists>b ba. Set.filter (\<lambda>x. \<exists>a b ba. x = (uid, (a, b), ba)) (fset t) = {(uid, (n, b), ba)})"
  apply (simp add: leaves_def ffilter_def fthe_elem_def Abs_fset_inverse)
  apply standard
   apply (rule_tac x="snd (fst (snd (the_elem (Set.filter (\<lambda>x. \<exists>a b ba. x = (uid, (a, b), ba)) (fset t)))))" in exI)
   apply (rule_tac x="snd (snd (the_elem (Set.filter (\<lambda>x. \<exists>a b ba. x = (uid, (a, b), ba)) (fset t))))" in exI)
   apply (simp add: Set.filter_def)
   apply clarify
   apply simp
  oops

function resolve_nondeterminism :: "nondeterministic_pair fset \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> generator_function \<Rightarrow> update_modifier \<Rightarrow> iEFSM option" where
  "resolve_nondeterminism s e t g m = (
    if s = {||} then
      if nondeterminism t then None else Some t
    else 
      let (from, (to1, to2), ((t1, u1), (t2, u2))) = fMax s;
          t' = merge_states to1 to2 t;
          z = (merge_states (arrives u1 t) (arrives u2 t) t)
      in 
      \<comment> \<open>   merge_transitions oldEFSM newEFSM t1FromOld     t2FromOld    newFrom t1NewTo t2NewTo t1 u1 t2 u2 maker modifier modify\<close>
      (case merge_transitions  e       z      (leaves u1 e) (leaves u2 e) (leaves u1 z)    (arrives u1 z) (arrives u2 z)     t1 u1 t2 u2 g     m        True of
      None \<Rightarrow> resolve_nondeterminism (s - {|fMax s|}) e t g m |
      Some new \<Rightarrow> resolve_nondeterminism (nondeterministic_pairs new) e new g m
      )
  )"
sorry
termination sorry

(* resolve_nondeterminism: tries to resolve any nondeterminism in a given EFSM                    *)
(* @param n - The nondeterministic pairs of the form (origin, (dest1, dest2), t1, t2)             *)
(* @param e - The EFSM before states s1 and s2 were merged                                        *)
(* @param s1 - The state to be merged with s2                                                     *)
(* @param s2 - The state to be merged with s1                                                     *)
(* @param t - The nondeterministic EFSM arising from merging s1 with s2                           *)
(* @param g - A function which takes two transitions and generates one which subsumes them both   *)
(* @param m - A function which modifies the nondeterministic EFSM                                 *)
definition merge :: "iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> generator_function \<Rightarrow> update_modifier \<Rightarrow> iEFSM option" where
"merge e s1 s2 g m = (if s1 = s2 then Some (e) else (let t' = (merge_states s1 s2 e) in
                       \<comment> \<open> Have we got any nondeterminism? \<close>
                       (if \<not> nondeterminism t' then
                         \<comment> \<open> If not then we're good to go \<close>
                         Some t' else
                         \<comment> \<open> If we have then we need to fix it \<close>
                         resolve_nondeterminism (nondeterministic_pairs t') e t' g m)))"

(* export_code resolve_nondeterminism in "Scala" *)

fun inference_step :: "iEFSM \<Rightarrow> (nat \<times> nat \<times> nat) list \<Rightarrow> generator_function \<Rightarrow> update_modifier \<Rightarrow> iEFSM option" where
  "inference_step _ [] _ _ = None" |
  "inference_step T ((s, s1, s2)#t) g m =
                                (if s > 0 then
                                   case merge T s1 s2 g m of
                                     Some new \<Rightarrow> Some new |
                                     None \<Rightarrow> inference_step T t g m
                                 else None)"

function infer :: "iEFSM \<Rightarrow> strategy \<Rightarrow> generator_function \<Rightarrow> update_modifier \<Rightarrow> iEFSM" where
  "infer t r g m = (case inference_step t (rev (sorted_list_of_fset (score t r))) g m of None \<Rightarrow> t | Some new \<Rightarrow> infer new r g m)"
  by auto
termination
proof-
  show ?thesis
    apply standard
     apply auto[1]
    sorry
qed

definition learn :: "log \<Rightarrow> strategy \<Rightarrow> generator_function \<Rightarrow> update_modifier \<Rightarrow> transition_matrix" where
  "learn l r g m = tm (infer (toiEFSM (make_pta l {||})) r g m)"

end