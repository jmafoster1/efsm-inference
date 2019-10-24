subsection \<open>Extended Finite State Machine Inference\<close>
text\<open>
This theory sets out the key definitions for the inference of extended finite state machines from
system traces.
\<close>

theory Inference
  imports "../EFSM" "../Contexts" "../FSet_Utils" Transition_Ordering
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
type_synonym tids = "tid list"
type_synonym iEFSM = "(tids \<times> (cfstate \<times> cfstate) \<times> transition) fset"

definition get_by_id :: "iEFSM \<Rightarrow> tid \<Rightarrow> transition" where
  "get_by_id e uid = (snd \<circ> snd) (fthe_elem (ffilter (\<lambda>(tids, _). uid \<in> set tids) e))"

definition get_by_ids :: "iEFSM \<Rightarrow> tids \<Rightarrow> transition" where
  "get_by_ids e uid = (snd \<circ> snd) (fthe_elem (ffilter (\<lambda>(tids, _). set uid \<subseteq> set tids) e))"

definition uids :: "iEFSM \<Rightarrow> nat fset" where
  "uids e = ffUnion (fimage (fset_of_list \<circ> fst) e)"

definition max_uid :: "iEFSM \<Rightarrow> nat option" where
  "max_uid e = (let uids = uids e in if uids = {||} then None else Some (fMax uids))"

(*
definition toiEFSM :: "transition_matrix \<Rightarrow> iEFSM" where
  "toiEFSM e = (let
    e_list = (sorted_list_of_fset e) in
    fold (\<lambda>(uid, tuple) iefsm. iefsm(uid $:= Some tuple)) (enumerate 0 e_list) <>
  )"
*)

definition tm :: "iEFSM \<Rightarrow> transition_matrix" where
  "tm e = fimage snd e"

definition merge_states_aux :: "nat \<Rightarrow> nat \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "merge_states_aux s1 s2 e = fimage (\<lambda>(uid, (origin, dest), t). (uid, (if origin = s1 then s2 else origin , if dest = s1 then s2 else dest), t)) e"

definition merge_states :: "nat \<Rightarrow> nat \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "merge_states x y t = (if x > y then merge_states_aux x y t else merge_states_aux y x t)"

lemma finfun_update_get: "f(a $:= b) $ c = (if c = a then b else f $ c)"
  by simp

lemma merge_states_symmetry: "merge_states x y t = merge_states y x t"
  by (simp add: merge_states_def)

(* declare[[show_types,show_sorts]] *)

definition outgoing_transitions :: "cfstate \<Rightarrow> iEFSM \<Rightarrow> (cfstate \<times> transition \<times> tids) fset" where
  "outgoing_transitions s e = fimage (\<lambda>(uid, (from, to), t'). (to, t', uid)) ((ffilter (\<lambda>(uid, (origin, dest), t). origin = s)) e)"

\<comment> \<open>Tuples of the form (cfstate \<times> (cfstate \<times> cfstate) \<times> ((transition \<times> tids) \<times> (transition \<times> tids)))\<close>
type_synonym nondeterministic_pair = "(cfstate \<times> (cfstate \<times> cfstate) \<times> ((transition \<times> tids) \<times> (transition \<times> tids)))"

definition state_nondeterminism :: "nat \<Rightarrow> (cfstate \<times> transition \<times> tids) fset \<Rightarrow> nondeterministic_pair fset" where
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

definition nondeterministic_pairs_labar_dest :: "iEFSM \<Rightarrow> nondeterministic_pair fset" where
  "nondeterministic_pairs_labar_dest t = ffilter
     (\<lambda>(_, (d, d'), (t, _), (t', _)).
      Label t = Label t' \<and> Arity t = Arity t' \<and> (choice t t' \<or> (Outputs t = Outputs t' \<and> d = d')))
     (ffUnion (fimage (\<lambda>s. state_nondeterminism s (outgoing_transitions s t)) (S t)))"

definition nondeterministic_pairs_labar :: "iEFSM \<Rightarrow> nondeterministic_pair fset" where
  "nondeterministic_pairs_labar t = ffilter
     (\<lambda>(_, (d, d'), (t, _), (t', _)).
      Label t = Label t' \<and> Arity t = Arity t' \<and> (choice t t' \<or> Outputs t = Outputs t'))
     (ffUnion (fimage (\<lambda>s. state_nondeterminism s (outgoing_transitions s t)) (S t)))"

definition deterministic :: "iEFSM \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> bool" where
  "deterministic t np = (np t = {||})"

definition nondeterministic :: "iEFSM \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> bool" where
  "nondeterministic t np = (\<not> deterministic t np)"

definition replace_transition :: "iEFSM \<Rightarrow> tids \<Rightarrow> transition \<Rightarrow> iEFSM" where
  "replace_transition e uid new = (fimage (\<lambda>(uids, (from, to), t). if set uid \<subseteq> set uids then (uids, (from, to), new) else (uids, (from, to), t)) e)"

definition replace_transitions :: "iEFSM \<Rightarrow> (tids \<times> transition) list \<Rightarrow> iEFSM" where
  "replace_transitions e ts = fold (\<lambda>(uid, new) acc. replace_transition acc uid new) ts e"

primrec make_guard :: "value list \<Rightarrow> nat \<Rightarrow> gexp list" where
"make_guard [] _ = []" |
"make_guard (h#t) n = (gexp.Eq (V (vname.I n)) (L h))#(make_guard t (n+1))"

primrec make_outputs :: "value list \<Rightarrow> output_function list" where
  "make_outputs [] = []" |
  "make_outputs (h#t) = (L h)#(make_outputs t)"

(* An execution represents a run of the software and has the form [(label, inputs, outputs)]*)
type_synonym execution = "(label \<times> value list \<times> value list) list"
type_synonym log = "execution list"

definition max_uid_total :: "iEFSM \<Rightarrow> nat" where
  "max_uid_total e = (case max_uid e of None \<Rightarrow> 0 | Some u \<Rightarrow> u)"

definition add_transition :: "iEFSM \<Rightarrow> cfstate \<Rightarrow> label \<Rightarrow> value list \<Rightarrow> value list \<Rightarrow> iEFSM" where
  "add_transition e s label inputs outputs = finsert ([max_uid_total e + 1], (s, (maxS (tm e))+1), \<lparr>Label=label, Arity=length inputs, Guard=(make_guard inputs 0), Outputs=(make_outputs outputs), Updates=[]\<rparr>) e"

definition startsWith :: "String.literal \<Rightarrow> String.literal \<Rightarrow> bool" where
  "startsWith string start = (\<exists>s'. string = start + s')"

definition endsWith :: "String.literal \<Rightarrow> String.literal \<Rightarrow> bool" where
  "endsWith string end = (\<exists>s'. string = s' + end)"

definition dropRight :: "String.literal \<Rightarrow> nat \<Rightarrow> String.literal" where
  "dropRight l n = String.implode (rev (drop n (rev (String.explode l))))"

fun nat_of_char :: "char \<Rightarrow> nat" where
  "nat_of_char CHR ''0'' = 0" |
  "nat_of_char CHR ''1'' = 1" |
  "nat_of_char CHR ''2'' = 2" |
  "nat_of_char CHR ''3'' = 3" |
  "nat_of_char CHR ''4'' = 4" |
  "nat_of_char CHR ''5'' = 5" |
  "nat_of_char CHR ''6'' = 6" |
  "nat_of_char CHR ''7'' = 7" |
  "nat_of_char CHR ''8'' = 8" |
  "nat_of_char CHR ''9'' = 9"

definition parseNat :: "string \<Rightarrow> nat" where
  "parseNat s = (let
    nats = map nat_of_char s;
    zipped = enumerate 0 (rev nats) in
    fold (\<lambda>(index, value) total. total + (value * (10 ^ index))) zipped 0
  )"

definition parseInt :: "String.literal \<Rightarrow> int" where
  "parseInt s = (if startsWith s STR ''-'' then -(int (parseNat (String.explode s))) else int (parseNat (String.explode s)))"

definition substring :: "String.literal \<Rightarrow> nat \<Rightarrow> String.literal" where
  "substring s n = String.implode (drop n (String.explode s))"

primrec make_guard_abstract :: "value list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (String.literal \<Rightarrow>f nat option) \<Rightarrow> gexp list \<Rightarrow> update_function list \<Rightarrow> (gexp list \<times> update_function list \<times> (String.literal \<Rightarrow>f nat option))" where
  "make_guard_abstract [] _ _ r G U = (G, U, r)" |
  "make_guard_abstract (h#t) i maxR r G U = (
    case h of
      value.Num _ \<Rightarrow> make_guard_abstract t (i+1) maxR r ((Eq (V (vname.I i)) (L h))#G) U |
      value.Str s \<Rightarrow>
        if s = STR ''_'' then
          make_guard_abstract t (i+1) maxR r G U
        else if startsWith s STR ''$'' then
          case r $ s of
            None \<Rightarrow> make_guard_abstract t (i+1) (maxR + 1) (r(s := maxR)) G ((maxR, V (I i))#U) |
            Some reg \<Rightarrow> make_guard_abstract t (i+1) maxR r ((Eq (V (vname.I i)) (V (R reg)))#G) U
        else if startsWith s STR ''<'' then
          if startsWith (substring s 1) STR ''$'' then
            case r $ (substring s 1) of
              Some reg \<Rightarrow> make_guard_abstract t (i+1) maxR r ((Gt (V (vname.I i)) (V (R reg)))#G) U
          else
            make_guard_abstract t (i+1) maxR r ((Gt (V (vname.I i)) (L (Num (parseInt (substring s 2)))))#G) U
        else if startsWith s STR ''/='' then
          if startsWith (substring s 1) STR ''$'' then
            case r $ (substring s 2) of
              Some reg \<Rightarrow> make_guard_abstract t (i+1) maxR r ((Gt (V (vname.I i)) (V (R reg)))#G) U
          else
            make_guard_abstract t (i+1) maxR r ((Gt (V (vname.I i)) (L (Num (parseInt (substring s 3)))))#G) U
        else
          make_guard_abstract t (i+1) maxR r ((Eq (V (vname.I i)) (L h))#G) U
  )"

primrec make_outputs_abstract :: "value list \<Rightarrow> nat \<Rightarrow> (String.literal \<Rightarrow>f nat option) \<Rightarrow> output_function list \<Rightarrow> output_function list" where
  "make_outputs_abstract []_ _ P = rev P" |
  "make_outputs_abstract (h#t) maxR r P = (case h of
    value.Num _ \<Rightarrow> make_outputs_abstract t maxR r ((L h)#P) |
    value.Str s \<Rightarrow>
      if startsWith s STR ''$'' then 
        case r $ s of
          Some reg \<Rightarrow> make_outputs_abstract t maxR r ((V (R reg))#P)
      else
        make_outputs_abstract t maxR r ((L h)#P)
    )"

definition add_transition_abstract :: "iEFSM \<Rightarrow> (String.literal \<Rightarrow>f nat option) \<Rightarrow> cfstate \<Rightarrow> label \<Rightarrow> value list \<Rightarrow> value list \<Rightarrow> (iEFSM \<times> (String.literal \<Rightarrow>f nat option))" where
  "add_transition_abstract e r s label inputs outputs = (let
    regs = fimage (total_max_reg \<circ> snd) (tm e);
    maxR = (if regs = {||} then 1 else fMax regs);
    (G, U1, r') = make_guard_abstract inputs 0 maxR r [] [];
    P = make_outputs_abstract outputs maxR r' [] in
    if endsWith label STR ''*'' then
      (finsert ([max_uid_total e + 1], (s, s), \<lparr>Label=dropRight label 1, Arity=length inputs, Guard=G, Outputs=P, Updates=U1\<rparr>) e, r')
    else
      (finsert ([max_uid_total e + 1], (s, (maxS (tm e))+1), \<lparr>Label=label, Arity=length inputs, Guard=G, Outputs=P, Updates=U1\<rparr>) e, r')
    )"

fun make_branch :: "iEFSM \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> iEFSM" where
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

fun make_branch_abstract :: "(iEFSM \<times> (String.literal \<Rightarrow>f nat option)) \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> iEFSM" where
  "make_branch_abstract (e, r) _ _ [] = e" |
  "make_branch_abstract (e, r1) s r ((label, inputs, outputs)#t) =
    (case (step (tm e) s r label inputs) of
      Some (transition, s', outputs', updated) \<Rightarrow> 
        if outputs' = (map Some outputs) then
          make_branch_abstract (e, r1) s' updated t
        else 
          make_branch_abstract (add_transition_abstract e r1 s label inputs outputs) ((maxS (tm e))+1) r t  |
      None \<Rightarrow>
          make_branch_abstract (add_transition_abstract e r1 s label inputs outputs) ((maxS (tm e))+1) r t
    )"

primrec make_pta :: "log \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "make_pta [] e = e" |
  "make_pta (h#t) e = make_pta t (make_branch e 0 <> h)"

definition make_pta_abstract :: "log \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "make_pta_abstract l e = fold (\<lambda>h e. make_branch_abstract (e, <>) 0 <> h) l e"

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

type_synonym update_modifier = "tids \<Rightarrow> tids \<Rightarrow> cfstate \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM option"

definition null_modifier :: update_modifier where
  "null_modifier _ _ _ _ _ _ = None"

type_synonym score = nat
type_synonym scoreboard = "(score \<times> (cfstate \<times> cfstate)) fset"
type_synonym strategy = "tids \<Rightarrow> tids \<Rightarrow> iEFSM \<Rightarrow> nat"

primrec k_outgoing :: "nat \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> (cfstate \<times> transition \<times> tids) fset" where
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
       \<comment> \<open>if outgoing_s1 = {||} \<and> outgoing_s2 = {||} then (s1, s2, 1) else\<close> (fSum scores, s1, s2 )
     ) pairs_to_score in
     ffilter (\<lambda>(score, _). score > 0) scores)"

definition origin :: "tids \<Rightarrow> iEFSM \<Rightarrow> nat" where
  "origin uid t = fst (fst (snd (fthe_elem (ffilter (\<lambda>x. set uid \<subseteq> set (fst x)) t))))"

definition dest :: "tids \<Rightarrow> iEFSM \<Rightarrow> nat" where
  "dest uid t = snd (fst (snd (fthe_elem (ffilter (\<lambda>x. set uid \<subseteq> set (fst x)) t))))"

inductive satisfies_trace :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> bool" where
  base: "satisfies_trace e s d []" |                                         
  step: "\<exists>(s', T) |\<in>| possible_steps e s d l i.
         apply_outputs (Outputs T) (join_ir i d) = (map Some p) \<and>
         satisfies_trace e s' (apply_updates (Updates T) (join_ir i d) d) t \<Longrightarrow>
         satisfies_trace e s d ((l, i, p)#t)"

lemma satisfies_trace_step: "satisfies_trace e s d ((l, i, p)#t) = (\<exists>(s', T) |\<in>| possible_steps e s d l i.
         apply_outputs (Outputs T) (join_ir i d) = (map Some p) \<and>
         satisfies_trace e s' (apply_updates (Updates T) (join_ir i d) d) t)"
  apply standard
   defer
   apply (simp add: satisfies_trace.step)
  apply (rule satisfies_trace.cases)
  by auto

fun satisfies_trace_prim :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> bool" where
  "satisfies_trace_prim _ _ _ [] = True" |
  "satisfies_trace_prim e s d ((l, i, p)#t) = (
    let poss_steps = possible_steps e s d l i in
    if fis_singleton poss_steps then
      let (s', T) = fthe_elem poss_steps in
      if apply_outputs (Outputs T) (join_ir i d) = (map Some p) then
        satisfies_trace_prim e s' (apply_updates (Updates T) (join_ir i d) d) t
      else False
    else
      (\<exists>(s', T) |\<in>| poss_steps.
         apply_outputs (Outputs T) (join_ir i d) = (map Some p) \<and>
         satisfies_trace_prim e s' (apply_updates (Updates T) (join_ir i d) d) t))"

lemma satisfies_trace_prim: "\<forall>s d. satisfies_trace e s d l = satisfies_trace_prim e s d l"
proof(induct l)
case Nil
  then show ?case
    by (simp add: satisfies_trace.base)
next
case (Cons a l)
  then show ?case
    apply (cases a)
    apply (simp add: satisfies_trace_step Let_def fis_singleton_alt)
    by auto
qed

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

definition insert_transition :: "tids \<Rightarrow> cfstate \<Rightarrow> cfstate \<Rightarrow> transition \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "insert_transition uid from to t e = (
    if \<nexists>(uid, (from', to'), t') |\<in>| e. from = from' \<and> to = to' \<and> t = t' then
      finsert (uid, (from, to), t) e
    else
      fimage (\<lambda>(uid', (from', to'), t').
        if from = from' \<and> to = to' \<and> t = t' then
          (uid'@uid, (from', to'), t')
        else
          (uid', (from', to'), t')
      ) e
  )"

definition make_distinct :: "iEFSM \<Rightarrow> iEFSM" where
  "make_distinct e = fold (\<lambda>(uid, (from, to), t) acc. insert_transition uid from to t acc) (sorted_list_of_fset e) {||}"

\<comment> \<open>When we replace one transition with another, we need to merge their uids to keep track of which\<close>
\<comment> \<open>transition accounts for which event in the original traces                                     \<close>
definition merge_transitions_aux :: "iEFSM \<Rightarrow> tids \<Rightarrow> tids \<Rightarrow> iEFSM" where
  "merge_transitions_aux e oldID newID = (let
    (uids1, (origin, dest), old) = fthe_elem (ffilter (\<lambda>(uids, _). oldID = uids) e);
    (uids2, (origin, dest), new) = fthe_elem (ffilter (\<lambda>(uids, _). newID = uids) e) in
    make_distinct (finsert (List.union uids1 uids2, (origin, dest), new) (e - {|(uids1, (origin, dest), old), (uids2, (origin, dest), new)|}))
  )"

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
definition merge_transitions :: "iEFSM \<Rightarrow> iEFSM \<Rightarrow> transition \<Rightarrow> tids \<Rightarrow> transition \<Rightarrow> tids \<Rightarrow> update_modifier \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM option" where
  "merge_transitions oldEFSM destMerge t\<^sub>1 u\<^sub>1 t\<^sub>2 u\<^sub>2 modifier np = (
     if \<forall>id \<in> set u\<^sub>1. directly_subsumes oldEFSM destMerge (origin [id] oldEFSM) (origin u\<^sub>1 destMerge) t\<^sub>2 t\<^sub>1 then
       \<comment> \<open>Replace t1 with t2\<close>
       Some (merge_transitions_aux destMerge u\<^sub>1 u\<^sub>2)
     else if \<forall>id \<in> set u\<^sub>2. directly_subsumes oldEFSM destMerge (origin [id] oldEFSM) (origin u\<^sub>2 destMerge) t\<^sub>1 t\<^sub>2 then
       \<comment> \<open>Replace t2 with t1\<close>
       Some (merge_transitions_aux destMerge u\<^sub>2 u\<^sub>1)
     else
        case modifier u\<^sub>1 u\<^sub>2 (origin u\<^sub>1 destMerge) destMerge oldEFSM np of
          None \<Rightarrow> None |
          Some e \<Rightarrow> Some (make_distinct e)
   )"

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
function resolve_nondeterminism :: "(cfstate \<times> cfstate) list \<Rightarrow> nondeterministic_pair list \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM option" where
  "resolve_nondeterminism _ [] _ new _ check np = (if deterministic new np \<and> check (tm new) then Some new else None)" |
  "resolve_nondeterminism closed ((from, (dest\<^sub>1, dest\<^sub>2), ((t\<^sub>1, u\<^sub>1), (t\<^sub>2, u\<^sub>2)))#ss) oldEFSM newEFSM m check np = (
     if (dest\<^sub>1, dest\<^sub>2) \<in> set closed then None else let
     destMerge = if dest\<^sub>1 = dest\<^sub>2 then newEFSM else merge_states dest\<^sub>1 dest\<^sub>2 newEFSM
     in
     case merge_transitions oldEFSM destMerge t\<^sub>1 u\<^sub>1 t\<^sub>2 u\<^sub>2 m np of
       None \<Rightarrow> resolve_nondeterminism ((dest\<^sub>1, dest\<^sub>2)#closed) ss oldEFSM newEFSM m check np |
       Some new \<Rightarrow>
         let newScores = (sorted_list_of_fset (np new)) in 
         if length (newScores) + size new + size (S new) < length (ss) + 1 + size newEFSM + size (S newEFSM) then
           case resolve_nondeterminism closed newScores oldEFSM new m check np of
             Some new' \<Rightarrow> Some new' |
             None \<Rightarrow> resolve_nondeterminism ((dest\<^sub>1, dest\<^sub>2)#closed) ss oldEFSM newEFSM m check np
         else
          None
   )"
     apply clarify
     apply simp
     apply (metis neq_Nil_conv prod_cases3 surj_pair)
  by auto
termination
  by (relation "measures [\<lambda>(_, ss, _, newEFSM, _). length ss + size newEFSM + size (S newEFSM)]", auto)

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
      let e' = make_distinct (merge_states s\<^sub>1 s\<^sub>2 e) in
      resolve_nondeterminism [] (sorted_list_of_fset (np e')) e e' m check np 
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

definition learn :: "nat \<Rightarrow> iEFSM \<Rightarrow> log \<Rightarrow> strategy \<Rightarrow> update_modifier \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM" where
  "learn n pta l r m np = (
     let check = satisfies (set l) in
         (infer n pta r m check np)
   )"

definition max_reg :: "iEFSM \<Rightarrow> nat option" where
  "max_reg e = EFSM.max_reg (tm e)"

definition "max_reg_total e = (case max_reg e of None \<Rightarrow> 0 | Some r \<Rightarrow> r)"

lemma fMax_None: "f \<noteq> {||} \<Longrightarrow> fMax f = None = (\<forall>x |\<in>| f. x = None)"
  apply standard
  using fMax_ge x_leq_None apply fastforce
  by (meson fBallE fMax_in)

definition max_output :: "iEFSM \<Rightarrow> nat" where
  "max_output e = EFSM.max_output (tm e)"

primrec try_heuristics :: "update_modifier list \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> update_modifier" where
  "try_heuristics [] _ = null_modifier" |
  "try_heuristics (h#t) np = (\<lambda>a b c d e np. case h a b c d e np of Some e' \<Rightarrow> Some e' | None \<Rightarrow> (try_heuristics t np) a b c d e np)"

primrec try_heuristics_check :: "(transition_matrix \<Rightarrow> bool) \<Rightarrow> update_modifier list \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> update_modifier" where
  "try_heuristics_check _ [] _ = null_modifier" |
  "try_heuristics_check check (h#t) np = (\<lambda>a b c d e np. 
    case h a b c d e np of
      Some e' \<Rightarrow>
        if check (tm e') then Some e' else (try_heuristics_check check t np) a b c d e np |
      None \<Rightarrow> (try_heuristics_check check t np) a b c d e np
    )"

definition all_regs :: "iEFSM \<Rightarrow> nat set" where
  "all_regs e = EFSM.all_regs (tm e)"

fun fold_into :: "nat \<Rightarrow> gexp list \<Rightarrow> gexp list" where
  "fold_into n [] = [gNot (Null (V (I n)))]" |
  "fold_into n ((Eq (V (I i)) (L l))#t) = (if i = n then (Eq (V (I i)) (L l))#t else (Eq (V (I i)) (L l))#(fold_into n t))" |
  "fold_into n ((In (I i) l)#t) = (if i = n then (In (I i) l)#t else (In (I i) l)#(fold_into n t))" |
  "fold_into n (h#t) = h#(fold_into n t)"

primrec smart_not_null :: "nat list \<Rightarrow> gexp list \<Rightarrow> gexp list" where
  "smart_not_null [] g = g" |
  "smart_not_null (h#t) g = fold_into h (smart_not_null t g)"

lemma fold_into_supset: "set (fold_into a g) \<supseteq> set g"
  by(induct g rule: fold_into.induct, auto)

lemma fold_into_gNot_or_not: "fold_into a g = g \<or> fold_into a g = g@[(gNot (Null (V (I a))))]"
proof(induct g)
  case Nil
  then show ?case
    by simp
next
  case (Cons a g)
  then show ?case
    apply (cases a)
         apply simp+
        apply (case_tac x21)
           apply simp
          apply (case_tac x22)
             apply simp
             apply (metis Cons.hyps fold_into.simps(1) fold_into.simps(2) fold_into.simps(6) vname.exhaust)
            apply simp+
     apply (case_tac x51)
    by auto
qed

lemma smart_not_null_superset: "set (smart_not_null l g) \<supseteq> set g"
proof(induct l)
  case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
    apply simp
    using fold_into_supset by blast
qed

lemma fold_into_not_null: "apply_guards (fold_into a g) s \<Longrightarrow> gval (gNot (Null (V (I a)))) s = true"
  apply (insert fold_into_gNot_or_not[of a g])
  apply (case_tac "fold_into a g = g @ [gNot (Null (V (I a)))]")
   apply (simp add: apply_guards_singleton apply_guards_append)
  apply simp
  apply (induct g)
   apply simp
   apply (simp add: apply_guards_cons)
  apply (case_tac aa)
       apply simp
      apply (case_tac x21)
         apply simp
        apply (case_tac x22)
           apply simp
           apply (case_tac "x2")
            apply simp
            apply (case_tac "x1a = a")
             apply simp
             apply (metis trilean.distinct(1))
            apply simp+
   apply (case_tac x51)
    apply simp
    apply (metis imageE list.inject trilean.distinct(1))
  by auto

lemma apply_guards_snn_map_gNot:
  "apply_guards (smart_not_null l g) s \<Longrightarrow> apply_guards (g @ map (\<lambda>i. gNot (Null (V (I i)))) l) s"
proof(induct l)
  case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
    apply (simp add: apply_guards_append apply_guards_cons del: gval.simps)
    apply standard
     apply (metis smart_not_null_superset apply_guards_subset smart_not_null.simps(2))
    apply standard
    using fold_into_not_null apply blast
    using apply_guards_subset fold_into_supset by blast
qed

lemma apply_guards_snn: "apply_guards (smart_not_null [0..<a] g) s \<Longrightarrow> apply_guards (g @ ensure_not_null a) s"
  by (simp only: ensure_not_null_def apply_guards_snn_map_gNot)

lemma satisfiable_list_snn: "satisfiable_list (smart_not_null [0..<a] g) \<Longrightarrow> satisfiable_list (g @ ensure_not_null a)"
  apply (simp add: satisfiable_list_def satisfiable_def apply_guards_fold[symmetric] del: fold_append)
  using apply_guards_snn by blast

definition simple_mutex :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "simple_mutex t t' = (
     Label t = Label t' \<and>
     Arity t = Arity t' \<and>
     max_reg_list (Guard t) = None \<and>
     max_input_list (Guard t) < Some (Arity t) \<and>
     satisfiable_list (smart_not_null [0..<(Arity t)] (Guard t)) \<and>
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
  by (metis satisfiable_list_snn can_take_satisfiable no_choice_no_subsumption)

definition max_int :: "iEFSM \<Rightarrow> int" where
  "max_int e = EFSM.max_int (tm e)"

fun literal_args :: "gexp \<Rightarrow> bool" where
  "literal_args (Bc v) = False" |
  "literal_args (Eq (V _) (L _)) = True" |
  "literal_args (In _ _) = True" |
  "literal_args (Eq _ _) = False" |
  "literal_args (Lt va v) = False" |
  "literal_args (Null v) = False" |
  "literal_args (Nor v va) = (literal_args v \<and> literal_args va)"

lemma literal_args_eq: "literal_args (Eq a b) \<Longrightarrow> \<exists>v l. a = (V v) \<and> b = (L l)"
  apply (cases a)
     apply simp
    apply (cases b)
  by auto

definition i_possible_steps :: "iEFSM \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (tids \<times> cfstate \<times> transition) fset" where
  "i_possible_steps e s r l i = fimage (\<lambda>(uid, (origin, dest), t). (uid, dest, t))
  (ffilter (\<lambda>(uid, (origin, dest::nat), t::transition).
      origin = s
      \<and> (Label t) = l
      \<and> (length i) = (Arity t)
      \<and> apply_guards (Guard t) (join_ir i r)
     ) 
    e)"

end
