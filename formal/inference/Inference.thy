subsection \<open>Extended Finite State Machine Inference\<close>
text\<open>
This theory sets out the key definitions for the inference of extended finite state machines from
system traces.
\<close>

theory Inference
  imports "EFSM.Contexts"
    "EFSM.Transition_Lexorder"
    "HOL-Library.Product_Lexorder"
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

definition origin :: "tids \<Rightarrow> iEFSM \<Rightarrow> nat" where
  "origin uid t = fst (fst (snd (fthe_elem (ffilter (\<lambda>x. set uid \<subseteq> set (fst x)) t))))"

definition dest :: "tids \<Rightarrow> iEFSM \<Rightarrow> nat" where
  "dest uid t = snd (fst (snd (fthe_elem (ffilter (\<lambda>x. set uid \<subseteq> set (fst x)) t))))"

definition get_by_id :: "iEFSM \<Rightarrow> tid \<Rightarrow> transition" where
  "get_by_id e uid = (snd \<circ> snd) (fthe_elem (ffilter (\<lambda>(tids, _). uid \<in> set tids) e))"

definition get_by_ids :: "iEFSM \<Rightarrow> tids \<Rightarrow> transition" where
  "get_by_ids e uid = (snd \<circ> snd) (fthe_elem (ffilter (\<lambda>(tids, _). set uid \<subseteq> set tids) e))"

definition uids :: "iEFSM \<Rightarrow> nat fset" where
  "uids e = ffUnion (fimage (fset_of_list \<circ> fst) e)"

definition max_uid :: "iEFSM \<Rightarrow> nat option" where
  "max_uid e = (let uids = uids e in if uids = {||} then None else Some (fMax uids))"

definition tm :: "iEFSM \<Rightarrow> transition_matrix" where
  "tm e = fimage snd e"

definition merge_states_aux :: "nat \<Rightarrow> nat \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "merge_states_aux s1 s2 e = fimage (\<lambda>(uid, (origin, dest), t). (uid, (if origin = s1 then s2 else origin , if dest = s1 then s2 else dest), t)) e"

definition merge_states :: "nat \<Rightarrow> nat \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
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

(* declare[[show_types,show_sorts]] *)

definition outgoing_transitions :: "cfstate \<Rightarrow> iEFSM \<Rightarrow> (cfstate \<times> transition \<times> tids) fset" where
  "outgoing_transitions s e = fimage (\<lambda>(uid, (from, to), t'). (to, t', uid)) ((ffilter (\<lambda>(uid, (origin, dest), t). origin = s)) e)"

\<comment> \<open>Tuples of the form $(cfstate \times (cfstate \times cfstate) \times ((transition \times tids) \times (transition \times tids)))$\<close>
type_synonym nondeterministic_pair = "(cfstate \<times> (cfstate \<times> cfstate) \<times> ((transition \<times> tids) \<times> (transition \<times> tids)))"

definition state_nondeterminism :: "nat \<Rightarrow> (cfstate \<times> transition \<times> tids) fset \<Rightarrow> nondeterministic_pair fset" where
  "state_nondeterminism og nt = (if size nt < 2 then {||} else ffUnion (fimage (\<lambda>x. let (dest, t) = x in fimage (\<lambda>y. let (dest', t') = y in (og, (dest, dest'), (t, t'))) (nt - {|x|})) nt))"

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

definition replace_all :: "iEFSM \<Rightarrow> tids list \<Rightarrow> transition \<Rightarrow> iEFSM" where
  "replace_all e ids new = fold (\<lambda>id acc. replace_transition acc id new) ids e"

definition replace_transitions :: "iEFSM \<Rightarrow> (tids \<times> transition) list \<Rightarrow> iEFSM" where
  "replace_transitions e ts = fold (\<lambda>(uid, new) acc. replace_transition acc uid new) ts e"

primrec make_guard :: "value list \<Rightarrow> nat \<Rightarrow> vname gexp list" where
"make_guard [] _ = []" |
"make_guard (h#t) n = (gexp.Eq (V (vname.I n)) (L h))#(make_guard t (n+1))"

primrec make_outputs :: "value list \<Rightarrow> output_function list" where
  "make_outputs [] = []" |
  "make_outputs (h#t) = (L h)#(make_outputs t)"

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

primrec make_pta_aux :: "log \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "make_pta_aux [] e = e" |
  "make_pta_aux (h#t) e = make_pta_aux t (make_branch e 0 <> h)"

definition "make_pta log = make_pta_aux log {||}"

lemma make_pta_aux_fold [code]: "make_pta_aux l e = fold (\<lambda>h e. make_branch e 0 <> h) l e"
  by(induct l arbitrary: e, auto)

type_synonym update_modifier = "tids \<Rightarrow> tids \<Rightarrow> cfstate \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM option"

definition null_modifier :: update_modifier where
  "null_modifier f _ _ _ _ _ _ = None"

record score = 
  Score :: nat
  S1 :: cfstate
  S2 :: cfstate
type_synonym scoreboard = "score fset"
type_synonym strategy = "tids \<Rightarrow> tids \<Rightarrow> iEFSM \<Rightarrow> nat"

primrec paths_of_length :: "nat \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> tids list fset" where
  "paths_of_length 0 _ _ = {|[]|}" |
  "paths_of_length (Suc m) e s = (
    let
      outgoing = outgoing_transitions s e;
      paths = ffUnion (fimage (\<lambda>(d, t, id). fimage (\<lambda>p. id#p) (paths_of_length m e d)) outgoing)
    in
      ffilter (\<lambda>l. length l = Suc m) paths
  )"

lemma fBall_ffilter: "\<forall>x |\<in>| X. f x \<Longrightarrow> ffilter f X = X"
  by auto

lemma fBall_ffilter2: "X = Y \<Longrightarrow> \<forall>x |\<in>| X. f x \<Longrightarrow> ffilter f X = Y"
  by auto

lemma paths_of_length_1:  "paths_of_length 1 e s = fimage (\<lambda>(d, t, id). [id]) (outgoing_transitions s e)"
  apply (simp add: One_nat_def)
  apply (simp add: outgoing_transitions_def comp_def One_nat_def[symmetric])
  apply (rule fBall_ffilter2)
   defer
   apply (simp add: ffilter_def ffUnion_def fBall_def Abs_fset_inverse)
   apply auto[1]
  apply (simp add: ffilter_def ffUnion_def fBall_def Abs_fset_inverse fset_both_sides)
  by force

fun step_score :: "(tids \<times> tids) list \<Rightarrow> iEFSM \<Rightarrow> strategy \<Rightarrow> nat" where
  "step_score [] _ _ = 0" |
  "step_score ((id1, id2)#t) e s = (
    let score = s id1 id2 e in
    if score = 0 then
      0
    else
      score + (step_score t e s)
  )"

lemma step_score_foldr [code]: "step_score xs e s = foldr (\<lambda>(id1, id2) acc. let score = s id1 id2 e in
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

definition score_from_list :: "tids list fset \<Rightarrow> tids list fset \<Rightarrow> iEFSM \<Rightarrow> strategy \<Rightarrow> nat" where
  "score_from_list P1 P2 e s = (
    let
      pairs = fimage (\<lambda>(l1, l2). zip l1 l2) (P1 |\<times>| P2);
      scored_pairs = fimage (\<lambda>l. step_score l e s) pairs
    in
    fSum scored_pairs
  )"

definition k_score :: "nat \<Rightarrow> iEFSM \<Rightarrow> strategy \<Rightarrow> scoreboard" where
  "k_score k e strat = (
    let 
      states = S e;
      pairs_to_score = (ffilter (\<lambda>(x, y). x < y) (states |\<times>| states));
      paths = fimage (\<lambda>(s1, s2). (s1, s2, paths_of_length k e s1, paths_of_length k e s2)) pairs_to_score;
      scores = fimage (\<lambda>(s1, s2, p1, p2). \<lparr>Score = score_from_list p1 p2 e strat, S1 = s1, S2 = s2\<rparr>) paths
    in
    ffilter (\<lambda>x. Score x > 0) scores
)"

definition score_state_pair :: "strategy \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> cfstate \<Rightarrow> nat" where
  "score_state_pair strat e s1 s2 = (
    let
      T1 = outgoing_transitions s1 e;
      T2 = outgoing_transitions s2 e
    in
      fSum (fimage (\<lambda>((_, _, t1), (_, _, t2)). strat t1 t2 e) (T1 |\<times>| T2))
  )"

definition score_1 :: "iEFSM \<Rightarrow> strategy \<Rightarrow> scoreboard" where
  "score_1 e strat = (
    let
      states = S e;
      pairs_to_score = (ffilter (\<lambda>(x, y). x < y) (states |\<times>| states));
      scores = fimage (\<lambda>(s1, s2). \<lparr>Score = score_state_pair strat e s1 s2, S1 = s1, S2 = s2\<rparr>) pairs_to_score
    in
      ffilter (\<lambda>x. Score x > 0) scores
  )"

lemma fprod_fimage: "((\<lambda>(_, _, id). [id]) |`| a |\<times>| (\<lambda>(_, _, id). [id]) |`| b) =
       fimage (\<lambda>((_, _, id1), (_, _, id2)). ([id1], [id2])) (a |\<times>| b)"
  apply (simp add: fimage_def fprod_def Abs_fset_inverse fset_both_sides)
  by force

lemma score_1: "score_1 e s = k_score 1 e s"
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

lemma satisfies_trace_prim: "satisfies_trace e s d l = satisfies_trace_prim e s d l"
proof(induct l arbitrary: s d)
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
  "(\<And>c. subsumes t2 c t1) \<Longrightarrow> directly_subsumes e1 e2 s s' t2 t1"
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

lemma cant_directly_subsume: "(\<And>c. \<not> subsumes t c t') \<Longrightarrow> \<not> directly_subsumes m m' s s' t t'"
  by (simp add: directly_subsumes_def)

definition insert_transition :: "tids \<Rightarrow> cfstate \<Rightarrow> cfstate \<Rightarrow> transition \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
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

definition make_distinct :: "iEFSM \<Rightarrow> iEFSM" where
  "make_distinct e = ffold_ord (\<lambda>(uid, (from, to), t) acc. insert_transition uid from to t acc) e {||}"

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
                       modifier function dest resolve nondeterminism that way.                    *)
(* @param oldEFSM   - the EFSM before merging the states which caused the nondeterminism          *)
(* @param preDestMerge   - the EFSM after merging the states which caused the nondeterminism      *)
(* @param newEFSM   - the current EFSM with nondeterminism                                        *)
(* @param t\<^sub>1        - a transition dest be merged with t\<^sub>2                                         *)
(* @param u\<^sub>1        - the unique identifier of t\<^sub>1                                                 *)
(* @param t\<^sub>2        - a transition dest be merged with t\<^sub>1                                         *)
(* @param u\<^sub>2        - the unique identifier of t\<^sub>2                                                 *)
(* @param modifier  - an update modifier function which tries dest generalise transitions         *)
definition merge_transitions :: "(cfstate \<times> cfstate) set \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> transition \<Rightarrow> tids \<Rightarrow> transition \<Rightarrow> tids \<Rightarrow> update_modifier \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> (iEFSM option \<times> (cfstate \<times> cfstate) set)" where
  "merge_transitions failedMerges oldEFSM preDestMerge destMerge t\<^sub>1 u\<^sub>1 t\<^sub>2 u\<^sub>2 modifier np = (
     if \<forall>id \<in> set u\<^sub>1. directly_subsumes oldEFSM destMerge (origin [id] oldEFSM) (origin u\<^sub>1 destMerge) t\<^sub>2 t\<^sub>1 then
       \<comment> \<open>Replace t1 with t2\<close>
       (Some (merge_transitions_aux destMerge u\<^sub>1 u\<^sub>2), failedMerges)
     else if \<forall>id \<in> set u\<^sub>2. directly_subsumes oldEFSM destMerge (origin [id] oldEFSM) (origin u\<^sub>2 destMerge) t\<^sub>1 t\<^sub>2 then
       \<comment> \<open>Replace t2 with t1\<close>
       (Some (merge_transitions_aux destMerge u\<^sub>2 u\<^sub>1), failedMerges)
     else
        case modifier u\<^sub>1 u\<^sub>2 (origin u\<^sub>1 destMerge) destMerge preDestMerge oldEFSM np of
          None \<Rightarrow> (None, failedMerges) |
          Some e \<Rightarrow> (Some (make_distinct e), failedMerges)
   )"

definition outgoing_transitions_from :: "iEFSM \<Rightarrow> cfstate \<Rightarrow> transition fset" where
  "outgoing_transitions_from e s = fimage (\<lambda>(_, _, t). t) (ffilter (\<lambda>(_, (orig, _), _). orig = s) e)"

fun bool2nat :: "bool \<Rightarrow> nat" where
  "bool2nat True = 1" |
  "bool2nat False = 0"

definition score_transitions :: "transition \<Rightarrow> transition \<Rightarrow> nat" where
  "score_transitions t1 t2 = (
    if Label t1 = Label t2 \<and> Arity t1 = Arity t2 \<and> length (Outputs t1) = length (Outputs t2) then
      1 + bool2nat (t1 = t2) + card ((set (Guard t2)) \<inter> (set (Guard t2))) + card ((set (Updates t2)) \<inter> (set (Updates t2))) + card ((set (Outputs t2)) \<inter> (set (Outputs t2)))
    else
      0
  )"

definition order_nondeterministic_pairs :: "nondeterministic_pair fset \<Rightarrow> nondeterministic_pair list" where
  "order_nondeterministic_pairs s = map snd (sorted_list_of_fset (fimage (\<lambda>s. let (_, _, (t1, _), (t2, _)) = s in (score_transitions t1 t2, s)) s))"

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
function resolve_nondeterminism :: "(cfstate \<times> cfstate) set \<Rightarrow> nondeterministic_pair list \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> (iEFSM option \<times> (cfstate \<times> cfstate) set)" where
  "resolve_nondeterminism failedMerges [] _ newEFSM _ check np = (
      if deterministic newEFSM np \<and> check (tm newEFSM) then Some newEFSM else None, failedMerges
  )" |
  "resolve_nondeterminism failedMerges ((from, (dest\<^sub>1, dest\<^sub>2), ((t\<^sub>1, u\<^sub>1), (t\<^sub>2, u\<^sub>2)))#ss) oldEFSM newEFSM m check np = (
    if (dest\<^sub>1, dest\<^sub>2) \<in> failedMerges \<or> (dest\<^sub>2, dest\<^sub>1) \<in> failedMerges then
      (None, failedMerges)
    else
    let destMerge = merge_states dest\<^sub>1 dest\<^sub>2 newEFSM in
    case merge_transitions failedMerges oldEFSM newEFSM destMerge t\<^sub>1 u\<^sub>1 t\<^sub>2 u\<^sub>2 m np of
      (None, failedMerges) \<Rightarrow> resolve_nondeterminism (insert (dest\<^sub>1, dest\<^sub>2) failedMerges) ss oldEFSM newEFSM m check np |
      (Some new, failedMerges) \<Rightarrow> (
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


(* Merge - tries dest merge two states in a given iEFSM and resolve the resulting nondeterminism    *)
(* @param e     - an iEFSM                                                                        *)
(* @param s1    - a state dest be merged with s2                                                    *)
(* @param s2    - a state dest be merged with s1                                                    *)
(* @param m     - an update modifier function which tries dest generalise transitions               *)
(* @param check - a function which takes an EFSM and returns a bool dest ensure that certain
                  properties hold in the new iEFSM                                                *)
definition merge :: "(cfstate \<times> cfstate) set \<Rightarrow> iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> (iEFSM option \<times> (cfstate \<times> cfstate) set)" where
  "merge failedMerges e s\<^sub>1 s\<^sub>2 m check np = (
    if s\<^sub>1 = s\<^sub>2 \<or> (s\<^sub>1, s\<^sub>2) \<in> failedMerges \<or> (s\<^sub>2, s\<^sub>1) \<in> failedMerges then
      (None, failedMerges)
    else 
      let e' = make_distinct (merge_states s\<^sub>1 s\<^sub>2 e) in
      resolve_nondeterminism failedMerges (order_nondeterministic_pairs (np e')) e e' m check np 
  )"

(* We want to sort first by score (highest to lowest) and then by state pairs (lowest to highest) *)
(* so we end up merging the states with the highest scores first and then break ties by those     *)
(* state pairs which are closest to the origin                                                    *)
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

(* inference_step - attempt dest carry out a single step of the inference process by merging the  *)
(* @param e - an iEFSM dest be generalised                                                        *)
(* @param ((s, s1, s2)#t) - a list of triples of the form (score, state, state) dest be merged    *)
(* @param m     - an update modifier function which tries dest generalise transitions             *)
(* @param check - a function which takes an EFSM and returns a bool dest ensure that certain
                  properties hold in the new iEFSM                                                *)
function inference_step :: "(cfstate \<times> cfstate) set \<Rightarrow> iEFSM \<Rightarrow> score fset \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> (iEFSM option \<times> (cfstate \<times> cfstate) set)" where
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

(* Takes an iEFSM and iterates inference_step until no further states can be successfully merged  *)
(* @param e - an iEFSM dest be generalised                                                        *)
(* @param r - a strategy dest identify and prioritise pairs of states dest merge                  *)
(* @param m     - an update modifier function which tries dest generalise transitions             *)
(* @param check - a function which takes an EFSM and returns a bool dest ensure that certain
                  properties hold in the new iEFSM                                                *)
function infer :: "(cfstate \<times> cfstate) set \<Rightarrow> nat \<Rightarrow> iEFSM \<Rightarrow> strategy \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM" where
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

lemma min_insert_zero: "a \<noteq> Min (insert a l) \<Longrightarrow> Min (insert a l) = Min l"
  by (metis Min.coboundedI Min.infinite Min.subset_imp Min_in Min_singleton antisym finite_insert insertE insert_not_empty subset_insertI)

lemma hd_insort: "a \<noteq> Min (insert a (set l)) \<Longrightarrow> hd (insort a (sort l)) = hd (sort l)"
  by (metis Min_singleton hd_sort_Min list.distinct(1) list.simps(15) min_insert_zero set_empty2 sort_key_simps(2))

fun get_ints :: "execution \<Rightarrow> int list" where
  "get_ints [] = []" |
  "get_ints ((_, inputs, outputs)#t) = (map (\<lambda>x. case x of Num n \<Rightarrow> n) (filter is_Num (inputs@outputs)))"

definition learn :: "nat \<Rightarrow> iEFSM \<Rightarrow> log \<Rightarrow> strategy \<Rightarrow> update_modifier \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM" where
  "learn n pta l r m np = (
     let check = satisfies (set l) in
         (infer {} n pta r m check np)
   )"

definition max_reg :: "iEFSM \<Rightarrow> nat option" where
  "max_reg e = EFSM.max_reg (tm e)"

definition "max_reg_total e = (case max_reg e of None \<Rightarrow> 0 | Some r \<Rightarrow> r)"

definition max_output :: "iEFSM \<Rightarrow> nat" where
  "max_output e = EFSM.max_output (tm e)"

primrec try_heuristics_check :: "(transition_matrix \<Rightarrow> bool) \<Rightarrow> update_modifier list \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> update_modifier" where
  "try_heuristics_check _ [] _ = null_modifier" |
  "try_heuristics_check check (h#t) np = (\<lambda>a b c d e f np. 
    case h a b c d e f np of
      Some e' \<Rightarrow> if check (tm e') then Some e' else (try_heuristics_check check t np) a b c d e f np |
      None \<Rightarrow> (try_heuristics_check check t np) a b c d e f np
    )"

definition all_regs :: "iEFSM \<Rightarrow> nat set" where
  "all_regs e = EFSM.all_regs (tm e)"

definition max_int :: "iEFSM \<Rightarrow> int" where
  "max_int e = EFSM.max_int (tm e)"

fun literal_args :: "'a gexp \<Rightarrow> bool" where
  "literal_args (Bc v) = False" |
  "literal_args (Eq (V _) (L _)) = True" |
  "literal_args (In _ _) = True" |
  "literal_args (Eq _ _) = False" |
  "literal_args (Gt va v) = False" |
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

definition "accepts_and_gets_us_to_both a b s s' = (
  \<exists>p. accepts_trace (tm a) p \<and>
      gets_us_to s (tm a) 0 <> p \<and>
      accepts_trace (tm b) p \<and>
      gets_us_to s' (tm b) 0 <> p)"

definition enumerate_exec_values :: "execution \<Rightarrow> value list" where
  "enumerate_exec_values vs = fold (\<lambda>(_, i, p) I. List.union (List.union i p) I) vs []"

definition enumerate_log_values :: "log \<Rightarrow> value list" where
  "enumerate_log_values l = fold (\<lambda>e I. List.union (enumerate_exec_values e) I) l []"

definition enumerate_exec_values_by_label :: "label \<Rightarrow> execution \<Rightarrow> value list" where
  "enumerate_exec_values_by_label label vs = fold (\<lambda>(l, i, p) I. if l = label then List.union (List.union i p) I else I) vs []"

definition enumerate_log_values_by_label :: "label \<Rightarrow> log \<Rightarrow> value list" where
  "enumerate_log_values_by_label label log = fold (\<lambda>e I. List.union (enumerate_exec_values_by_label label e) I) log []"

fun test_exec :: "execution \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> ((label \<times> inputs \<times> cfstate \<times> cfstate \<times> registers \<times> tids \<times> value list \<times> outputs) list \<times> execution)" where
  "test_exec [] _ _ _ = ([], [])" |
  "test_exec ((l, i, expected)#es) e s r = (
    let
      ps = i_possible_steps e s r l i
    in
      if fis_singleton ps then
        let
          (id, s', t) = fthe_elem ps;
          r' = apply_updates (Updates t) (join_ir i r) r;
          actual = apply_outputs (Outputs t) (join_ir i r);
          (est, fail) = (test_exec es e s' r')
        in
        ((l, i, s, s', r, id, expected, actual)#est, fail)
      else
        ([], (l, i, expected)#es)
  )"

definition test_log :: "log \<Rightarrow> iEFSM \<Rightarrow> ((label \<times> inputs \<times> cfstate \<times> cfstate \<times> registers \<times> tids \<times> value list \<times> outputs) list \<times> execution) list" where
  "test_log l e = map (\<lambda>t. test_exec t e 0 <>) l"

end
