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
We first need dest define the i_efsm data type which assigns each transition a unique identity. This is
necessary because transitions may not be unique in an EFSM. Assigning transitions a unique
identifier enables us dest look up the origin and destination states of transitions without having dest
pass them around in the inference functions.
\<close>
type_synonym tid = nat
type_synonym i_transition_matrix = "(tid \<times> (cfstate \<times> cfstate) \<times> transition) fset"
record i_efsm =
  T :: i_transition_matrix
  F :: "nat fset"

lemma i_efsm_equiv_if: "T e = T e' \<Longrightarrow> F e = F e' \<Longrightarrow> (e::i_efsm) = e'"
  by simp

definition get_by_id :: "i_efsm \<Rightarrow> nat \<Rightarrow> transition" ("(_|_|)" [20, 20] 40) where
  "get_by_id e u = snd (snd (fthe_elem (ffilter (\<lambda>(uid, _). uid = u) (T e))))"

definition max_uid :: "i_transition_matrix \<Rightarrow> nat" where
  "max_uid e = fMax (fimage fst e)"

primrec toi_efsm_aux :: "nat \<Rightarrow> ((nat \<times> nat) \<times> transition) list \<Rightarrow> (nat \<times> (nat \<times> nat) \<times> transition) list" where
  "toi_efsm_aux _ [] = []" |
  "toi_efsm_aux n (h#t) = (n, h)#(toi_efsm_aux (n+1) t)"

definition toi_efsm :: "efsm \<Rightarrow> i_efsm" where
  "toi_efsm e = \<lparr>T = fset_of_list (toi_efsm_aux 0 (sorted_list_of_fset (efsm.T e))), F = efsm.F e\<rparr>"

definition tm :: "i_efsm \<Rightarrow> efsm" where
  "tm e = \<lparr>efsm.T = fimage snd (T e), F = F e\<rparr>"

lemma in_tm: "((s, a), bb) |\<in>| efsm.T (tm b) \<Longrightarrow> \<exists>id. (id, (s, a), bb) |\<in>| T b"
  apply (simp add: tm_def fimage_def fmember_def Abs_fset_inverse)
  by fastforce

definition maxUID :: "i_efsm \<Rightarrow> nat" where
  "maxUID e = fMax (fimage (\<lambda>x. fst x) (T e))"

definition S :: "i_efsm \<Rightarrow> nat fset" where
  "S m = fimage (\<lambda>(uid, (s, s'), t). s) (T m) |\<union>| fimage (\<lambda>(uid, (s, s'), t). s') (T m)"

lemma S_alt: "S t = EFSM.S (tm t)"
  apply (simp add: S_def EFSM.S_def tm_def)
  by force

lemma to_in_S: "(\<exists>to from uid. (uid, (from, to), t) |\<in>| (T xb) \<longrightarrow> to |\<in>| S xb)"
  apply (simp add: S_def)
  by blast

lemma from_in_S: "(\<exists>to from uid. (uid, (from, to), t) |\<in>| (T xb) \<longrightarrow> from |\<in>| S xb)"
  apply (simp add: S_def)
  by blast

definition tS :: "i_transition_matrix \<Rightarrow> nat fset" where
  "tS m = fimage (\<lambda>(uid, (s, s'), t). s) m |\<union>| fimage (\<lambda>(uid, (s, s'), t). s') m"

lemma S_tS: "S t = tS (T t)"
  by (simp add: S_def tS_def)

definition merge_states_aux :: "nat \<Rightarrow> nat \<Rightarrow> i_transition_matrix \<Rightarrow> i_transition_matrix" where
  "merge_states_aux x y t = (fimage (\<lambda>(uid, (origin, dest), t). (uid, (if origin = x then y else origin , if dest = x then y else dest), t)) t)"

lemma merge_states_aux_finsert: "merge_states_aux x y (finsert t ts) =
finsert ((\<lambda>(uid, (origin, dest), t). (uid, (if origin = x then y else origin , if dest = x then y else dest), t)) t) (merge_states_aux x y ts)"
  by (simp add: merge_states_aux_def)

definition merge_states :: "nat \<Rightarrow> nat \<Rightarrow> i_efsm \<Rightarrow> i_efsm option" where
  "merge_states x y t = (
    if (x |\<in>| F t \<and> y |\<in>| F t) \<or>
       (x |\<notin>| F t \<and> y |\<notin>| F t) then
      let newT = (if x > y then merge_states_aux x y (T t) else merge_states_aux y x (T t)) in
      Some \<lparr>T = newT, F = (tS newT |\<union>| F t) |\<inter>| (F t)\<rparr>
    else
      None
  )"

lemma merge_states_aux_self: "merge_states_aux x x e = e"
proof(induct e)
  case empty
  then show ?case
    by (simp add: merge_states_aux_def)
next
  case (insert x e)
  then show ?case
    apply (cases x)
    by (simp add: merge_states_aux_def)
qed

lemma merge_states_same: "merge_states x x t = Some t"
  apply (simp add: merge_states_def Let_def)
  apply (rule i_efsm_equiv_if)
   apply (simp add: merge_states_aux_self)
  by auto

lemma merge_states_symmetry: "merge_states x y t = merge_states y x t"
  by (simp add: merge_states_def merge_states_aux_def)

(* declare[[show_types,show_sorts]] *)

definition outgoing_transitions :: "cfstate \<Rightarrow> i_efsm \<Rightarrow> (cfstate \<times> transition \<times> tid) fset" where
  "outgoing_transitions n t = fimage (\<lambda>(uid, (from, to), t'). (to, t', uid)) (ffilter (\<lambda>(uid, (origin, dest), t). origin = n) (T t))"

type_synonym nondeterministic_pair = "(nat \<times> (nat \<times> nat) \<times> ((transition \<times> nat) \<times> (transition \<times> nat)))"

definition state_nondeterminism :: "nat \<Rightarrow> (nat \<times> transition \<times> nat) fset \<Rightarrow> nondeterministic_pair fset" where
  "state_nondeterminism origin nt = (if size nt < 2 then {||} else ffUnion (fimage (\<lambda>x. let (dest, t) = x in fimage (\<lambda>y. let (dest', t') = y in (origin, (dest, dest'), (t, t'))) (nt - {|x|})) nt))"

lemma state_nondeterminism_empty[simp]: "state_nondeterminism a {||} = {||}"
  by (simp add: state_nondeterminism_def ffilter_def Set.filter_def)

lemma state_nondeterminism_singledestn[simp]: "state_nondeterminism a {|x|} = {||}"
  by (simp add: state_nondeterminism_def ffilter_def Set.filter_def)

(* For each state, get its outgoing transitions and see if there's any nondeterminism there *)
definition nondeterministic_pairs :: "i_efsm \<Rightarrow> nondeterministic_pair fset" where
  "nondeterministic_pairs t = ffilter (\<lambda>(_, _, (t, _), (t', _)). Label t = Label t' \<and> Arity t = Arity t' \<and> choice t t') (ffUnion (fimage (\<lambda>s. state_nondeterminism s (outgoing_transitions s t)) (S t)))"

definition nondeterministic_pairs_labar_dest :: "i_efsm \<Rightarrow> nondeterministic_pair fset" where
  "nondeterministic_pairs_labar_dest t = ffilter
     (\<lambda>(_, (d, d'), (t, _), (t', _)).
      Label t = Label t' \<and> Arity t = Arity t' \<and> (choice t t' \<or> (Outputs t = Outputs t' \<and> d = d')))
     (ffUnion (fimage (\<lambda>s. state_nondeterminism s (outgoing_transitions s t)) (S t)))"

definition nondeterministic_pairs_labar :: "i_efsm \<Rightarrow> nondeterministic_pair fset" where
  "nondeterministic_pairs_labar t = ffilter
     (\<lambda>(_, (d, d'), (t, _), (t', _)).
      Label t = Label t' \<and> Arity t = Arity t' \<and> (choice t t' \<or> Outputs t = Outputs t'))
     (ffUnion (fimage (\<lambda>s. state_nondeterminism s (outgoing_transitions s t)) (S t)))"

definition deterministic :: "i_efsm \<Rightarrow> (i_efsm \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> bool" where
  "deterministic t np = (np t = {||})"

definition nondeterministic :: "i_efsm \<Rightarrow> (i_efsm \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> bool" where
  "nondeterministic t np = (\<not> deterministic t np)"

definition replace_transition :: "i_efsm \<Rightarrow> tid \<Rightarrow> cfstate \<Rightarrow> cfstate \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> i_efsm" where
  "replace_transition t uid from dest orig new = \<lparr>T = (ffilter (\<lambda>x. snd x \<noteq> ((from, dest), orig) \<and> snd x \<noteq> ((from, dest), new)) (T t)) |\<union>| {|(uid, (from, dest), new)|}, F = F t\<rparr>"

definition exits_state :: "i_efsm \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> bool" where
  "exits_state e t from = (\<exists>dest uid. (uid, (from, dest), t) |\<in>| (T e))"

primrec make_guard :: "value list \<Rightarrow> nat \<Rightarrow> gexp list" where
"make_guard [] _ = []" |
"make_guard (h#t) n = (gexp.Eq (V (vname.I n)) (L h))#(make_guard t (n+1))"

fun make_outputs :: "value option list \<Rightarrow> output_function list" where
  "make_outputs [] = []" |
  "make_outputs (None # t) = Null#(make_outputs t)" |
  "make_outputs (Some h#t) = (Eq (L h))#(make_outputs t)"

definition add_transition :: "efsm \<Rightarrow> cfstate \<Rightarrow> label \<Rightarrow> value list \<Rightarrow> outputs \<Rightarrow> efsm" where
  "add_transition e s label inputs outputs = \<lparr>efsm.T = finsert ((s, (maxS e)+1), \<lparr>Label=label, Arity=length inputs, Guard=(make_guard inputs 0), Outputs=(make_outputs outputs), Updates=[]\<rparr>) (efsm.T e), F = efsm.F e\<rparr>"

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
      value.Num _ \<Rightarrow> make_guard_abstract t (i+1) maxR r ((gexp.Eq (V (vname.I i)) (L h))#G) U |
      value.Str s \<Rightarrow>
        if s = STR ''_'' then
          make_guard_abstract t (i+1) maxR r G U
        else if startsWith s STR ''$'' then
          case r $ s of
            None \<Rightarrow> make_guard_abstract t (i+1) (maxR + 1) (r(s := maxR)) G ((maxR, V (I i))#U) |
            Some reg \<Rightarrow> make_guard_abstract t (i+1) maxR r ((gexp.Eq (V (vname.I i)) (V (R reg)))#G) U
        else if startsWith s STR ''<'' then
          if startsWith (substring s 1) STR ''$'' then
            case r $ (substring s 1) of
              Some reg \<Rightarrow> make_guard_abstract t (i+1) maxR r ((gexp.Gt (V (vname.I i)) (V (R reg)))#G) U
          else
            make_guard_abstract t (i+1) maxR r ((gexp.Gt (V (vname.I i)) (L (Num (parseInt (substring s 2)))))#G) U
        else if startsWith s STR ''/='' then
          if startsWith (substring s 1) STR ''$'' then
            case r $ (substring s 2) of
              Some reg \<Rightarrow> make_guard_abstract t (i+1) maxR r ((gexp.Gt (V (vname.I i)) (V (R reg)))#G) U
          else
            make_guard_abstract t (i+1) maxR r ((gexp.Gt (V (vname.I i)) (L (Num (parseInt (substring s 3)))))#G) U
        else
          make_guard_abstract t (i+1) maxR r ((gexp.Eq (V (vname.I i)) (L h))#G) U
  )"

fun make_outputs_abstract :: "outputs \<Rightarrow> nat \<Rightarrow> (String.literal \<Rightarrow>f nat option) \<Rightarrow> output_function list \<Rightarrow> output_function list" where
  "make_outputs_abstract []_ _ P = rev P" |
  "make_outputs_abstract (None # t) maxR r P = make_outputs_abstract t maxR r (Null#P)" |
  "make_outputs_abstract (Some h#t) maxR r P = (case h of
    value.Num _ \<Rightarrow> make_outputs_abstract t maxR r ((Eq (L h))#P) |
    value.Str s \<Rightarrow>
      if startsWith s STR ''$'' then 
        case r $ s of
          Some reg \<Rightarrow> make_outputs_abstract t maxR r (Eq (V (R reg))#P)
      else
        make_outputs_abstract t maxR r ((Eq (L h))#P)
    )"

definition add_transition_abstract :: "efsm \<Rightarrow> (String.literal \<Rightarrow>f nat option) \<Rightarrow> cfstate \<Rightarrow> label \<Rightarrow> value list \<Rightarrow> outputs \<Rightarrow> (efsm \<times> (String.literal \<Rightarrow>f nat option))" where
  "add_transition_abstract e r s label inputs outputs = (let
    regs = fimage (total_max_reg \<circ> snd) (efsm.T e);
    maxR = (if regs = {||} then 1 else fMax regs);
    (G, U1, r') = make_guard_abstract inputs 0 maxR r [] [];
    P = make_outputs_abstract outputs maxR r' [] in
    if endsWith label STR ''*'' then
      (\<lparr>efsm.T = (finsert ((s, s), \<lparr>Label=dropRight label 1, Arity=length inputs, Guard=G, Outputs=P, Updates=U1\<rparr>) (efsm.T e)), F = efsm.F e\<rparr>, r')
    else
      (\<lparr>efsm.T = (finsert ((s, (maxS e)+1), \<lparr>Label=label, Arity=length inputs, Guard=G, Outputs=P, Updates=U1\<rparr>) (efsm.T e)), F = efsm.F e\<rparr>, r')
    )"

fun make_branch :: "efsm \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> efsm" where
  "make_branch e s _ [] = \<lparr>efsm.T = efsm.T e, F = finsert s (efsm.F e)\<rparr>" |
  "make_branch e s r ((label, inputs, outputs)#t) =
    (case (step (efsm.T e) s r label inputs outputs) of
      Some (transition, s', updated) \<Rightarrow> make_branch e s' updated t |
      None \<Rightarrow>
          make_branch (add_transition e s label inputs outputs) ((maxS e)+1) r t
    )"

fun make_branch_abstract :: "(efsm \<times> (String.literal \<Rightarrow>f nat option)) \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> efsm" where
  "make_branch_abstract (e, r) s _ [] = \<lparr>efsm.T = efsm.T e, F = finsert s (efsm.F e)\<rparr>" |
  "make_branch_abstract (e, r1) s r ((label, inputs, outputs)#t) = (
   case (step (efsm.T e) s r label inputs outputs) of
     Some (transition, s', updated) \<Rightarrow>
       make_branch_abstract (e, r1) s' updated t |
     None \<Rightarrow>
       make_branch_abstract (add_transition_abstract e r1 s label inputs outputs) ((maxS e)+1) r t
    )"

primrec make_pta :: "log \<Rightarrow> efsm \<Rightarrow> efsm" where
  "make_pta [] e = e" |
  "make_pta (h#t) e = make_pta t (make_branch e 0 <> h)"

definition make_pta_abstract :: "log \<Rightarrow> efsm \<Rightarrow> efsm" where
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

type_synonym update_modifier = "tid \<Rightarrow> tid \<Rightarrow> cfstate \<Rightarrow> i_efsm \<Rightarrow> i_efsm \<Rightarrow> (i_efsm \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> i_efsm option"

definition null_modifier :: update_modifier where
  "null_modifier _ _ _ _ _ _ = None"

type_synonym scoreboard = "(nat \<times> (cfstate \<times> cfstate)) fset"
type_synonym strategy = "tid \<Rightarrow> tid \<Rightarrow> i_efsm \<Rightarrow> nat"

primrec k_outgoing :: "nat \<Rightarrow> i_efsm \<Rightarrow> cfstate \<Rightarrow> (cfstate \<times> transition \<times> tid) fset" where
  "k_outgoing 0 i s = outgoing_transitions s i" |
  "k_outgoing (Suc m) i s = (let
     outgoing = outgoing_transitions s i;
     others = fimage fst outgoing in
     outgoing |\<union>| ffUnion (fimage (\<lambda>s. k_outgoing m i s) others)
  )"

definition k_score :: "bool \<Rightarrow> nat \<Rightarrow> i_efsm \<Rightarrow> strategy \<Rightarrow> scoreboard" where
  "k_score mergeFinals n e rank = (let 
     states = (S e);
     pairs_to_score = (ffilter (\<lambda>(x, y). x < y) (states |\<times>| states));
     scores = fimage (\<lambda>(s1, s2). let
        outgoing_s1 = fimage (snd \<circ> snd) (k_outgoing n e s1);
        outgoing_s2 = fimage (snd \<circ> snd) (k_outgoing n e s2);
        scores = fimage (\<lambda>(x, y). rank x y e) (outgoing_s1 |\<times>| outgoing_s2) in
       if mergeFinals \<and> outgoing_s1 = {||} \<and> outgoing_s2 = {||} then (1, s1, s2) else (fSum scores, s1, s2 )
     ) pairs_to_score in
     ffilter (\<lambda>(score, _). score > 0) scores)"

definition origin :: "nat \<Rightarrow> i_efsm \<Rightarrow> nat" where
  "origin uid t = fst (fst (snd (fthe_elem (ffilter (\<lambda>x. (\<exists>s. x = (uid, s))) (T t)))))"

lemma origin_code [code]: "origin uid t = fst (fst (snd (fthe_elem (ffilter (\<lambda>x. fst x = uid) (T t)))))"
  apply (simp add: origin_def)
  by (metis fst_eqD surj_pair)

definition dest :: "nat \<Rightarrow> i_efsm \<Rightarrow> nat" where
  "dest uid t = snd (fst (snd (fthe_elem (ffilter (\<lambda>x. (\<exists>s. x = (uid, s))) (T t)))))"

lemma dest_code [code]: "dest uid t = snd (fst (snd (fthe_elem (ffilter (\<lambda>x. fst x = uid) (T t)))))"
  apply (simp add: dest_def)
  by (metis fst_eqD surj_pair)

inductive satisfies_trace :: "efsm \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> bool" where
  base: "satisfies_trace e s d []" |                                         
  step: "\<exists>(s', T) |\<in>| possible_steps (efsm.T e) s d l i p.
         satisfies_trace e s' (apply_updates (Updates T) (join_ir i d) d) t \<Longrightarrow>
         satisfies_trace e s d ((l, i, p)#t)"

lemma satisfies_trace_step: "satisfies_trace e s d ((l, i, p)#t) = (\<exists>(s', T) |\<in>| possible_steps (efsm.T e) s d l i p.
         satisfies_trace e s' (apply_updates (Updates T) (join_ir i d) d) t)"
  apply standard
   defer
   apply (simp add: satisfies_trace.step)
  apply (rule satisfies_trace.cases)
  by auto

fun satisfies_trace_prim :: "efsm \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> bool" where
  "satisfies_trace_prim _ _ _ [] = True" |
  "satisfies_trace_prim e s d ((l, i, p)#t) = (
    let poss_steps = possible_steps (efsm.T e) s d l i p in
    if fis_singleton poss_steps then
      let (s', T) = fthe_elem poss_steps in
        satisfies_trace_prim e s' (apply_updates (Updates T) (join_ir i d) d) t
    else
      (\<exists>(s', T) |\<in>| poss_steps.
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

definition satisfies :: "execution set \<Rightarrow> efsm \<Rightarrow> bool" where
  "satisfies Tm e = (\<forall>t \<in> Tm. satisfies_trace e 0 <> t)"

definition directly_subsumes :: "i_efsm \<Rightarrow> i_efsm \<Rightarrow> cfstate \<Rightarrow> cfstate \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> bool" where
  "directly_subsumes e1 e2 s s' t1 t2 \<equiv> (\<forall>p. recognises_trace (tm e1) p \<and> gets_us_to s (tm e1) 0 <>  p \<longrightarrow>
                                             recognises_trace (tm e2) p \<and> gets_us_to s' (tm e2) 0 <>  p \<longrightarrow>
                                             (\<forall>c. anterior_context (tm e2) p = Some c \<longrightarrow> subsumes t1 c t2)) \<and>
                                         (\<exists>c. subsumes t1 c t2)"

lemma directly_subsumes_self: "directly_subsumes e1 e2 s s' t t"
  apply (simp add: directly_subsumes_def)
  by (simp add: transition_subsumes_self)

lemma subsumes_in_all_contexts_directly_subsumes:
  "\<forall>c. subsumes t2 c t1 \<Longrightarrow> directly_subsumes e1 e2 s s' t2 t1"
  by (simp add: directly_subsumes_def)

lemma gets_us_to_and_not_subsumes: 
  "\<exists>p. recognises_trace (tm e1) p \<and>
       gets_us_to s (tm e1) 0 (K$ None) p \<and>
       recognises_trace (tm e2) p \<and>
       gets_us_to s' (tm e2) 0 (K$ None) p \<and>
       (anterior_context (tm e2) p) = Some a \<and>
       \<not> subsumes t1 a t2 \<Longrightarrow>
   \<not> directly_subsumes e1 e2 s s' t1 t2"
  unfolding directly_subsumes_def by auto

lemma cant_directly_subsume: "\<forall>c. \<not> subsumes t c t' \<Longrightarrow> \<not> directly_subsumes m m' s s' t t'"
  by (simp add: directly_subsumes_def)

definition drop_transition :: "i_efsm \<Rightarrow> nat \<Rightarrow> i_efsm" where
  "drop_transition e t = \<lparr>T = ffilter (\<lambda>(uid, _). uid \<noteq> t) (T e), F = F e\<rparr>"

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
definition merge_transitions :: "i_efsm \<Rightarrow> i_efsm \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> update_modifier \<Rightarrow> (i_efsm \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> i_efsm option" where
  "merge_transitions oldEFSM destMerge t\<^sub>1 u\<^sub>1 t\<^sub>2 u\<^sub>2 modifier np = (
     if directly_subsumes oldEFSM destMerge (origin u\<^sub>1 oldEFSM) (origin u\<^sub>1 destMerge) t\<^sub>2 t\<^sub>1 then
       Some (drop_transition destMerge u\<^sub>1)
     else if directly_subsumes oldEFSM destMerge (origin u\<^sub>2 oldEFSM) (origin u\<^sub>2 destMerge) t\<^sub>1 t\<^sub>2 then
       Some (drop_transition destMerge u\<^sub>2)
     else
        modifier u\<^sub>1 u\<^sub>2 (origin u\<^sub>1 destMerge) destMerge oldEFSM np
   )"

fun make_distinct_aux :: "(nat \<times> (nat \<times> nat) \<times> transition) list \<Rightarrow> i_transition_matrix \<Rightarrow> i_transition_matrix" where
  "make_distinct_aux [] e = e" |
  "make_distinct_aux (h#t) e = (if snd h |\<in>| fimage snd e then make_distinct_aux t e else make_distinct_aux t (finsert h e))"

(* This removes duplicate transitions (i.e. identical transitions with the same origin and        *)
(* destination states but with different uids                                                     *)
definition make_distinct :: "i_efsm option \<Rightarrow> i_efsm option" where
  "make_distinct e = (case e of None \<Rightarrow> None | Some e \<Rightarrow> Some \<lparr>T = make_distinct_aux (sorted_list_of_fset (T e)) {||}, F = F e\<rparr>)"

(* resolve_nondeterminism - tries dest resolve nondeterminism in a given i_efsm                      *)
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
                  properties hold in the new i_efsm                                                *)
function resolve_nondeterminism :: "(cfstate \<times> cfstate) list \<Rightarrow> nondeterministic_pair list \<Rightarrow> i_efsm \<Rightarrow> i_efsm \<Rightarrow> update_modifier \<Rightarrow> (efsm \<Rightarrow> bool) \<Rightarrow> (i_efsm \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> i_efsm option" where
  "resolve_nondeterminism _ [] _ new _ check np = (if deterministic new np \<and> check (tm new) then Some new else None)" |
  "resolve_nondeterminism closed ((from, (dest\<^sub>1, dest\<^sub>2), ((t\<^sub>1, u\<^sub>1), (t\<^sub>2, u\<^sub>2)))#ss) oldEFSM newEFSM m check np = (
     \<comment> \<open>Fail if we've already tried (and failed) to merge the destination states\<close>
     if (dest\<^sub>1, dest\<^sub>2) \<in> set closed then None else
     \<comment> \<open>Otherwise merge the destination states and then the transitions\<close>
     case (if dest\<^sub>1 = dest\<^sub>2 then Some newEFSM else merge_states dest\<^sub>1 dest\<^sub>2 newEFSM) of
      None \<Rightarrow> None |
      Some destMerge \<Rightarrow> (
        case make_distinct (merge_transitions oldEFSM destMerge t\<^sub>1 u\<^sub>1 t\<^sub>2 u\<^sub>2 m np) of
          None \<Rightarrow> resolve_nondeterminism ((dest\<^sub>1, dest\<^sub>2)#closed) ss oldEFSM newEFSM m check np |
          Some new \<Rightarrow>
            let newScores = (sorted_list_of_fset (np new)) in 
            if length (newScores) + size (T new) + size (S new) < length (ss) + 1 + size (T newEFSM) + size (S newEFSM) then
              case resolve_nondeterminism closed newScores oldEFSM new m check np of
                Some new' \<Rightarrow> Some new' |
                None \<Rightarrow> resolve_nondeterminism ((dest\<^sub>1, dest\<^sub>2)#closed) ss oldEFSM newEFSM m check np
            else
              None)
   )"
     apply clarify
     apply simp
     apply (metis neq_Nil_conv prod_cases3 surj_pair)
  by auto
termination
  by (relation "measures [\<lambda>(_, ss, _, newEFSM, _). length ss + size (T newEFSM) + size (S newEFSM)]", auto)

(* Merge - tries dest merge two states in a given i_efsm and resolve the resulting nondeterminism    *)
(* @param e     - an i_efsm                                                                        *)
(* @param s1    - a state dest be merged with s2                                                    *)
(* @param s2    - a state dest be merged with s1                                                    *)
(* @param m     - an update modifier function which tries dest generalise transitions               *)
(* @param check - a function which takes an EFSM and returns a bool dest ensure that certain
                  properties hold in the new i_efsm                                                *)
definition merge :: "i_efsm \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> update_modifier \<Rightarrow> (efsm \<Rightarrow> bool) \<Rightarrow> (i_efsm \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> i_efsm option" where
  "merge e s\<^sub>1 s\<^sub>2 m check np = (
    if s\<^sub>1 = s\<^sub>2 then
      None
    else
      case (merge_states s\<^sub>1 s\<^sub>2 e) of None \<Rightarrow> None | Some e' \<Rightarrow> (
      case resolve_nondeterminism [] (sorted_list_of_fset (np e')) e e' m check np of
      None \<Rightarrow> None |
      \<comment> \<open>Strip out any merged accept states\<close>
      Some merged \<Rightarrow> Some \<lparr>T = T merged, F = S merged |\<inter>| F merged\<rparr>)
  )"

(* inference_step - attempt dest carry out a single step of the inference process by merging the    *)
(* @param e - an i_efsm dest be generalised                                                          *)
(* @param ((s, s1, s2)#t) - a list of triples of the form (score, state, state) dest be merged      *)
(* @param m     - an update modifier function which tries dest generalise transitions               *)
(* @param check - a function which takes an EFSM and returns a bool dest ensure that certain
                  properties hold in the new i_efsm                                                *)
fun inference_step :: "i_efsm \<Rightarrow> (nat \<times> nat \<times> nat) list \<Rightarrow> update_modifier \<Rightarrow> (efsm \<Rightarrow> bool) \<Rightarrow> (i_efsm \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> i_efsm option" where
  "inference_step _ [] _ _ _ = None" |
  "inference_step e ((_, s\<^sub>1, s\<^sub>2)#t) m check np = (
     case merge e s\<^sub>1 s\<^sub>2 m check np of
       Some new \<Rightarrow> Some new |
       None \<Rightarrow> inference_step e t m check np
  )"

(* Takes an i_efsm and iterates inference_step until no further states can be successfully merged  *)
(* @param e - an i_efsm dest be generalised                                                          *)
(* @param r - a strategy dest identify and prioritise pairs of states dest merge                      *)
(* @param m     - an update modifier function which tries dest generalise transitions               *)
(* @param check - a function which takes an EFSM and returns a bool dest ensure that certain
                  properties hold in the new i_efsm                                                *)
function infer :: "bool \<Rightarrow> nat \<Rightarrow> i_efsm \<Rightarrow> strategy \<Rightarrow> update_modifier \<Rightarrow> (efsm \<Rightarrow> bool) \<Rightarrow> (i_efsm \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> i_efsm" where
  "infer mergeFinals n e r m check np = (
    case inference_step e (rev (sorted_list_of_fset (k_score mergeFinals n e r))) m check np of
      None \<Rightarrow> e |
      Some new \<Rightarrow> if size (S new) + size (T new) < size (S e) + size (T e) then infer mergeFinals n new r m check np else e
  )"
  by auto
termination
  by (relation "measures [\<lambda>(_, n, e, _). size (S e) + size (T e)]", auto)

fun get_smallest :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "get_smallest n s = (if n \<notin> set s then n else get_smallest (n + 1) (removeAll n s))"

definition make_smaller_aux :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "make_smaller_aux i s = (if i < 100 then i else get_smallest i s)"

fun make_smaller :: "int \<Rightarrow> nat list \<Rightarrow> int" where
  "make_smaller n s = (if n < 0 then - (int (make_smaller_aux (nat n) s)) else int (make_smaller_aux (nat n) s))"

fun make_smaller_val :: "nat list \<Rightarrow> value \<Rightarrow> value" where
  "make_smaller_val _ (value.Str s) = value.Str s" |
  "make_smaller_val s (Num n) = Num (make_smaller n s)"

definition learn :: "bool \<Rightarrow> nat \<Rightarrow> efsm \<Rightarrow> log \<Rightarrow> strategy \<Rightarrow> update_modifier \<Rightarrow> (i_efsm \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> efsm" where
  "learn mergeFinals n pta l r m np = (
     let check = satisfies (set l) in
         (tm (infer mergeFinals n (toi_efsm pta) r m check np))
   )"

definition uids :: "i_efsm \<Rightarrow> nat fset" where
  "uids e = fimage fst (T e)"

lemma uid_in_uids: "(\<exists>to from uid. (uid, (from, to), t) |\<in>| (T xb) \<longrightarrow> uid |\<in>| uids xb)"
  apply (simp add: uids_def)
  by blast

lemma to_from_in_S_uid_in_uids: "(uid, (from, to), t) |\<in>| (T e) \<Longrightarrow> to |\<in>| S e \<and> from |\<in>| S e \<and> uid |\<in>| uids e"
  apply (simp add: S_def uids_def)
  by force

definition max_reg :: "i_efsm \<Rightarrow> nat option" where
  "max_reg e = (let maxes = (fimage (\<lambda>(_, _, t). Transition.max_reg t) (T e)) in if maxes = {||} then None else fMax maxes)"

lemma fMax_None: "f \<noteq> {||} \<Longrightarrow> fMax f = None = (\<forall>x |\<in>| f. x = None)"
  apply standard
  using fMax_ge x_leq_None apply fastforce
  by (meson fBallE fMax_in)

lemma max_reg_none_no_updates: "Inference.max_reg b = None \<Longrightarrow>
       \<forall>(id, (s, s'), t) |\<in>| (T b).  (Updates t) = []"
  apply (simp add: Inference.max_reg_def)
  apply (case_tac "T b = {||}")
   apply simp
  apply (simp add: fMax_None)
  apply clarify
  using max_reg_none_no_updates
  by force

definition total_max_reg :: "i_efsm \<Rightarrow> nat" where
  "total_max_reg e = (case fMax (fimage (\<lambda>(_, _, t). Transition.max_reg t) (T e)) of None \<Rightarrow> 0 | Some r \<Rightarrow> r)"

definition max_output :: "i_efsm \<Rightarrow> nat" where
  "max_output e = fMax (fimage (\<lambda>(_, _, t). length (Outputs t)) (T e))"

primrec try_heuristics :: "update_modifier list \<Rightarrow> (i_efsm \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> update_modifier" where
  "try_heuristics [] _ = null_modifier" |
  "try_heuristics (h#t) np = (\<lambda>a b c d e np. case h a b c d e np of Some e' \<Rightarrow> Some e' | None \<Rightarrow> (try_heuristics t np) a b c d e np)"

primrec try_heuristics_check :: "(efsm \<Rightarrow> bool) \<Rightarrow> update_modifier list \<Rightarrow> (i_efsm \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> update_modifier" where
  "try_heuristics_check _ [] _ = null_modifier" |
  "try_heuristics_check check (h#t) np = (\<lambda>a b c d e np. 
    case h a b c d e np of
      Some e' \<Rightarrow>
        if check (tm e') then Some e' else (try_heuristics_check check t np) a b c d e np |
      None \<Rightarrow> (try_heuristics_check check t np) a b c d e np
    )"

definition drop_transitions :: "i_efsm \<Rightarrow> nat fset \<Rightarrow> i_efsm" where
  "drop_transitions e t = \<lparr>T = ffilter (\<lambda>(uid, _). uid |\<notin>| t) (T e), F = F e\<rparr>"

definition replaceAll :: "i_efsm \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> i_efsm" where
  "replaceAll e old new = \<lparr>T = fimage (\<lambda>(uid, (from, dest), t). if t = old then (uid, (from, dest), new) else (uid, (from, dest), t)) (T e), F = F e\<rparr>"

definition replace :: "i_efsm \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> i_efsm" where
  "replace e tID t' = \<lparr>T = fimage (\<lambda>(uid, (from, dest), t). if uid = tID then (uid, (from, dest), t') else (uid, (from, dest), t)) (T e), F = F e\<rparr>"

definition all_regs :: "i_efsm \<Rightarrow> nat set" where
  "all_regs e = \<Union> (image (\<lambda>(_, _, t). enumerate_registers t) (fset (T e)))"

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

definition "satisfiable_list l = satisfiable (fold gAnd l (gexp.Bc True))"

fun fold_into :: "nat \<Rightarrow> gexp list \<Rightarrow> gexp list" where
  "fold_into n [] = [gNot (gexp.Null (V (I n)))]" |
  "fold_into n ((gexp.Eq (V (I i)) (L l))#t) = (if i = n then (gexp.Eq (V (I i)) (L l))#t else (gexp.Eq (V (I i)) (L l))#(fold_into n t))" |
  "fold_into n ((gexp.In (I i) l)#t) = (if i = n then (gexp.In (I i) l)#t else (gexp.In (I i) l)#(fold_into n t))" |
  "fold_into n (h#t) = h#(fold_into n t)"

primrec smart_not_null :: "nat list \<Rightarrow> gexp list \<Rightarrow> gexp list" where
  "smart_not_null [] g = g" |
  "smart_not_null (h#t) g = fold_into h (smart_not_null t g)"

lemma fold_into_supset: "set (fold_into a g) \<supseteq> set g"
  by(induct g rule: fold_into.induct, auto)

lemma fold_into_gNot_or_not: "fold_into a g = g \<or> fold_into a g = g@[(gNot (gexp.Null (V (I a))))]"
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

lemma fold_into_not_null: "apply_guards (fold_into a g) s \<Longrightarrow> gval (gNot (gexp.Null (V (I a)))) s = true"
  apply (insert fold_into_gNot_or_not[of a g])
  apply (case_tac "fold_into a g = g @ [gNot (gexp.Null (V (I a)))]")
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
  "apply_guards (smart_not_null l g) s \<Longrightarrow> apply_guards (g @ map (\<lambda>i. gNot (gexp.Null (V (I i)))) l) s"
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

definition max_int :: "i_transition_matrix \<Rightarrow> int" where
  "max_int e = Max (insert 0 (EFSM.enumerate_ints (fimage snd e)))"

definition max_int_2 :: "i_efsm \<Rightarrow> i_efsm \<Rightarrow> int" where
  "max_int_2 e1 e2 = Max (insert 0 (EFSM.enumerate_ints (fimage snd (T e1 |\<union>| T e2))))"

fun literal_args :: "gexp \<Rightarrow> bool" where
  "literal_args (gexp.Bc v) = False" |
  "literal_args (gexp.Eq (V _) (L _)) = True" |
  "literal_args (gexp.In _ _) = True" |
  "literal_args (gexp.Eq _ _) = False" |
  "literal_args (gexp.Gt va v) = False" |
  "literal_args (gexp.Null v) = False" |
  "literal_args (gexp.Nor v va) = (literal_args v \<and> literal_args va)"

lemma literal_args_eq: "literal_args (gexp.Eq a b) \<Longrightarrow> \<exists>v l. a = (V v) \<and> b = (L l)"
  apply (cases a)
     apply simp
    apply (cases b)
  by auto
end
