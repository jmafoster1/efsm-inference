theory Store_Reuse
imports "../Inference"
begin
datatype ioTag = In | Out

instantiation ioTag :: linorder begin
fun less_ioTag :: "ioTag \<Rightarrow> ioTag \<Rightarrow> bool" where
  "In < Out = True" |
  "Out < _ = False" |
  "In < In = False"

definition less_eq_ioTag :: "ioTag \<Rightarrow> ioTag \<Rightarrow> bool" where
  "less_eq_ioTag x y = (x < y \<or> x = y)"
declare less_eq_ioTag_def [simp]

instance
  apply standard
  using less_ioTag.elims(2) apply fastforce
     apply simp
    apply (metis ioTag.exhaust less_eq_ioTag_def)
  using less_eq_ioTag_def less_ioTag.elims(2) apply blast
  by (metis (full_types) ioTag.exhaust less_eq_ioTag_def less_ioTag.simps(1))
end

type_synonym index = "nat \<times> ioTag \<times> nat"

fun lookup :: "index \<Rightarrow> execution \<Rightarrow> value" where
  "lookup (eventNo, In, inx) t = (let (_, inputs, _) = nth t eventNo in nth inputs inx)" |
  "lookup (eventNo, Out, inx) t = (let (_, _, outputs) = nth t eventNo in nth outputs inx)"

abbreviation eventNum :: "index \<Rightarrow> nat" where
  "eventNum i \<equiv> fst i"

abbreviation ioTag :: "index \<Rightarrow> ioTag" where
  "ioTag i \<equiv> fst (snd i)"

abbreviation inx :: "index \<Rightarrow> nat" where
  "inx i \<equiv> snd (snd i)"

primrec index :: "value list \<Rightarrow> nat \<Rightarrow> ioTag \<Rightarrow> nat \<Rightarrow> index fset" where
  "index [] _ _ _ = {||}" |
  "index (h#t) eventNo io ind = finsert (eventNo, io, ind) (index t eventNo io (ind + 1))"

definition io_index :: "nat \<Rightarrow> value list \<Rightarrow> value list \<Rightarrow> index fset" where
  "io_index eventNo inputs outputs = (index inputs eventNo In 0) |\<union>| (index outputs eventNo Out 0)"

definition indices :: "execution \<Rightarrow> index fset" where
  "indices e = foldl (|\<union>|) {||} (map (\<lambda>(eventNo, (label, inputs, outputs)). io_index eventNo inputs outputs) (enumerate 0 e))"

definition get_by_id_intratrace_matches :: "execution \<Rightarrow> (index \<times> index) fset" where
  "get_by_id_intratrace_matches e = ffilter (\<lambda>(a, b). lookup a e = lookup b e \<and> eventNum a \<le> eventNum b \<and> a \<noteq> b) (indices e |\<times>| indices e)"

(*
  If the EFSM is nondeterministic, we need to make sure it chooses the right path so that it accepts
  the input trace.
*)
definition i_step :: "trace \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (transition \<times> cfstate \<times> tids \<times> registers) option" where
  "i_step tr e s r l i = (let 
    poss_steps = (i_possible_steps e s r l i);
    possibilities = ffilter (\<lambda>(u, s', t). accepts (tm e) s' (apply_updates (Updates t) (join_ir i r) r) tr) poss_steps in
    case random_member possibilities of
      None \<Rightarrow> None |
      Some (u, s', t) \<Rightarrow>
      Some (t, s', u, (apply_updates (Updates t) (join_ir i r) r))
  )"

type_synonym match = "(((transition \<times> tids) \<times> ioTag \<times> nat) \<times> ((transition \<times> tids) \<times> ioTag \<times> nat))"

definition "exec2trace t = map (\<lambda>(label, inputs, _). (label, inputs)) t"
primrec (nonexhaustive) walk_up_to :: "nat \<Rightarrow> iEFSM \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> (transition \<times> tids)" where
  "walk_up_to n e s r (h#t) =
    (case (i_step (exec2trace t) e s r (fst h) (fst (snd h))) of
      (Some (transition, s', uid, updated)) \<Rightarrow> (case n of 0 \<Rightarrow> (transition, uid) | Suc m \<Rightarrow> walk_up_to m e s' updated t)
    )"

definition find_intertrace_matches_aux :: "(index \<times> index) fset \<Rightarrow> iEFSM \<Rightarrow> execution \<Rightarrow> match fset" where
  "find_intertrace_matches_aux intras e t = fimage (\<lambda>((e1, io1, inx1), (e2, io2, inx2)). (((walk_up_to e1 e 0 <> t), io1, inx1), ((walk_up_to e2 e 0 <> t), io2, inx2))) intras" 

definition find_intertrace_matches :: "log \<Rightarrow> iEFSM \<Rightarrow> match list" where
  "find_intertrace_matches l e = filter (\<lambda>((e1, io1, inx1), (e2, io2, inx2)). e1 \<noteq> e2) (concat (map (\<lambda>(t, m). sorted_list_of_fset (find_intertrace_matches_aux m e t)) (zip l (map get_by_id_intratrace_matches l))))"

definition total_max_input :: "iEFSM \<Rightarrow> nat" where
  "total_max_input e = (case EFSM.max_input (tm e) of None \<Rightarrow> 0 | Some i \<Rightarrow> i)"

definition total_max_reg :: "iEFSM \<Rightarrow> nat" where
  "total_max_reg e = (case EFSM.max_reg (tm e) of None \<Rightarrow> 0 | Some i \<Rightarrow> i)"

definition remove_guard_add_update :: "transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition" where
  "remove_guard_add_update t inputX outputX = \<lparr>
    Label = (Label t), Arity = (Arity t),
    Guard = (filter (\<lambda>g. \<not> gexp_constrains g (V (vname.I inputX))) (Guard t)),
    Outputs = (Outputs t),
    Updates = (outputX, (V (vname.I inputX)))#(Updates t)
  \<rparr>"

definition generalise_output :: "transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition" where
  "generalise_output t regX outputX = \<lparr>
      Label = (Label t),
      Arity = (Arity t),
      Guard = (Guard t),
      Outputs = list_update (Outputs t) outputX (V (R regX)),
      Updates = (Updates t)
    \<rparr>"

definition is_generalised_output_of :: "transition \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "is_generalised_output_of t' t r p = (t' = generalise_output t r p)"

primrec count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count _ [] = 0" |
  "count a (h#t) = (if a = h then 1+(count a t) else count a t)"

definition replaceAll :: "iEFSM \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> iEFSM" where
  "replaceAll e old new = fimage (\<lambda>(uid, (from, dest), t). if t = old then (uid, (from, dest), new) else (uid, (from, dest), t)) e"

primrec generalise_transitions ::
  "((((transition \<times> tids) \<times> ioTag \<times> nat) \<times> (transition \<times> tids) \<times> ioTag \<times> nat) \<times>
     ((transition \<times> tids) \<times> ioTag \<times> nat) \<times> (transition \<times> tids) \<times> ioTag \<times> nat) list \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "generalise_transitions [] e = e" |
  "generalise_transitions (h#t) e = (let
    ((((orig1, u1), _), (orig2, u2), _), (((gen1, u1'), _), (gen2, u2), _)) = h in
   generalise_transitions t (replaceAll (replaceAll e orig1 gen1) orig2 gen2))"

definition strip_uids :: "(((transition \<times> tids) \<times> ioTag \<times> nat) \<times> (transition \<times> tids) \<times> ioTag \<times> nat) \<Rightarrow> ((transition \<times> ioTag \<times> nat) \<times> (transition \<times> ioTag \<times> nat))" where
  "strip_uids x = (let (((t1, u1), io1, in1), (t2, u2), io2, in2) = x in ((t1, io1, in1), (t2, io2, in2)))"

definition modify :: "match list \<Rightarrow> tids \<Rightarrow> tids \<Rightarrow> iEFSM \<Rightarrow> iEFSM option" where
  "modify matches u1 u2 old = (let relevant = filter (\<lambda>(((_, u1'), io, _), (_, u2'), io', _). io = In \<and> io' = Out \<and> (u1 = u1' \<or> u2 = u1' \<or> u1 = u2' \<or> u2 = u2')) matches;
                                   newReg = case max_reg old of None \<Rightarrow> 1 | Some r \<Rightarrow> r + 1;
                                   replacements = map (\<lambda>(((t1, u1), io1, inx1), (t2, u2), io2, inx2). (((remove_guard_add_update t1 inx1 newReg, u1), io1, inx1), (generalise_output t2 newReg inx2, u2), io2, inx2)) relevant;
                                   comparisons = zip relevant replacements;
                                   stripped_replacements = map strip_uids replacements;
                                   to_replace = filter (\<lambda>(_, s). count (strip_uids s) stripped_replacements > 1) comparisons in
                                if to_replace = [] then None else Some ((generalise_transitions to_replace old))
                              )"

(* type_synonym update_modifier = "transition \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> (iEFSM \<times> (nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> nat)) option" *)
definition heuristic_1 :: "log \<Rightarrow> update_modifier" where
  "heuristic_1 l = (\<lambda>t1 t2 s new old np. let newEFSMopt = (modify (find_intertrace_matches l old) t1 t2 new) in
                                      case newEFSMopt of None \<Rightarrow> None |
                                                      Some newEFSM \<Rightarrow> resolve_nondeterminism [] (sorted_list_of_fset (np newEFSM)) old newEFSM null_modifier (\<lambda>a. True) np)"

lemma remove_guard_add_update_preserves_outputs: "Outputs (remove_guard_add_update t i r) = Outputs t"
  by (simp add: remove_guard_add_update_def)

lemma remove_guard_add_update_preserves_label: "Label (remove_guard_add_update t i r) = Label t"
  by (simp add: remove_guard_add_update_def)

lemma remove_guard_add_update_preserves_arity: "Arity (remove_guard_add_update t i r) = Arity t"
  by (simp add: remove_guard_add_update_def)

lemmas remove_guard_add_update_preserves = remove_guard_add_update_preserves_label
                                           remove_guard_add_update_preserves_arity
                                           remove_guard_add_update_preserves_outputs

definition is_generalisation_of :: "transition \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "is_generalisation_of t' t i r = (t' = remove_guard_add_update t i r \<and> 
                                    i < Arity t \<and>
                                    (\<exists>v. Eq (V (vname.I i)) (L v) \<in> set (Guard t)) \<and>
                                    r \<notin> set (map fst (Updates t)))"

lemma generalise_output_preserves_label: "Label (generalise_output t r p) = Label t"
  by (simp add: generalise_output_def)

lemma generalise_output_preserves_arity: "Arity (generalise_output t r p) = Arity t"
  by (simp add: generalise_output_def)

lemma generalise_output_preserves_guard: "Guard (generalise_output t r p) = Guard t"
  by (simp add: generalise_output_def)

lemma generalise_output_preserves_output_length: "length (Outputs (generalise_output t r p)) = length (Outputs t)"
  by (simp add: generalise_output_def)

lemma generalise_output_preserves_updates: "Updates (generalise_output t r p) = Updates t"
  by (simp add: generalise_output_def)

lemmas generalise_output_preserves = generalise_output_preserves_label
                                     generalise_output_preserves_arity
                                     generalise_output_preserves_output_length
                                     generalise_output_preserves_guard
                                     generalise_output_preserves_updates

definition is_proper_generalisation_of :: "transition \<Rightarrow> transition \<Rightarrow> iEFSM \<Rightarrow> bool" where
 "is_proper_generalisation_of t' t e = (\<exists>i \<le> total_max_input e. \<exists> r \<le> total_max_reg e.
                                        is_generalisation_of t' t i r \<and>
                                        (\<forall>u \<in> set (Updates t). fst u \<noteq> r) \<and>
                                        (\<forall>i \<le> max_input (tm e). \<forall>u \<in> set (Updates t). fst u \<noteq> r)
                                       )"

(* Recognising the same input used in multiple guards *)
definition generalise_input :: "transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition" where
  "generalise_input t r i = \<lparr>
      Label = Label t,
      Arity = Arity t,
      Guard = map (\<lambda>g. case g of Eq (V (I i')) (L _) \<Rightarrow> if i = i' then Eq (V (I i)) (V (R r)) else g | _ \<Rightarrow> g) (Guard t),
      Outputs = Outputs t,
      Updates = Updates t
    \<rparr>"

fun structural_count :: "((transition \<times> ioTag \<times> nat) \<times> (transition \<times> ioTag \<times> nat)) \<Rightarrow> ((transition \<times> ioTag \<times> nat) \<times> (transition \<times> ioTag \<times> nat)) list \<Rightarrow> nat" where
  "structural_count _ [] = 0" |
  "structural_count a (((t1', io1', i1'), (t2', io2', i2'))#t) = (
    let ((t1, io1, i1), (t2, io2, i2)) = a in
    if same_structure t1 t1' \<and> same_structure t2 t2' \<and>
       io1 = io1' \<and> io2 = io2' \<and>
       i1 = i1' \<and> i2 = i2'
    then
      1+(structural_count a t)
    else
      structural_count a t
    )"

definition remove_guards_add_update :: "transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition" where
  "remove_guards_add_update t inputX outputX = \<lparr>
    Label = (Label t), Arity = (Arity t),
    Guard = [],
    Outputs = (Outputs t),
    Updates = (outputX, (V (vname.I inputX)))#(Updates t)
  \<rparr>"

definition modify_2 :: "match list \<Rightarrow> tids \<Rightarrow> tids \<Rightarrow> iEFSM \<Rightarrow> iEFSM option" where
  "modify_2 matches u1 u2 old = (let relevant = filter (\<lambda>(((_, u1'), io, _), (_, u2'), io', _). io = In \<and> io' = In \<and> (u1 = u1' \<or> u2 = u1' \<or> u1 = u2' \<or> u2 = u2')) matches;
                                   newReg = case max_reg old of None \<Rightarrow> 1 | Some r \<Rightarrow> r + 1;
                                   replacements = map (\<lambda>(((t1, u1), io1, inx1), (t2, u2), io2, inx2).
                                                  (((remove_guards_add_update t1 inx1 newReg, u1), io1, inx1),
                                                    (generalise_input t2 newReg inx2, u2), io2, inx2)) relevant;
                                   comparisons = zip relevant replacements;
                                   stripped_replacements = map strip_uids replacements;
                                   to_replace = filter (\<lambda>(_, s). structural_count (strip_uids s) stripped_replacements > 1) comparisons in
                                if to_replace = [] then None else Some ((generalise_transitions to_replace old))
                              )"

(* type_synonym update_modifier = "transition \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> (iEFSM \<times> (nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> nat)) option" *)
definition heuristic_2 :: "log \<Rightarrow> update_modifier" where
  "heuristic_2 l = (\<lambda>t1 t2 s new old np. let newEFSMopt = (modify_2 (find_intertrace_matches l old) t1 t2 new) in
                                      case newEFSMopt of None \<Rightarrow> None |
                                                      Some newEFSM \<Rightarrow> resolve_nondeterminism [] (sorted_list_of_fset (nondeterministic_pairs newEFSM)) old newEFSM null_modifier (\<lambda>a. True) np)"
hide_const ioTag.In

end                                                   