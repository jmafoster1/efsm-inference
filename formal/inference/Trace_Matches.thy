theory Trace_Matches
imports Inference
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

definition get_intratrace_matches :: "execution \<Rightarrow> (index \<times> index) fset" where
  "get_intratrace_matches e = Abs_fset {(a, b). lookup a e = lookup b e \<and> eventNum a \<le> eventNum b}"

primrec index :: "value list \<Rightarrow> nat \<Rightarrow> ioTag \<Rightarrow> nat \<Rightarrow> index fset" where
  "index [] _ _ _ = {||}" |
  "index (h#t) eventNo io ind = finsert (eventNo, io, ind) (index t eventNo io (ind + 1))"

definition io_index :: "nat \<Rightarrow> value list \<Rightarrow> value list \<Rightarrow> index fset" where
  "io_index eventNo inputs outputs = (index inputs eventNo In 0) |\<union>| (index outputs eventNo Out 0)"

definition indices :: "execution \<Rightarrow> index fset" where
  "indices e = foldl (|\<union>|) {||} (map (\<lambda>(eventNo, (label, inputs, outputs)). io_index eventNo inputs outputs) (enumerate 0 e))"

definition get_intratrace_matches_alt :: "execution \<Rightarrow> (index \<times> index) fset" where
  "get_intratrace_matches_alt e = ffilter (\<lambda>(a, b). lookup a e = lookup b e \<and> eventNum a \<le> eventNum b \<and> a \<noteq> b) (indices e |\<times>| indices e)"

lemma get_intratrace_matches_preproces:  "get_intratrace_matches_alt e = ffilter (\<lambda>(a, b). lookup a e = lookup b e) (ffilter (\<lambda>(a, b). eventNum a \<le> eventNum b \<and> a \<noteq> b) (indices e |\<times>| indices e))"
  apply (simp add: get_intratrace_matches_alt_def)
  apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse fprod_def)
  apply (simp add: Set.filter_def)
  by auto

primrec get_all_intratrace_matches :: "log \<Rightarrow> (index \<times> index) fset list" where
  "get_all_intratrace_matches [] = []" |
  "get_all_intratrace_matches (h#t) = (get_intratrace_matches h)#(get_all_intratrace_matches t)"

primrec get_all_intratrace_matches_alt :: "log \<Rightarrow> (index \<times> index) fset list" where
  "get_all_intratrace_matches_alt [] = []" |
  "get_all_intratrace_matches_alt (h#t) = (get_intratrace_matches_alt h)#(get_all_intratrace_matches_alt t)"

(* 
  To detect all intertrace matches, walk the trace in the current machine and replace eventNo with
  the corresponding transition's uid. If the uids match then there's an intertrace match.
*)

definition i_possible_steps :: "iEFSM \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (nat \<times> nat \<times> transition) fset" where
  "i_possible_steps e s r l i = fimage (\<lambda>(uid, (origin, dest), t). (uid, dest, t)) (ffilter (\<lambda>(uid, (origin, dest::nat), t::transition). origin = s \<and> (Label t) = l \<and> (length i) = (Arity t) \<and> apply_guards (Guard t) (join_ir i r)) e)"


definition i_step :: "iEFSM \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (transition \<times> nat \<times> nat \<times> datastate) option" where
"i_step e s r l i = (if size (i_possible_steps e s r l i) = 1 then (
                     let (u, s', t) = (fthe_elem (i_possible_steps e s r l i)) in
                     Some (t, s', u, (EFSM.apply_updates (Updates t) (join_ir i r) r))
                   )
                   else None)"

type_synonym match = "(((transition \<times> nat) \<times> ioTag \<times> nat) \<times> ((transition \<times> nat) \<times> ioTag \<times> nat))"

primrec (nonexhaustive) walk_up_to :: "nat \<Rightarrow> iEFSM \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> execution \<Rightarrow> (transition \<times> nat)" where
  "walk_up_to n e s r (h#t) =
    (case (i_step e s r (fst h) (fst (snd h))) of
      (Some (transition, s', uid, updated)) \<Rightarrow> (case n of 0 \<Rightarrow> (transition, uid) | Suc m \<Rightarrow> walk_up_to m e s' updated t)
    )"

definition find_intertrace_matches_aux :: "(index \<times> index) fset \<Rightarrow> iEFSM \<Rightarrow> execution \<Rightarrow> match fset" where
  "find_intertrace_matches_aux intras e t = fimage (\<lambda>((e1, io1, inx1), (e2, io2, inx2)). (((walk_up_to e1 e 0 <> t), io1, inx1), ((walk_up_to e2 e 0 <> t), io2, inx2))) intras" 

definition find_intratrace_matches :: "log \<Rightarrow> iEFSM \<Rightarrow> match list" where
  "find_intratrace_matches l e = filter (\<lambda>((e1, io1, inx1), (e2, io2, inx2)). e1 \<noteq> e2) (concat (map (\<lambda>(t, m). sorted_list_of_fset (find_intertrace_matches_aux m e t)) (zip l (get_all_intratrace_matches_alt l))))"

definition get :: "iEFSM \<Rightarrow> nat \<Rightarrow> transition" where
  "get e u = snd (snd (fthe_elem (ffilter (\<lambda>(uid, _). uid = u) e)))"

fun get_aexp_biggest_reg :: "aexp \<Rightarrow> nat" where
  "get_aexp_biggest_reg (L _) = 0" |
  "get_aexp_biggest_reg (V (R n)) = n" |
  "get_aexp_biggest_reg (V (I _)) = 0" |
  "get_aexp_biggest_reg (Plus a1 a2) = max (get_aexp_biggest_reg a1) (get_aexp_biggest_reg a2)" |
  "get_aexp_biggest_reg (Minus a1 a2) = max (get_aexp_biggest_reg a1) (get_aexp_biggest_reg a2)"

fun get_gexp_biggest_reg :: "gexp \<Rightarrow> nat" where
  "get_gexp_biggest_reg (gexp.Bc _) = 0" |
  "get_gexp_biggest_reg (gexp.Eq a1 a2) = max (get_aexp_biggest_reg a1) (get_aexp_biggest_reg a2)" |
  "get_gexp_biggest_reg (gexp.Gt a1 a2) = max (get_aexp_biggest_reg a1) (get_aexp_biggest_reg a2)" |
  "get_gexp_biggest_reg (gexp.Nor g1 g2) = max (get_gexp_biggest_reg g1) (get_gexp_biggest_reg g2)" |
  "get_gexp_biggest_reg (gexp.Null (R n)) = n" |
  "get_gexp_biggest_reg (gexp.Null (I n)) = 0"

definition get_biggest_t_reg :: "transition \<Rightarrow> nat" where
  "get_biggest_t_reg t = (let s = (fset_of_list ((map get_gexp_biggest_reg (Guard t))@ (map (\<lambda>(_, a). get_aexp_biggest_reg a) (Updates t)))) in 
                          if s = {||} then 0 else fMax s)"

definition new_reg :: "iEFSM \<Rightarrow> nat" where
  "new_reg e = (fMax (fimage (\<lambda>(_, (_, _), t). get_biggest_t_reg t) e)) + 1"

definition "guard_filter inputX = (\<lambda>g. \<nexists>a. g = gexp.Eq (V (I inputX)) a \<or> g = gexp.Eq a (V (I inputX)))"
declare guard_filter_def [simp]

definition remove_guard_add_update :: "transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition" where
  "remove_guard_add_update t inputX outputX = \<lparr>Label = (Label t), Arity = (Arity t), Guard = (filter (guard_filter inputX) (Guard t)), Outputs = (Outputs t), Updates = (R outputX, (V (I inputX)))#(Updates t)\<rparr>"

definition generalise_output :: "transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition" where
  "generalise_output t regX outputX = \<lparr>Label = (Label t), Arity = (Arity t), Guard = (Guard t), Outputs = list_update (Outputs t) outputX (V (R regX)), Updates = (Updates t)\<rparr>"

primrec count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count _ [] = 0" |
  "count a (h#t) = (if a = h then 1+(count a t) else count a t)"

definition replaceAll :: "iEFSM \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> iEFSM" where
  "replaceAll e old new = fimage (\<lambda>(uid, (from, to), t). if t = old then (uid, (from, to), new) else (uid, (from, to), t)) e"

primrec generalise_transitions :: "((((transition \<times> nat) \<times> ioTag \<times> nat) \<times>
     (transition \<times> nat) \<times> ioTag \<times> nat) \<times>
    ((transition \<times> nat) \<times> ioTag \<times> nat) \<times>
    (transition \<times> nat) \<times> ioTag \<times> nat) list \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "generalise_transitions [] e = e" |
  "generalise_transitions (h#t) e = (let ((((orig1, u1), _), (orig2, u2), _), (((gen1, u1'), _), (gen2, u2), _)) = h in
                                         generalise_transitions t (replaceAll (replaceAll e orig1 gen1) orig2 gen2))"

definition strip_uids :: "(((transition \<times> nat) \<times> ioTag \<times> nat) \<times> (transition \<times> nat) \<times> ioTag \<times> nat) \<Rightarrow> ((transition \<times> ioTag \<times> nat) \<times> (transition \<times> ioTag \<times> nat))" where
  "strip_uids x = (let (((t1, u1), io1, in1), (t2, u2), io2, in2) = x in ((t1, io1, in1), (t2, io2, in2)))"

definition modify :: "match list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> iEFSM \<Rightarrow> iEFSM option" where
  "modify matches u1 u2 old = (let relevant = filter (\<lambda>(((_, u1'), io, _), (_, u2'), io', _). io = In \<and> io' = Out \<and> (u1 = u1' \<or> u2 = u1' \<or> u1 = u2' \<or> u2 = u2')) matches;
                                   newReg = new_reg old;
                                   replacements = map (\<lambda>(((t1, u1), io1, inx1), (t2, u2), io2, inx2). (((remove_guard_add_update t1 (inx1+1) newReg, u1), io1, inx1), (generalise_output t2 newReg inx2, u2), io2, inx2)) relevant;
                                   comparisons = zip relevant replacements;
                                   stripped_replacements = map strip_uids replacements;
                                   to_replace = filter (\<lambda>(_, s). count (strip_uids s) stripped_replacements > 1) comparisons in
                                if to_replace = [] then None else Some (generalise_transitions to_replace old)
                              )"

(* type_synonym update_modifier = "transition \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> (iEFSM \<times> (nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> nat)) option" *)
definition heuristic_1 :: "log \<Rightarrow> update_modifier" where
  "heuristic_1 l = (\<lambda>t1 t2 s new old. modify (find_intratrace_matches l old) t1 t2 old)"
end                                                   