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

definition modify :: "match list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> iEFSM \<Rightarrow> iEFSM option" where
  "modify matches u1 u2 old = (let relevant = filter (\<lambda>(((_, u1'), _, _), (_, u2'), _, _). u1 = u1' \<or> u2 = u1' \<or> u1 = u2' \<or> u2 = u2') matches in
                                None
                              )"
(*
Are either of the two transitions we're in in the list?
If they are, do we have a match?
*)
end