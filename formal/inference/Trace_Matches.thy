theory Trace_Matches
imports Inference
begin
datatype ioTag = In | Out
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

definition possible_steps :: "iEFSM \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (nat \<times> nat \<times> transition) fset" where
  "possible_steps e s r l i = fimage (\<lambda>(uid, (origin, dest), t). (uid, dest, t)) (ffilter (\<lambda>(uid, (origin, dest::nat), t::transition). origin = s \<and> (Label t) = l \<and> (length i) = (Arity t) \<and> apply_guards (Guard t) (join_ir i r)) e)"


definition step :: "iEFSM \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (transition \<times> nat \<times> nat \<times> datastate) option" where
"step e s r l i = (if fis_singleton (possible_steps e s r l i) then (
                     let (u, s', t) = (fthe_elem (possible_steps e s r l i)) in
                     Some (t, s', u, (EFSM.apply_updates (Updates t) (join_ir i r) r))
                   )
                   else None)"

fun walk_up_to :: "nat \<Rightarrow> iEFSM \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> nat option" where
  "walk_up_to _ _ _ _ [] = None" |
  "walk_up_to 0 e s r (h#t) =
    (case (step e s r (fst h) (snd h)) of
      (Some (transition, s', uid, updated)) \<Rightarrow> Some uid |
      _ \<Rightarrow> None
    )"|
  "walk_up_to n e s r (h#t) =
    (case (step e s r (fst h) (snd h)) of
      (Some (transition, s', uid, updated)) \<Rightarrow> walk_up_to (n-1) e s' updated t |
      _ \<Rightarrow> None
    )"

definition find_intertrace_matches_aux :: "(index \<times> index) fset \<Rightarrow> (index \<times> index) fset" where
  "find_intertrace_matches_aux intras = fimage (\<lambda>((e1, io1, inx1), (e2, io2, inx2)). (walk_up_to e1)) intras" 
end