theory Trace_Matches
imports Inference
begin
datatype io = I | O
type_synonym index = "nat \<times> io \<times> nat"

fun lookup :: "index \<Rightarrow> execution \<Rightarrow> value" where
  "lookup (eventNo, I, inx) t = (let (_, inputs, _) = nth t eventNo in nth inputs inx)" |
  "lookup (eventNo, io.O, inx) t = (let (_, _, outputs) = nth t eventNo in nth outputs inx)"

abbreviation eventNum :: "index \<Rightarrow> nat" where
  "eventNum i \<equiv> fst i"

abbreviation io :: "index \<Rightarrow> io" where
  "io i \<equiv> fst (snd i)"

abbreviation inx :: "index \<Rightarrow> nat" where
  "inx i \<equiv> snd (snd i)"

definition get_intratrace_matches :: "execution \<Rightarrow> (index \<times> index) fset" where
  "get_intratrace_matches e = Abs_fset {(a, b). lookup a e = lookup b e \<and> eventNum a \<le> eventNum b}"

primrec get_all_intratrace_matches :: "log \<Rightarrow> (index \<times> index) fset list" where
  "get_all_intratrace_matches [] = []" |
  "get_all_intratrace_matches (h#t) = (get_intratrace_matches h)#(get_all_intratrace_matches t)"

(* 
  To detect all intertrace matches, walk the trace in the current machine and replace eventNo with
  the corresponding transition's uid. If the uids match then there's an intertrace match.
*)

end