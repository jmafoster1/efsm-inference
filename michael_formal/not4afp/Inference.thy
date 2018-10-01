theory Inference
  imports "../EFSM" "../Contexts"
begin

type_synonym 'statename transition_function = "('statename \<times> 'statename) \<Rightarrow> transition set"
type_synonym 'statename transition_matrix = "(('statename \<times> 'statename) \<times> transition list) list"

definition merge_with :: "'s \<Rightarrow> 's \<Rightarrow> 's list" where
  "merge_with x y = (if x = y then [x] else [x, y])"

primrec pairs :: "'s \<Rightarrow> 's list \<Rightarrow> 's transition_function \<Rightarrow> transition set" where
  "pairs x [] _ = {}" |
  "pairs x (h#hs) t = (t (x, h)) \<union> (pairs x hs t)"

primrec all_pairs :: "'s list \<Rightarrow> 's list \<Rightarrow> 's transition_function \<Rightarrow> transition set" where
  "all_pairs [] x _ = {}" |
  "all_pairs (h#hs) x t = (pairs h x t) \<union> (all_pairs hs x t)"

definition merge_states :: "'s \<Rightarrow> 's \<Rightarrow> 's transition_function \<Rightarrow> 's transition_function" where
  "merge_states x y t = (\<lambda>(from, to). if from = y \<or> to = y then {} 
                                      else (all_pairs (if from = x \<or> from = y then merge_with x y else [from])
                                                      (if to = x \<or> to = y then merge_with x y else [to]) t))"

definition choice :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "choice t t' = ((Label t) = (Label t') \<and> (Arity t) = (Arity t') \<and> (\<exists> s. apply_guards (Guard t) s \<and> apply_guards (Guard t') s))"

definition nondeterministic_pairs :: "'s::linorder transition_function \<Rightarrow> (('s \<times> 's) \<times> (transition \<times> transition)) set" where
  "nondeterministic_pairs t = {((s1, s2), (t1, t2)). \<exists> s'. t1 \<in> t (s', s1) \<and> t2 \<in> t (s', s2) \<and> t1 \<noteq> t2 \<and> choice t1 t2}"

fun flatten_transitions :: "(('s \<times> 's) \<times> transition list) \<Rightarrow> ('s \<times> 's \<times> transition) list" where
  "flatten_transitions (_, []) = []" |
  "flatten_transitions ((from, to), (h#t)) = (from, to, h)#(flatten_transitions ((from, to), t))"

primrec flatten_transition_matrix :: "'s transition_matrix \<Rightarrow> ('s \<times> 's \<times> transition) list" where
  "flatten_transition_matrix [] = []" |
  "flatten_transition_matrix (h#t) = (flatten_transitions h)@(flatten_transition_matrix t)"

definition lst_nondeterministic_pairs :: "'s::linorder transition_function \<Rightarrow> (('s \<times> 's) \<times> (transition \<times> transition)) list" where
  "lst_nondeterministic_pairs t = [((s1, s2), (t1, t2)). \<exists> s'. t1 \<in> t (s', s1) \<and> t2 \<in> t (s', s2) \<and> t1 \<noteq> t2 \<and> choice t1 t2]"

definition nondeterminism :: "'s::linorder transition_function \<Rightarrow> bool" where
  "nondeterminism t = (nondeterministic_pairs t \<noteq> {})"

definition merge_transitions :: "context \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> transition option" where
  "merge_transitions c t1 t2 = (if subsumes c t1 t2 then Some t1 else
                             if subsumes c t2 t1 then Some t2 else None)"

definition merge :: "context \<Rightarrow> 's::linorder transition_matrix \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's transition_matrix" where
  "merge c t s1 s2 = (if (nondeterminism (merge_states s1 s2 t)) then 
                      case sorted_list_of_set (nondeterministic_pairs (merge_states s1 s2 t)) of
                      [] \<Rightarrow> t
                      else t)"

end
