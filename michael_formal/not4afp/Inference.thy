theory Inference
  imports "../EFSM" "../Contexts"
begin

type_synonym 'statename transition_function = "('statename \<times> 'statename) \<Rightarrow> transition set"
type_synonym 'statename transition_matrix = "(('statename \<times> 'statename) \<times> transition set) list"

primrec function_of_matrix :: "'s transition_matrix \<Rightarrow> 's transition_function" where
  "function_of_matrix [] = (\<lambda>x. {})" |
  "function_of_matrix (h#t) = (\<lambda>x. if x = (fst h) then snd h else (function_of_matrix t) x)"

definition replace_state :: "'s \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's" where
  "replace_state s orig new = (if s = orig then new else s)"

fun merge_states_matrix :: "'s \<Rightarrow> 's \<Rightarrow> 's transition_matrix \<Rightarrow> 's transition_matrix" where
  "merge_states_matrix _ _ [] = []" |
  "merge_states_matrix s1 s2 (((s, s'), t)#tail) = ((replace_state s s1 s2, replace_state s' s1 s2), t)#(merge_states_matrix s1 s2 tail)"

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


(* declare[[show_types,show_sorts]] *)

definition choice :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "choice t t' = ((Label t) = (Label t') \<and> (Arity t) = (Arity t') \<and> (\<exists> s. apply_guards (Guard t) s \<and> apply_guards (Guard t') s))"

definition nondeterministic_pairs :: "'s transition_function \<Rightarrow> ('s \<times> ('s \<times> 's) \<times> (transition \<times> transition)) set" where
  "nondeterministic_pairs t = {(s', (s1, s2), (t1, t2)). t1 \<in> t (s', s1) \<and> t2 \<in> t (s', s2) \<and> t1 \<noteq> t2 \<and> choice t1 t2}"

definition nondeterministic_transitions :: "'s transition_function \<Rightarrow> ('s \<times> ('s \<times> 's) \<times> (transition \<times> transition)) option" where
  "nondeterministic_transitions t = (if nondeterministic_pairs t = {} then None else Some (Eps (\<lambda> x. x \<in> nondeterministic_pairs t)))"

definition nondeterminism :: "'s transition_function \<Rightarrow> bool" where
  "nondeterminism t = (nondeterministic_pairs t \<noteq> {})"

definition merge_transitions :: "context \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> transition option" where
  "merge_transitions c t1 t2 = (if subsumes c t1 t2 then Some t1 else
                             if subsumes c t2 t1 then Some t2 else None)"

definition replace_transition :: "'s transition_function \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> transition set \<Rightarrow> transition \<Rightarrow> 's transition_function" where
  "replace_transition t from to orig new = (\<lambda>x. if x = (from, to) then (t x - orig) \<union> {new} else t x)"
                                                                                                                              
fun replace_transition_matrix :: "'s transition_matrix \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> transition set \<Rightarrow> transition \<Rightarrow> 's transition_matrix" where
  "replace_transition_matrix [] from to orig new = []" |
  "replace_transition_matrix ((x, t)#tt) from to orig new = (if x = (from, to) then (x, t-orig \<union> {new}) else (x, t))#(replace_transition_matrix tt from to orig new)"

definition defined :: "'s transition_function \<Rightarrow> ('s \<times> 's) set" where
  "defined t = {x. t x \<noteq> {}}"

function merge_matrix :: "context \<Rightarrow> 's transition_matrix \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's transition_matrix option" where
  "merge_matrix c t s1 s2 =  (let t' = (merge_states_matrix s1 s2 t) in
                       (case nondeterministic_transitions (function_of_matrix t') of
                        None \<Rightarrow> Some (merge_states_matrix s1 s2 t) |
                        Some (from, (to1, to2), (t1, t2)) \<Rightarrow> (if s1 = s2 then
                                                                if subsumes c t1 t2 then Some (replace_transition_matrix t' from to1 {t2} t1)
                                                                else if subsumes c t2 t1 then Some (replace_transition_matrix t' from to1 {t1} t2)
                                                                else None
                                                              else merge_matrix c t to1 to2)))"
  by auto
termination
  sorry

function merge :: "context \<Rightarrow> 's transition_function \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's transition_function option" where
  "merge c t s1 s2 = (if finite (defined t) then (let t' = (merge_states s1 s2 t) in
                       (case nondeterministic_transitions t' of
                        None \<Rightarrow> Some t' |
                        Some (from, (to1, to2), (t1, t2)) \<Rightarrow> (if s1 = s2 then
                                                                if subsumes c t1 t2 then Some (replace_transition t' from to1 {t2} t1)
                                                                else if subsumes c t2 t1 then Some (replace_transition t' from to1 {t1} t2)
                                                                else None
                                                              else merge c t to1 to2)))
                      else None)"
  by auto

lemma inf_term: "infinite (defined aa) \<Longrightarrow> merge a aa ab b = None"
  sorry

termination
  apply clarify
  apply (case_tac "infinite (defined aa)")
  sorry
  
end
