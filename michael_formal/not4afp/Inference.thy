theory Inference
  imports "../EFSM" "../Contexts" Transition_Ordering Prod_Linorder
begin

definition replace_state :: "'s \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's" where
  "replace_state s orig new = (if s = orig then new else s)"

definition merge_with :: "'s \<Rightarrow> 's \<Rightarrow> 's list" where
  "merge_with x y = (if x = y then [x] else [x, y])"

primrec pairs :: "'s \<Rightarrow> 's list \<Rightarrow> 's::finite transition_function \<Rightarrow> transition fset" where
  "pairs x [] _ = {||}" |
  "pairs x (h#hs) t = (t (x, h)) |\<union>| (pairs x hs t)"

primrec all_pairs :: "'s list \<Rightarrow> 's list \<Rightarrow> 's::finite transition_function \<Rightarrow> transition fset" where
  "all_pairs [] x _ = {||}" |
  "all_pairs (h#hs) x t = (pairs h x t) |\<union>| (all_pairs hs x t)"

definition merge_states :: "'s \<Rightarrow> 's \<Rightarrow> 's::finite transition_function \<Rightarrow> 's::finite transition_function" where
  "merge_states x y t = (if x = y then t else (\<lambda>(from, to). if from = y \<or> to = y then {||} 
                                      else (all_pairs (if from = x \<or> from = y then merge_with x y else [from])
                                                      (if to = x \<or> to = y then merge_with x y else [to]) t)))"

(* declare[[show_types,show_sorts]] *)

definition choice :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "choice t t' = ((Label t) = (Label t') \<and> (Arity t) = (Arity t') \<and> (\<exists> s. apply_guards (Guard t) s \<and> apply_guards (Guard t') s))"

lemma choice_symmetry: "choice x y = choice y x"
  using choice_def by auto

definition nondeterministic_pairs :: "'s::finite transition_function \<Rightarrow> ('s \<times> ('s \<times> 's) \<times> (transition \<times> transition)) set" where
  "nondeterministic_pairs t = {(origin, (dest1, dest2), (t1, t2)). t1 |\<in>| t (origin, dest1) \<and> t2 |\<in>| t (origin, dest2) \<and> t1 < t2 \<and> choice t1 t2}"

definition nondeterministic_transitions :: "'s::{finite,linorder} transition_function \<Rightarrow> ('s \<times> ('s \<times> 's) \<times> (transition \<times> transition)) option" where
  "nondeterministic_transitions t = (if nondeterministic_pairs t = {} then None else Some (Max (nondeterministic_pairs t)))"

definition nondeterminism :: "'s::finite transition_function \<Rightarrow> bool" where
  "nondeterminism t = (nondeterministic_pairs t \<noteq> {})"

definition replace_transition :: "'s::finite transition_function \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> transition fset \<Rightarrow> transition \<Rightarrow> 's::finite transition_function" where
  "replace_transition t from to orig new = (\<lambda>x. if x = (from, to) then (t x |-| orig) |\<union>| {|new|} else t x)"
                                                                                                                              
definition defined :: "'s::finite transition_function \<Rightarrow> ('s \<times> 's) set" where
  "defined t = {x. t x \<noteq> {||}}"

primrec alreadyUpdated :: "updates \<Rightarrow> vname \<Rightarrow> bool" where
  "alreadyUpdated [] _ = False" |
  "alreadyUpdated (h#t) r = (if fst h = r then True else alreadyUpdated t r)"

(* function modifyUpdates :: "'s::finite transition_function \<Rightarrow> context \<Rightarrow> 's::finite transition_function option" where
    "modifyUpdates t c = 
        Get all the transitions which go into a state
        For each one, see if there's a transition which subsumes it and produces the posterior context c for ALL inputs
        If there is, good job!
        If there isn't, fail
    
*)

definition hilbert_option :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option" where
  "hilbert_option f = (if {x. f x} = {} then None else Some (Eps f))"

fun make_context :: "'s::finite efsm \<Rightarrow> context \<Rightarrow> 's \<Rightarrow> 's::finite transition_function option" where
  "make_context e c s = (if \<exists>p. posterior_sequence (transition_trace e (s0 e) <> p) empty = c \<and> last (state_trace e (s0 e) <> p) = s
                  then Some (T e)
                  \<comment> \<open> else if it is possible to modify the update functions of incoming transitions
                     to get the right context then do that \<close>
                  else None)"

lemma make_context_options: "make_context e c s = None \<or> (\<exists>t. make_context e c s = Some t)"
  by simp

primrec gets_us_to :: "'statename::finite \<Rightarrow> 'statename efsm \<Rightarrow> 'statename \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> bool" where
  "gets_us_to target _ s _ [] = (s = target)" |
  "gets_us_to target e s r (h#t) =
    (case (step e s r (fst h) (snd h)) of
      (Some (_, s', _, r')) \<Rightarrow> gets_us_to target e s' r' t |
      _ \<Rightarrow> (s = target)
    )"

definition anterior_context :: "'s::finite efsm \<Rightarrow> trace \<Rightarrow> context" where
 "anterior_context e p = posterior_sequence (transition_trace e (s0 e) <> p) empty"

(* Does t1 subsume t2 in all possible anterior contexts? *)
(* For every path which gets us to the problem state, does t1 subsume t2 in the resulting context *)
definition directly_subsumes :: "'s::finite efsm \<Rightarrow> 's \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> bool" where
  "directly_subsumes e s t1 t2 = (\<forall>p. (gets_us_to s e (s0 e) <>  p) \<longrightarrow> subsumes (anterior_context e p) t1 t2)"

fun merge_transitions :: "'s::finite efsm \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> 's transition_function option" where
  "merge_transitions e from to1 to2 t1 t2 = (
    \<comment> \<open> If t1 directly subsumes t2 then replace t2 with t1 \<close>
    if directly_subsumes e from t1 t2 then Some (replace_transition (T e) from to2 {|t2|} t1) else
    \<comment> \<open> If t2 directly subsumes t1 then replace t1 with t2 \<close>
    if directly_subsumes e from t2 t1 then Some (replace_transition (T e) from to1 {|t1|} t2) else
    \<comment> \<open> Can we get a context where one transition subsumes the other directly \<close>
    \<comment> \<open> Can we make a transition which subsumes both? \<close>
    None
  )"

(* The number of states decreases down to one then either we can merge all of the transitons or we can't *)
function merge :: "'s::{finite, linorder} efsm \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's transition_function option" where
  "merge e s1 s2 = (let t' = (merge_states s1 s2 (T e)) in
                       \<comment> \<open> Have we got any nondeterminism? \<close>
                       (case nondeterministic_transitions t' of
                         \<comment> \<open> If not then we're good to go \<close>
                         None \<Rightarrow> Some t' |
                         \<comment> \<open> If we have then we need to fix it \<close>
                         Some (from, (to1, to2), (t1, t2)) \<Rightarrow> (if s1 \<noteq> s2 then merge \<lparr>s0 = s0 e, T = t'\<rparr> to1 to2 else
                            \<comment> \<open> Can we get a context where one transition subsumes the other directly \<close>
                            case (hilbert_option (\<lambda>c'. (subsumes c' t1 t2 \<or> subsumes c' t2 t1) \<and> make_context e c' (s0 e) \<noteq> None)) of
                              Some c' \<Rightarrow> make_context e c' (s0 e) |
                                      \<comment> \<open> Can we make a transition which subsumes both? \<close>
                              None \<Rightarrow> (case (hilbert_option (\<lambda>(c', tr). subsumes c' tr t1 \<and> subsumes c' tr t2)) of
                                          Some (c', tr) \<Rightarrow> Some (replace_transition t' from to1 {|t1|} tr) |
                                          None \<Rightarrow> None
                                        )
                        )
                      )
                    )"
  by auto

termination
  apply standard
   apply auto[1]
  apply (simp add: nondeterministic_transitions_def)
  apply (case_tac "nondeterministic_pairs (merge_states s1 s2 (T e)) = {}")
   apply simp
  apply simp
  apply (case_tac x2)
  apply simp
  sorry
  
end
