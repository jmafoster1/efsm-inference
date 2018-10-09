theory Inference
  imports "../EFSM" "../Contexts"
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

definition nondeterministic_pairs :: "'s::finite transition_function \<Rightarrow> ('s \<times> ('s \<times> 's) \<times> (transition \<times> transition)) set" where
  "nondeterministic_pairs t = {(s', (s1, s2), (t1, t2)). t1 |\<in>| t (s', s1) \<and> t2 |\<in>| t (s', s2) \<and> t1 \<noteq> t2 \<and> choice t1 t2}"

definition nondeterministic_transitions :: "'s::finite transition_function \<Rightarrow> ('s \<times> ('s \<times> 's) \<times> (transition \<times> transition)) option" where
  "nondeterministic_transitions t = (if nondeterministic_pairs t = {} then None else Some (Eps (\<lambda> x. x \<in> nondeterministic_pairs t)))"

definition nondeterminism :: "'s::finite transition_function \<Rightarrow> bool" where
  "nondeterminism t = (nondeterministic_pairs t \<noteq> {})"

definition merge_transitions :: "context \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> transition option" where
  "merge_transitions c t1 t2 = (if subsumes c t1 t2 then Some t1 else
                             if subsumes c t2 t1 then Some t2 else None)"

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
  "make_context e c s = (if \<exists>p. posterior_sequence (observe_transitions e (s0 e) <> p) empty = c \<and> last (state_trace e (s0 e) <> p) = s
                  then Some (T e)
                  (* else if it is possible to modify the update functions of incoming transitions
                     to get the right context then do that *)
                  else None)"

lemma make_context_options: "make_context e c s = None \<or> (\<exists>t. make_context e c s = Some t)"
  by simp

(* The number of states decreases down to one then either we can merge all of the transitons or we can't *)

function merge :: "'s::finite efsm \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's::finite transition_function option" where
  "merge e s1 s2 = (let t' = (merge_states s1 s2 (T e)) in
                       (* Have we got any nondeterminisms? *)
                       (case nondeterministic_transitions t' of
                         (* If not then we're good to go *)
                         None \<Rightarrow> Some t' |
                         (* If we have then we need to fix it *)
                         Some (from, (to1, to2), (t1, t2)) \<Rightarrow> (if s1 \<noteq> s2 then merge \<lparr>s0 = s0 e, T = t'\<rparr> to1 to2 else
                            (* Can we get a context where one transition subsumes the other directly *)
                            case (hilbert_option (\<lambda>c'. (subsumes c' t1 t2 \<or> subsumes c' t2 t1) \<and> make_context e c' (s0 e) \<noteq> None)) of
                              Some c' \<Rightarrow> make_context e c' (s0 e) |
                                      (* Can we make a transition which subsumes both? *)
                              None \<Rightarrow> (case (hilbert_option (\<lambda>(c', tr). subsumes c' tr t1 \<and> subsumes c' tr t2)) of
                                          Some (c', tr) \<Rightarrow> Some (replace_transition t' from to1 {|t1|} tr) |
                                          None \<Rightarrow> None
                                        )
                        )
                      )
                    )"
  by auto

termination
  apply clarify
  sorry
  
end
