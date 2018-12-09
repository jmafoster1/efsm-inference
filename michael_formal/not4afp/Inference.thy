theory Inference
  imports "../EFSM" "../Contexts" Transition_Ordering Prod_Linorder
begin

definition merge_states_aux :: "nat \<Rightarrow> nat \<Rightarrow> transition_matrix \<Rightarrow> transition_matrix" where
  "merge_states_aux x y t = (fimage (\<lambda>((origin, dest), t). ((if origin = x then y else origin , if dest = x then y else dest), t)) t)"

definition merge_states :: "nat \<Rightarrow> nat \<Rightarrow> transition_matrix \<Rightarrow> transition_matrix" where
  "merge_states x y t = (if x > y then merge_states_aux x y t else merge_states_aux y x t)"

lemma merge_states_reflexive: "merge_states x x t = t"
  by (simp add: merge_states_def merge_states_aux_def)

lemma merge_states_symmetry: "merge_states x y t = merge_states y x t"
  by (simp add: merge_states_def merge_states_aux_def)

(* declare[[show_types,show_sorts]] *)

definition choice :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "choice t t' = ((Label t) = (Label t') \<and> (Arity t) = (Arity t') \<and> (\<exists> s. apply_guards (Guard t) s \<and> apply_guards (Guard t') s))"

lemma choice_symmetry: "choice x y = choice y x"
  using choice_def by auto

definition all_pairs :: "transition_matrix \<Rightarrow> (((nat \<times> nat) \<times> transition) \<times> (nat \<times> nat) \<times> transition) fset" where
  "all_pairs t = ffUnion (fimage (\<lambda>x. fimage (\<lambda>y. (x, y)) t) t)"

(* Get every possible ((origin, dest), transition) pair, filter then for nondeterminism, then put them in the right format *)
definition nondeterministic_pairs :: "transition_matrix \<Rightarrow> (nat \<times> (nat \<times> nat) \<times> (transition \<times> transition)) fset" where
  "nondeterministic_pairs t = fimage (\<lambda>(((origin1, dest1), t1), (origin2, dest2), t2). (origin1, (dest1, dest2), (t1, t2))) (ffilter (\<lambda>(((origin1, dest1), t1), (origin2, dest2), t2). origin1 = origin2 \<and> t1 < t2 \<and> choice t1 t2) (all_pairs t))"

definition nondeterministic_transitions :: "transition_matrix \<Rightarrow> (nat \<times> (nat \<times> nat) \<times> (transition \<times> transition)) option" where
  "nondeterministic_transitions t = (if nondeterministic_pairs t = {||} then None else Some (fMax (nondeterministic_pairs t)))"

definition nondeterminism :: "transition_matrix \<Rightarrow> bool" where
  "nondeterminism t = (nondeterministic_pairs t \<noteq> {||})"

definition replace_transition :: "transition_matrix \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> transition_matrix" where
  "replace_transition t from to orig new = (ffilter (\<lambda>x. x \<noteq> ((from, to), orig)) t) |\<union>| {|((from, to), new)|}"
                                                                                                                              
definition defined :: "transition_matrix \<Rightarrow> (nat \<times> nat) fset" where
  "defined t = fimage (\<lambda>x. fst x) t"

primrec alreadyUpdated :: "updates \<Rightarrow> vname \<Rightarrow> bool" where
  "alreadyUpdated [] _ = False" |
  "alreadyUpdated (h#t) r = (if fst h = r then True else alreadyUpdated t r)"

(* function modifyUpdates :: "transition_matrix \<Rightarrow> context \<Rightarrow> transition_matrix option" where
    "modifyUpdates t c = 
        Get all the transitions which go into a state
        For each one, see if therenat a transition which subsumes it and produces the posterior context c for ALL inputs
        If there is, good job!
        If there isn't, fail
    
*)

fun make_context :: "transition_matrix \<Rightarrow> context \<Rightarrow> nat \<Rightarrow> transition_matrix option" where
  "make_context e c s = (if \<exists>p. posterior_sequence empty e 0 <> p = c \<and> last (state_trace e 0 <> p) = s
                  then Some e
                  \<comment> \<open> else if it is possible to modify the update functions of incoming transitions
                     to get the right context then do that \<close>
                  else None)"

lemma make_context_options: "make_context e c s = None \<or> (\<exists>t. make_context e c s = Some t)"
  by simp

primrec gets_us_to :: "nat \<Rightarrow>transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> bool" where
  "gets_us_to target _ s _ [] = (s = target)" |
  "gets_us_to target e s r (h#t) =
    (case (step e s r (fst h) (snd h)) of
      (Some (_, s', _, r')) \<Rightarrow> gets_us_to target e s' r' t |
      _ \<Rightarrow> (s = target)
    )"

definition anterior_context :: "transition_matrix \<Rightarrow> trace \<Rightarrow> context" where
 "anterior_context e t = posterior_sequence \<lbrakk>\<rbrakk> e 0 <> t"

(* Does t1 subsume t2 in all possible anterior contexts? *)
(* For every path which gets us to the problem state, does t1 subsume t2 in the resulting context *)
definition directly_subsumes :: "transition_matrix \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> bool" where
  "directly_subsumes e s t1 t2 = (\<forall>p. (gets_us_to s e 0 <>  p) \<longrightarrow> subsumes (anterior_context e p) t1 t2)"

definition exits_state :: "transition_matrix \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> bool" where
  "exits_state e t from = ((ffilter (\<lambda>((from', to), t'). from' = from \<and> t' = t) e) \<noteq> {||})"

fun merge_transitions :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> transition_matrix option" where
  "merge_transitions oldEFSM newEFSM t1FromOld t2FromOld newFrom t1NewTo t2NewTo t1 t2 = (
    \<comment> \<open> If t1 directly subsumes t2 then replace t2 with t1 \<close>
    if directly_subsumes oldEFSM t1FromOld t1 t2 then Some (replace_transition newEFSM newFrom t2NewTo t2 t1) else
    \<comment> \<open> If t2 directly subsumes t1 then replace t1 with t2 \<close>
    if directly_subsumes oldEFSM t2FromOld t2 t1 then Some (replace_transition newEFSM newFrom t1NewTo t1 t2) else
    \<comment> \<open> Can we get a context where one transition subsumes the other directly \<close>
    \<comment> \<open> Can we make a transition which subsumes both? \<close>
    None
  )"

declare merge_transitions.simps[simp del]

function merge_2 :: "transition_matrix \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition_matrix option" and 
  resolve_nondeterminism :: "(nat \<times> (nat \<times> nat) \<times> (transition \<times> transition)) fset \<Rightarrow> transition_matrix \<Rightarrow> nat \<Rightarrow> nat  \<Rightarrow> transition_matrix \<Rightarrow> transition_matrix option" where
  "resolve_nondeterminism s e s1 s2 t = (if s = {||} then None else (let (from, (to1, to2), (t1, t2)) = fMax s; t' = merge_2 t to1 to2 in
                        case t' of None \<Rightarrow> resolve_nondeterminism (s - {|fMax s|}) e s1 s2 t |
                                    Some t \<Rightarrow> merge_transitions e t (if exits_state e t1 s1 then s1 else s2) (if exits_state e t2 s1 then s1 else s2) from to1 to2 t1 t2 ))" |

"merge_2 e s1 s2 = (if s1 = s2 then Some (e) else (let t' = (merge_states s1 s2 (e)) in
                       \<comment> \<open> Have we got any nondeterminism? \<close>
                       (if \<not> nondeterminism t' then
                         \<comment> \<open> If not then we're good to go \<close>
                         Some t' else
                         \<comment> \<open> If we have then we need to fix it \<close>
                         resolve_nondeterminism (nondeterministic_pairs t') e s1 s2 t')))"
  sorry
termination
  sorry

definition hilbert_option :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option" where
  "hilbert_option f = (if {x. f x} = {} then None else Some (Eps f))"
 
end
