theory Inference
  imports "../Nondeterministic_EFSM" "../EFSM" "../Contexts" Transition_Ordering
          "~~/src/HOL/Library/Product_Lexorder"
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

definition all_pairs :: "'a fset \<Rightarrow> ('a \<times> 'a) fset" where
  "all_pairs t = ffUnion (fimage (\<lambda>x. fimage (\<lambda>y. (x, y)) t) t)"

definition fprod :: "'a fset \<Rightarrow> 'b fset \<Rightarrow> ('a \<times> 'b) fset" where
  "fprod a b = Abs_fset ((fset a) \<times> (fset b))"

lemma fprod_empty[simp]: "\<forall>a. fprod {||} a = {||}"
  apply (simp add: fprod_def)
  by (simp add: bot_fset_def)

lemma fprod_empty_2[simp]: "\<forall>a. fprod a {||} = {||}"
  apply (simp add: fprod_def ffUnion_def)
  by (simp add: bot_fset_def)

(* Get every possible ((origin, dest), transition) pair, filter then for nondeterminism, then put them in the right format *)
definition nondeterministic_pairs :: "transition_matrix \<Rightarrow> (nat \<times> (nat \<times> nat) \<times> (transition \<times> transition)) fset" where
  "nondeterministic_pairs t = fimage (\<lambda>(((origin1, dest1), t1), (origin2, dest2), t2). (origin1, (dest1, dest2), (t1, t2))) (ffilter (\<lambda>(((origin1, dest1), t1), (origin2, dest2), t2). origin1 = origin2 \<and> t1 < t2 \<and> choice t1 t2) (all_pairs t))"

definition nondeterministic_transitions :: "transition_matrix \<Rightarrow> (nat \<times> (nat \<times> nat) \<times> (transition \<times> transition)) option" where
  "nondeterministic_transitions t = (if nondeterministic_pairs t = {||} then None else Some (fMax (nondeterministic_pairs t)))"

definition nondeterminism :: "transition_matrix \<Rightarrow> bool" where
  "nondeterminism t = (nondeterministic_pairs t \<noteq> {||})"

definition replace_transition :: "transition_matrix \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> transition_matrix" where
  "replace_transition t from to orig new = (ffilter (\<lambda>x. x \<noteq> ((from, to), orig)) t) |\<union>| {|((from, to), new)|}"

definition exits_state :: "transition_matrix \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> bool" where
  "exits_state e t from = ((ffilter (\<lambda>((from', to), t'). from' = from \<and> t' = t) e) \<noteq> {||})"

primrec make_guard :: "value list \<Rightarrow> nat \<Rightarrow> guard list" where
"make_guard [] _ = []" |
"make_guard (h#t) n = (gexp.Eq (V (I n)) (L h))#(make_guard t (n+1))"

primrec make_outputs :: "value list \<Rightarrow> output_function list" where
  "make_outputs [] = []" |
  "make_outputs (h#t) = (L h)#(make_outputs t)"

fun maxS :: "transition_matrix \<Rightarrow> nat" where
  "maxS t = (if t = {||} then 0 else fMax ((fimage (\<lambda>((origin, dest), t). origin) t) |\<union>| (fimage (\<lambda>((origin, dest), t). dest) t)))"

fun make_branch :: "transition_matrix \<Rightarrow> nat  \<Rightarrow> datastate \<Rightarrow> (char list \<times> value list \<times> value list) list \<Rightarrow> transition_matrix" where
  "make_branch e _ _ [] = e" |
  "make_branch e s r ((label, inputs, outputs)#t) =
    (case (step e s r label inputs) of
      (Some (transition, s', outputs, updated)) \<Rightarrow> (make_branch e s' updated t) |
      None \<Rightarrow> make_branch (finsert ((s, (maxS e)+1), \<lparr>Label=label, Arity=length inputs, Guard=(make_guard inputs 1), Outputs=(make_outputs outputs), Updates=[]\<rparr>) e) ((maxS e)+1) r t
    )"

type_synonym log = "(char list \<times> value list \<times> value list) list list"

primrec make_pta :: "log \<Rightarrow> transition_matrix \<Rightarrow> transition_matrix" where
  "make_pta [] e = e" |
  "make_pta (h#t) e = (make_branch e 0 <> h)|\<union>|(make_pta t e)"

type_synonym generator_function = "transition_matrix \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> transition option"

definition null_generator :: generator_function where
  "null_generator a b c d e = None"

type_synonym update_modifier = "transition \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> transition_matrix \<Rightarrow> (transition_matrix \<times> (nat \<Rightarrow> nat)) option"

definition null_modifier :: update_modifier where
  "null_modifier a b c d = None"

definition easy_merge :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> generator_function \<Rightarrow> transition_matrix option" where
  "easy_merge oldEFSM newEFSM t1FromOld t2FromOld newFrom t1NewTo t2NewTo t1 t2 maker = (
    \<comment> \<open> If t1 directly subsumes t2 then replace t2 with t1 \<close>
    if directly_subsumes oldEFSM t1FromOld t2 t1 then Some (replace_transition newEFSM newFrom t2NewTo t1 t2) else
    \<comment> \<open> If t2 directly subsumes t1 then replace t1 with t2 \<close>
    if directly_subsumes oldEFSM t2FromOld t1 t2 then Some (replace_transition newEFSM newFrom t1NewTo t2 t1) else
    \<comment> \<open> Can we make a transition which subsumes both? \<close>
    (case maker oldEFSM t1FromOld t1 t2FromOld t2 of
    Some t' \<Rightarrow>
    if directly_subsumes oldEFSM t2FromOld t1 t' \<and> directly_subsumes oldEFSM t1FromOld t2 t' then
       Some (replace_transition (replace_transition newEFSM newFrom t1NewTo t2 t') newFrom t2NewTo t1 t') else
    None |
    None \<Rightarrow> None)
  )"

definition same_structure :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> bool" where
  "same_structure t1 t2 \<equiv> (\<forall>s1 s2 t. ((s1, s2), t) |\<in>| t1 \<longrightarrow> (\<exists>t'. ((s1, s2), t') |\<in>| t2 \<and> directly_subsumes t1 s1 t' t)) \<and>
                          (\<forall>s1 s2 t. ((s1, s2), t) |\<in>| t2 \<longrightarrow> (\<exists>t'. ((s1, s2), t') |\<in>| t1 \<and> directly_subsumes t1 s1 t' t))"

definition merge_transitions :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> generator_function \<Rightarrow> update_modifier \<Rightarrow> bool \<Rightarrow> transition_matrix option" where
  "merge_transitions oldEFSM newEFSM t1FromOld t2FromOld newFrom t1NewTo t2NewTo t1 t2 maker modifier modify = (
     case easy_merge oldEFSM newEFSM t1FromOld t2FromOld newFrom t1NewTo t2NewTo t1 t2 maker of
      Some x \<Rightarrow> Some x |
      \<comment> \<open> Can we modify the updates such that subsumption can occur? \<close>
      None \<Rightarrow> (
        if modify then
          (case modifier t1 t2 newFrom newEFSM of
            None \<Rightarrow> None |
            Some (t', H) \<Rightarrow> (if nondeterministic_simulates t' oldEFSM then easy_merge t' t' (H newFrom) (H newFrom) (H newFrom) (H t1NewTo) (H t2NewTo) t1 t2 maker else None)
          )
        else None
      )
    )"

type_synonym scoreboard = "(nat \<times> (nat \<times> nat)) fset"
type_synonym strategy = "transition fset \<Rightarrow> transition fset \<Rightarrow> nat"

definition outgoing_transitions :: "nat \<Rightarrow> transition_matrix \<Rightarrow> transition fset" where
  "outgoing_transitions n t = fimage (\<lambda>(x, t'). t') (ffilter (\<lambda>((origin, dest), t). origin = n) t)"

definition score :: "transition_matrix \<Rightarrow> strategy \<Rightarrow> scoreboard" where
  "score t rank = fimage (\<lambda>(s1, s2). (rank (outgoing_transitions s1 t) (outgoing_transitions s2 t), (s1, s2))) (ffilter (\<lambda>(x, y). x < y) (all_pairs (S t)))"

function resolve_nondeterminism :: "(nat \<times> (nat \<times> nat) \<times> (transition \<times> transition)) fset \<Rightarrow> transition_matrix \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition_matrix \<Rightarrow> generator_function \<Rightarrow> update_modifier \<Rightarrow> transition_matrix option" and
                        merge :: "transition_matrix \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> generator_function \<Rightarrow> update_modifier \<Rightarrow> transition_matrix option" where
  "resolve_nondeterminism s e s1 s2 t g m = (if s = {||} then None else (let (from, (to1, to2), (t1, t2)) = fMax s in
                        case merge t to1 to2 g m of None \<Rightarrow> resolve_nondeterminism (s - {|fMax s|}) e s1 s2 t g m |
                                    Some t \<Rightarrow> merge_transitions e t (if exits_state e t1 s1 then s1 else s2) (if exits_state e t2 s1 then s1 else s2) from to1 to2 t1 t2 g m True))" |

"merge e s1 s2 g m = (if s1 = s2 then Some (e) else (let t' = (merge_states s1 s2 (e)) in
                       \<comment> \<open> Have we got any nondeterminism? \<close>
                       (if \<not> nondeterminism t' then
                         \<comment> \<open> If not then we're good to go \<close>
                         Some t' else
                         \<comment> \<open> If we have then we need to fix it \<close>
                         resolve_nondeterminism (nondeterministic_pairs t') e s1 s2 t' g m)))"
     defer
     apply auto[1]
    apply simp
   apply auto[1]
  sorry
termination
  sorry

(* export_code resolve_nondeterminism in "Scala" *)

fun inference_step :: "transition_matrix \<Rightarrow> (nat \<times> nat \<times> nat) list \<Rightarrow> generator_function \<Rightarrow> update_modifier \<Rightarrow> transition_matrix option" where
  "inference_step _ [] _ _ = None" |
  "inference_step T ((s, s1, s2)#t) g m =
                                (if s > 0 then
                                   case merge T s1 s2 g m of
                                     Some new \<Rightarrow> Some new |
                                     None \<Rightarrow> inference_step T t g m
                                 else None)"

function infer :: "transition_matrix \<Rightarrow> strategy \<Rightarrow> generator_function \<Rightarrow> update_modifier \<Rightarrow> transition_matrix" where
  "infer t r g m = (case inference_step t (rev (sorted_list_of_fset (score t r))) g m of None \<Rightarrow> t | Some new \<Rightarrow> infer new r g m)"
  by auto
termination
proof-
  show ?thesis
    apply standard
     apply auto[1]
    sorry
qed

definition learn :: "log \<Rightarrow> strategy \<Rightarrow> generator_function \<Rightarrow> update_modifier \<Rightarrow> transition_matrix" where
  "learn l r g m = infer (make_pta l {||}) r g m"

end