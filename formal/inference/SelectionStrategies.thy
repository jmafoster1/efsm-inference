section\<open>Selection Strategies\<close>
text\<open>The strategy used to idenfity and prioritise states to be merged plays a big part in how the
final model turns out. This theory file presents a number of different selection strategies.\<close>

theory SelectionStrategies
imports Inference
begin

subsection\<open>One of the simplest strategies is to look only at the labels and arities of outgoing
transitions of each state. Pairs of states are ranked by how many transitions with the same label
and arity they have in common.\<close>
definition naive_score :: strategy where
  "naive_score t1 t2 = size (ffilter (\<lambda>(x, y). Label x = Label y \<and> Arity x = Arity y) (t1 |\<times>| t2))"

lemma naive_score_empty: "\<forall>a. naive_score a {||} = 0"
  by (simp add: naive_score_def)

lemma naive_score_empty_2: "\<forall>a. naive_score {||} a = 0"
  by (simp add: naive_score_def)

definition score_one_final_state :: "strategy \<Rightarrow> strategy" where
  "score_one_final_state s t1 t2 = (if t1 = {||} \<and> t2 = {||} then 1 else s t1 t2)"

definition naive_score_one_final_state :: strategy where
  "naive_score_one_final_state = score_one_final_state naive_score"

fun bool2nat :: "bool \<Rightarrow> nat" where
  "bool2nat True = 1" |
  "bool2nat False = 0"

(* One point each for equal label, arity, and outputs *)
definition naive_score_rank :: strategy where
  "naive_score_rank t1 t2 = Sum (fset (fimage (\<lambda>(x, y). bool2nat (Label x = Label y) + bool2nat (Arity x = Arity y) + bool2nat (Outputs x = Outputs y)) (t1 |\<times>| t2)))"

definition naive_score_rank_one_final_state :: strategy where
  "naive_score_rank_one_final_state = score_one_final_state naive_score_rank"

(* Functions with same label, and input and output arities contribute one point for each guard    *)
(* and output they share. *)
definition naive_score_comprehensive :: strategy where
  "naive_score_comprehensive t1 t2 = Sum (fset (fimage (\<lambda>(x, y). if Label x = Label y \<and> Arity x = Arity y then
                                                                   if length (Outputs x) = length (Outputs y) then
                                                                     card (set (Guard x) \<inter> set (Guard y)) + length (filter (\<lambda>(p1, p2). p1 = p2) (zip (Outputs x) (Outputs y)))
                                                                   else 0
                                                                 else 0)
                                               (t1 |\<times>| t2)))"

(* Functions with same label, and input and output arities contribute one point for each guard    *)
(* and output they share. Transitions which are exactly equal get a very high score. *)
definition naive_score_comprehensive_eq_high :: strategy where
  "naive_score_comprehensive_eq_high t1 t2 = Sum (fset (fimage (\<lambda>(x, y). 
                                                               if x = y then 100 else
                                                                 if Label x = Label y \<and> Arity x = Arity y then
                                                                   if length (Outputs x) = length (Outputs y) then
                                                                     card (set (Guard x) \<inter> set (Guard y)) + length (filter (\<lambda>(p1, p2). p1 = p2) (zip (Outputs x) (Outputs y)))
                                                                   else 0
                                                                 else 0)
                                               (t1 |\<times>| t2)))"


end