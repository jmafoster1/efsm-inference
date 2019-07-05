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
  "naive_score t1 t2 = size (ffilter (\<lambda>(x, y). Label x = Label y \<and> Arity x = Arity y) (fprod t1 t2))"

lemma naive_score_empty: "\<forall>a. naive_score a {||} = 0"
  by (simp add: naive_score_def)

lemma naive_score_empty_2: "\<forall>a. naive_score {||} a = 0"
  by (simp add: naive_score_def)

definition naive_score_one_final_state :: strategy where
  "naive_score_one_final_state t1 t2 = (if t1 = {||} \<and> t2 = {||} then 1 else size (ffilter (\<lambda>(x, y). Label x = Label y \<and> Arity x = Arity y) (fprod t1 t2)))"

fun bool2nat :: "bool \<Rightarrow> nat" where
  "bool2nat True = 1" |
  "bool2nat False = 0"

definition naive_score_rank_one_final_state :: strategy where
  "naive_score_rank_one_final_state t1 t2 = (
     if t1 = {||} \<and> t2 = {||} then
       1 else
     Sum (fset (fimage (\<lambda>(x, y). bool2nat (Label x = Label y) + bool2nat (Arity x = Arity y) + bool2nat (Outputs x = Outputs y)) (fprod t1 t2)))
   )"

end