section{*Selection Strategies*}
text{*The strategy used to idenfity and prioritise states to be merged plays a big part in how the
final model turns out. This theory file presents a number of different selection strategies. *}

theory SelectionStrategies
imports Inference
begin

subsection{*One of the simplest strategies is to look only at the labels and arities of outgoing
transitions of each state. Pairs of states are ranked by how many transitions with the same label
and arity they have in common.*}
definition naive_score :: strategy where
  "naive_score t1 t2 = size (ffilter (\<lambda>(x, y). Label x = Label y \<and> Arity x = Arity y) (fprod t1 t2))"

lemma naive_score_empty: "\<forall>a. naive_score a {||} = 0"
  by (simp add: naive_score_def)

lemma naive_score_empty_2: "\<forall>a. naive_score {||} a = 0"
  by (simp add: naive_score_def)
  

end