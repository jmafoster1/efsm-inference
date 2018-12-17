theory SelectionStrategies
imports "Inference"
begin

definition naive_score :: strategy where
  "naive_score t1 t2 = size (ffilter (\<lambda>(x, y). Label x = Label y \<and> Arity x = Arity y) (fprod t1 t2))"

lemma naive_score_empty: "\<forall>a. naive_score a {||} = 0"
  by (simp add: naive_score_def)

lemma naive_score_empty_2: "\<forall>a. naive_score {||} a = 0"
  by (simp add: naive_score_def)
  

end