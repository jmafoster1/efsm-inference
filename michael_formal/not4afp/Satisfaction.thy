theory Satisfaction
imports GExp
begin

lemma "\<not> satisfiable (gAnd (Gt (V (R 1)) (L (Num 100))) (Eq (V (R 1)) (L (Num 0))))"
  apply (simp add: satisfiable_def)
  apply clarify
  apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (s (R (Suc 0))) (Some (Num 100))")
  by auto
  


end