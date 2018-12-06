theory List_Linorder
imports Main
begin

instantiation list :: (linorder) linorder begin
fun less_eq_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "[] \<le> _ = True" |
  "_ \<le> [] = False" |
  "(h1#t1) \<le> (h2#t2) = (if h1 = h2 then t1 \<le> t2 else h1 < h2)"

definition less_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "(less_list x y) = (less_eq x y \<and> \<not> less_eq y x)"

instance proof
  fix x :: "'a list"
  show "x \<le> x"
  proof (induct x)
    case Nil
    then show ?case by simp
  next
    case (Cons a x)
    then show ?case by simp
  qed
next
  fix x y :: "'a list"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (simp add: less_list_def)
next
  fix x y z :: "'a list"
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  proof (induct x)
    case Nil
    then show ?case
      by simp
  next
    case (Cons x xs)
    then show ?case
    proof (induct y)
      case Nil
      then show ?case by simp
    next
      case (Cons y ys)
      then show ?case
      proof (induct z)
        case Nil
        then show ?case by simp
      next
        case (Cons z zs)
        then show ?case
          apply simp
          apply (case_tac "x=y")
          apply (case_tac "y=z")
           apply simp
          sorry
      qed
    qed
  qed


end

end