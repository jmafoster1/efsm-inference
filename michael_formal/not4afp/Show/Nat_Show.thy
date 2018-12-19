theory Nat_Show
imports "Show.Show"
begin
instantiation nat :: "show" begin
primrec shows_prec_nat :: "nat \<Rightarrow> nat \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_prec_nat _ 0 lst = (CHR ''0'')#lst" |
  "shows_prec_nat n (Suc m) lst = (CHR ''s'')#(shows_prec_nat n m lst)"

fun shows_list_nat :: "nat list \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_list_nat [] c = c" |
  "shows_list_nat [h] c = (shows_prec 0 h '''')@c" |
  "shows_list_nat (h#t) c = (shows_prec 0 h '''')@(shows_list_nat t c)"

instance proof
  fix x :: nat
  fix p r s
  show "shows_prec p x (r @ s) = shows_prec p x r @ s"
  proof (induct x)
    case 0
    then show ?case by simp
  next
    case (Suc x)
    then show ?case by simp
  qed
next
  fix xs :: "nat list"
  fix p r s
  show "shows_list xs (r @ s) = shows_list xs r @ s"
  proof (induct xs)
case Nil
  then show ?case by simp
next
  case (Cons a as)
  then show ?case
    apply (cases as)
     apply simp
    by simp
qed
qed
end

lemma x_not_suc0:"x \<noteq> Suc 0 \<Longrightarrow> show x \<noteq> ''s0''"
proof (induction x)
  case 0
  then show ?case by simp
next
  case (Suc x)
  then show ?case
    apply simp
  proof -
    assume a1: "0 < x"
    have "CHR ''s'' \<noteq> CHR ''0''"
      by force
    then show "show x \<noteq> ''0''"
      using a1 by (metis Suc_pred list.inject shows_prec_nat.simps(2))
  qed
qed

lemma length_show_x: "(x::nat) < (y::nat) \<Longrightarrow> length (show x) < length (show y)"
proof-
  fix x
  show "x < y \<Longrightarrow> length (show x) < length (show y)"
  proof (induct y)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    then show ?case
      apply simp
      using less_Suc_eq by blast
  qed
qed

lemma "(x::nat) \<noteq> (y::nat) \<Longrightarrow> show x \<noteq> show y"
  apply (case_tac "x < y")
  using length_show_x apply fastforce
  by (metis length_show_x not_less_iff_gr_or_eq)

lemma "show (x::nat) = show (y::nat) \<Longrightarrow> x = y"
  by (metis length_show_x not_less_iff_gr_or_eq)

end