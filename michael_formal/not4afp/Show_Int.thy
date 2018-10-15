theory Show_Int
imports Show_Nat
begin

instantiation int :: "show" begin
  definition shows_prec_int :: "nat \<Rightarrow> int \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_prec_int p i = (if i < 0 then shows_string ''-'' o shows_prec p (nat (- i)) else shows_prec p (nat i))"

fun shows_list_int :: "int list \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_list_int [] l = l" |
  "shows_list_int [n] l = shows_prec 0 n l" |
  "shows_list_int (h#t) l = (shows_prec 0 h '''') @ (shows_list_int t l)"

instance proof
  fix x::int
  fix p r s
  show "shows_prec p x (r @ s) = shows_prec p x r @ s"
  proof (induct x)
    case (nonneg n)
    then show ?case
      by (simp add: shows_prec_int_def shows_string_def shows_prec_nat_def)
  next
    case (neg n)
    then show ?case
      by (simp add: shows_prec_int_def shows_string_def shows_prec_nat_def)
  qed
next
  fix xs :: "int list"
  fix r s
  show "shows_list xs (r @ s) = shows_list xs r @ s"
  proof (induct xs)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a xs)
    then show ?case
    proof (induct xs)
      case Nil
      then show ?case
        by (simp add: shows_prec_int_def shows_string_def shows_prec_nat_def)
    next
      case (Cons a xs)
      then show ?case
        by (simp)
    qed
  qed
qed
end

lemma show_int_deterministic: "show (v1::int) = show (v2::int) \<Longrightarrow> v1 = v2"
  apply (cases v1)
   apply (cases v2)
    apply (simp add: shows_prec_int_def)
    apply (simp add: show_nat_deterministic)
   apply (simp add: shows_prec_int_def shows_string_def)
   apply (metis list.sel(1) show_nat_not_neg)
   apply (cases v2)
   apply (simp add: shows_prec_int_def shows_string_def)
   apply (metis list.sel(1) show_nat_not_neg)
   apply (simp add: shows_prec_int_def shows_string_def)
  using show_nat_deterministic by fastforce

lemma show_int_not_quoted: "hd (show (n :: int)) = CHR ''-'' \<or>
hd (show (n :: int)) = CHR ''0'' \<or>
hd (show (n :: int)) = CHR ''1'' \<or>
hd (show (n :: int)) = CHR ''2'' \<or>
hd (show (n :: int)) = CHR ''3'' \<or>
hd (show (n :: int)) = CHR ''4'' \<or>
hd (show (n :: int)) = CHR ''5'' \<or>
hd (show (n :: int)) = CHR ''6'' \<or>
hd (show (n :: int)) = CHR ''7'' \<or>
hd (show (n :: int)) = CHR ''8'' \<or>
hd (show (n :: int)) = CHR ''9''"
  apply (cases n)
   apply (simp add: show_nat_not_quoted shows_prec_int_def)
  by (simp add: shows_prec_int_def shows_string_def)
end