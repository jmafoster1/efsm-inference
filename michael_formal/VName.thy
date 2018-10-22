theory VName
imports "Show.Show_Instances"
begin
datatype vname = I nat | R nat

instantiation vname :: "show" begin
fun shows_prec_vname :: "nat \<Rightarrow> vname \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_prec_vname n (I i) c = ''i''@shows_prec n i c" |
  "shows_prec_vname n (R i) c = ''r''@shows_prec n i c"

fun shows_list_vname :: "vname list \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_list_vname [] l = l" |
  "shows_list_vname [u] l = shows_prec 0 u l" |
  "shows_list_vname (h#t) l = (shows_prec 0 h '''')@'',''@(shows_list_vname t l)"

instance proof
  fix x::vname
  fix r s p
  show "shows_prec p x (r @ s) = shows_prec p x r @ s"
  proof (cases x)
    case (I x1)
    then show ?thesis by (simp add: shows_prec_append)
  next
    case (R x2)
    then show ?thesis by (simp add: shows_prec_append)
  qed
next
  fix xs :: "vname list"
  fix r s
  show "shows_list xs (r @ s) = shows_list xs r @ s"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case
    proof (induct xs)
      case Nil
      then show ?case
        apply (simp add: shows_prec_list_def)
        apply (cases a)
         apply (simp add: shows_prec_append)
        by (simp add: shows_prec_append)
    next
      case (Cons a xs)
      then show ?case by simp
    qed
  qed
qed
end

lemma show_nat_deterministic: "\<forall>(x::nat) (y::nat). show x = show y \<longrightarrow> x = y"
  apply (simp add: shows_prec_nat_def)
  sorry

lemma show_vname_deterministic: "show (v1::vname) = show (v2::vname) \<Longrightarrow> v1 = v2"
  apply (cases v1)
   apply (cases v2)
    apply (simp add: show_nat_deterministic)
   apply simp
   apply (cases v2)
   apply simp
  by (simp add: show_nat_deterministic)

end