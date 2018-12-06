theory Show_Unit
imports "Show.Show"
begin

instantiation unit::"show" begin
definition shows_prec_unit :: "nat \<Rightarrow> unit \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_prec_unit n u l = ''()''@l"

fun shows_list_unit :: "unit list \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_list_unit [] l = l" |
  "shows_list_unit [u] l = shows_prec 0 u l" |
  "shows_list_unit (h#t) l = (shows_prec 0 h '''')@'',''@(shows_list_unit t l)"

instance proof
  fix x :: unit
  fix p r s
  show "shows_prec p x (r @ s) = shows_prec p x r @ s"
    by (simp add: shows_prec_unit_def)
next
  fix xs :: "unit list"
  fix r s
  show "shows_list xs (r @ s) = shows_list xs r @ s"
  proof (induct xs)
case Nil
  then show ?case by (simp add: shows_prec_unit_def)
next
  case (Cons a xs)
  then show ?case
  proof (induct xs)
case Nil
  then show ?case
    by (simp add: shows_prec_unit_def)
next
  case (Cons a xs)
then show ?case by simp
qed
qed
qed

end

end