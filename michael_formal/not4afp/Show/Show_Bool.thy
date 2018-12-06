theory Show_Bool
imports "Show.Show"
begin
instantiation bool::"show" begin
fun shows_prec_bool :: "nat \<Rightarrow> bool \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_prec_bool _ True l = ''True''@l"|
  "shows_prec_bool _ False l = ''False''@l"

fun shows_list_bool :: "bool list \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_list_bool [] l = l" |
  "shows_list_bool [b] l = shows_prec 0 b l" |
  "shows_list_bool (h#t) l = (shows_prec 0 h '''')@'',''@(shows_list_bool t l)"

instance proof
  fix x :: bool
  fix p r s
  show "shows_prec p x (r @ s) = shows_prec p x r @ s"
    apply (cases x)
     apply simp
    by simp
next
  fix xs::"bool list"
  fix p r s
  show "shows_list xs (r @ s) = shows_list xs r @ s "
  proof (induct xs)
case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
  proof (induct xs)
    case Nil
    then show ?case
      apply (cases a)
       apply simp
      by simp
next
  case (Cons a xs)
  then show ?case
    by simp
qed
qed
qed
end

lemma show_true: "show True = ''True''"
  by (simp add: shows_string_def)

lemma show_false: "show False = ''False''"
  by (simp add: shows_string_def)
end