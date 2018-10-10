theory Value
imports "Show.Show_Instances"
begin
datatype "value" = Num int | Str string

instantiation "value" :: "show" begin
definition shows_prec_value :: "nat \<Rightarrow> value \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_prec_value n v l = (case v of Num v \<Rightarrow>  shows_prec n v l | Str v \<Rightarrow>  shows_prec n v l)"

primrec shows_list_value :: "value list \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_list_value [] l1 = l1" |
  "shows_list_value (h#t) l1 = (shows_prec 1 h '''')@(shows_list_value t l1)"

(* apply standard = proof *)
(* or just do the types in "fix" *)
instance proof
  fix p::nat
  fix x::"value"
  fix r s
  show "shows_prec p x (r @ s) = shows_prec p x r @ s"
  apply (simp add: shows_prec_value_def)
  apply (case_tac x)
   apply (simp add: shows_prec_append)
  by (simp add: shows_prec_append)
next
  fix p::nat
  fix x::"value"
  fix xs :: "value list"
  fix r s
  show "shows_list xs (r @ s) = shows_list xs r @ s"
  proof (induction "xs")
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case
      by simp
  qed
qed
end
end