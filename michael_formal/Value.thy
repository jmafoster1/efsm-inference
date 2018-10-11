theory Value
imports "Show.Show_Instances" Utils
begin
datatype "value" = Num int | Str string

instantiation "value" :: "show" begin
definition shows_prec_value :: "nat \<Rightarrow> value \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_prec_value n v l = (case v of Num v \<Rightarrow>  shows_prec n v l | Str v \<Rightarrow>  ''\"''@shows_prec n v ''''@''\"''@l)"

primrec shows_list_value_aux :: "value list \<Rightarrow> string list" where
  "shows_list_value_aux [] = ''''" |
  "shows_list_value_aux (h#t) = (shows_prec 0 h '''')#(shows_list_value_aux t)"

definition shows_list_value :: "value list \<Rightarrow> char list \<Rightarrow> char list" where
"shows_list_value lst c = (join (shows_list_value_aux lst) '', '')@c"

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
    then show ?case by (simp add: shows_list_value_def)
  next
    case (Cons a xs)
    then show ?case by (simp add: shows_list_value_def)
  qed
qed
end
end