theory VName
imports "Show.Show_Instances"
begin
datatype vname = I nat | R nat

instantiation vname :: "show" begin
fun shows_prec_vname :: "nat \<Rightarrow> vname \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_prec_vname n (I i) c = shows_prec n i c" |
  "shows_prec_vname n (R i) c = shows_prec n i c"

primrec shows_list_vname :: "vname list \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_list_vname [] l1 = l1" |
  "shows_list_vname (h#t) l1 = (shows_prec 1 h '''')@(shows_list_vname t l1)"

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
    then show ?case by simp
  qed
qed
end
end