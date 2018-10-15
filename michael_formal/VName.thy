theory VName
imports Utils "not4afp/Show_Nat"
begin
datatype vname = I nat | R nat

instantiation vname :: "show" begin
fun shows_prec_vname :: "nat \<Rightarrow> vname \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_prec_vname n (I i) c = ''i''@shows_prec n i c" |
  "shows_prec_vname n (R i) c = ''r''@shows_prec n i c"

primrec shows_list_vname_aux :: "vname list \<Rightarrow> string list" where
  "shows_list_vname_aux [] = ''''" |
  "shows_list_vname_aux (h#t) = (shows_prec 0 h '''')#(shows_list_vname_aux t)"

definition shows_list_vname :: "vname list \<Rightarrow> char list \<Rightarrow> char list" where
"shows_list_vname lst c = (join (shows_list_vname_aux lst) '', '')@c"

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
    then show ?case by (simp add: shows_list_vname_def)
  next
    case (Cons a xs)
    then show ?case by (simp add: shows_list_vname_def)
  qed
qed
end

lemma show_vname_deterministic: "show (v1::vname) = show (v2::vname) \<Longrightarrow> v1 = v2"
  apply (cases v1)
   apply (cases v2)
    apply (simp add: show_nat_deterministic)
   apply simp
   apply (cases v2)
   apply simp
  by (simp add: show_nat_deterministic)

end