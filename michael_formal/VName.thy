theory VName
imports "Show.Show_Instances" Utils
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

lemma show_nat_0: "show (0::nat) = ''0''"
  by (simp add: shows_prec_nat_def showsp_nat.simps shows_string_def)

lemma "show v1 \<noteq> show (Suc v1)"
  apply (simp add: shows_prec_nat_def)
  sorry

lemma "\<not> v2 < (10::nat) \<Longrightarrow> ''0'' \<noteq> show v2"
  apply (simp add: shows_prec_nat_def)
  sorry

lemma nat_deterministic_string: "(show (v1::nat) = show (v2::nat)) = (v1 = v2)"
  apply (case_tac "v1 < 10")
   apply (case_tac "v2 < 10")
    apply (simp add: shows_prec_nat_def)
    apply (simp add: showsp_nat.simps)
    apply (simp add: shows_string_def)
    apply presburger
   apply simp
   apply (case_tac "v1 = 0")
    apply (simp add: show_nat_0)

   

lemma vname_deterministic_string: "(show (v1::vname) = show (v2::vname)) = (v1 = v2)"
proof (cases v1)
  case (I x1)
  then show ?thesis
    apply (cases v2)
     apply simp

next
  case (R x2)
  then show ?thesis sorry
qed
end