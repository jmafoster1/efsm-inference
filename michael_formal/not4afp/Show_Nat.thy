theory Show_Nat
  imports "Show.Show" "~~/src/HOL/Library/Log_Nat"
begin

definition sod :: "nat \<Rightarrow> char" where
  "sod n = char_of ((n mod 10) + 48)"

lemma sod_suc_0: "sod (Suc 0) = CHR ''1''"
  by (simp add: sod_def char_of_def)

fun natToString :: "nat \<Rightarrow> string" where
  "natToString 0 = ''''" |
  "natToString n = (natToString (n div 10)) @ [(sod n)]"

fun "showNat" :: "nat \<Rightarrow> string" where
  "showNat 0 = ''0''" |
  "showNat n = natToString n"

lemma x_div_ten_zero: "((x::nat) div 10 = 0) = (x < 10)"
proof
  show "x div 10 = 0 \<Longrightarrow> x < 10"
    by simp
next
  show "x < 10 \<Longrightarrow> x div 10 = 0"
    by simp
qed

lemma natToString_0: "(natToString x = []) = (x = 0)"
proof (induct x)
  case 0
  then show ?case by simp
next
  case (Suc x)
  then show ?case by simp
qed

lemma x_neq_0: "x \<noteq> 0 \<Longrightarrow> showNat x \<noteq> ''0''"
proof (induct x)
  case 0
  then show ?case by simp
next
  case (Suc y)
  then show ?case
    apply simp
    apply clarify
    apply (simp add: natToString_0 x_div_ten_zero)
    apply (case_tac "y=0")
     apply (simp add: sod_def char_of_def)
    apply (case_tac "y=1")
     apply (simp add: sod_def char_of_def)
    apply (case_tac "y=2")
     apply (simp add: sod_def char_of_def)
    apply (case_tac "y=3")
     apply (simp add: sod_def char_of_def)
    apply (case_tac "y=4")
     apply (simp add: sod_def char_of_def)
    apply (case_tac "y=5")
     apply (simp add: sod_def char_of_def)
    apply (case_tac "y=6")
     apply (simp add: sod_def char_of_def)
    apply (case_tac "y=7")
     apply (simp add: sod_def char_of_def)
    apply (case_tac "y=8")
     apply (simp add: sod_def char_of_def)
    by simp
qed

lemma sod_neq: "sod (Suc n) \<noteq> sod (Suc m) \<Longrightarrow> n \<noteq> m"
  apply (simp add: sod_def)
  by auto

lemma n_mod_10: "(Suc n) mod 10 \<noteq> Suc (n mod 10) \<Longrightarrow> (Suc n) mod 10 = 0"
  by (meson mod_Suc)

lemma sub4show_y: "(natToString (Suc x div 10) @ [sod (Suc x)] = show y) = (show y = natToString (Suc x div 10) @ [sod (Suc x)])"
  by auto

lemma x_neq_1: "x \<noteq> 1 \<Longrightarrow> showNat x \<noteq> ''1''"
  proof (induct x)
  case 0
  then show ?case by simp
next
  case (Suc y)
  then show ?case
    apply simp
    apply clarify
    apply (simp add: natToString_0 x_div_ten_zero)
    apply (case_tac "y=0")
     apply (simp add: sod_def char_of_def)
    apply (case_tac "y=1")
     apply (simp add: sod_def char_of_def)
    apply (case_tac "y=2")
     apply (simp add: sod_def char_of_def)
    apply (case_tac "y=3")
     apply (simp add: sod_def char_of_def)
    apply (case_tac "y=4")
     apply (simp add: sod_def char_of_def)
    apply (case_tac "y=5")
     apply (simp add: sod_def char_of_def)
    apply (case_tac "y=6")
     apply (simp add: sod_def char_of_def)
    apply (case_tac "y=7")
     apply (simp add: sod_def char_of_def)
    apply (case_tac "y=8")
     apply (simp add: sod_def char_of_def)
    by simp
qed

lemma x_div_10_0: "(x::nat) \<noteq> 0 \<Longrightarrow> x \<noteq> 1 \<Longrightarrow> x \<noteq> 2 \<Longrightarrow> x \<noteq> 3 \<Longrightarrow> x \<noteq> 4 \<Longrightarrow> x \<noteq> 5 \<Longrightarrow> x \<noteq> 6 \<Longrightarrow> x \<noteq> 7 \<Longrightarrow> x \<noteq> 8 \<Longrightarrow> x \<noteq> 9 \<Longrightarrow> (x \<ge> 10)"
  by simp

lemma x_div_10: "Suc x div 10 \<noteq> x div 10 \<Longrightarrow> Suc x div 10 = Suc (x div 10)"
  by simp

lemma sod_x_equality: "x div 10 = y div 10 \<Longrightarrow> sod x = sod y \<Longrightarrow> x = y"
  apply (simp add: sod_def)
  by (metis mult_div_mod_eq)

instantiation nat :: "show" begin
definition shows_prec_nat :: "nat \<Rightarrow> nat \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_prec_nat p n l = showNat n @ l"

fun shows_list_nat :: "nat list \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_list_nat [] l = l" |
  "shows_list_nat [n] l = shows_prec 0 n l" |
  "shows_list_nat (h#t) l = (shows_prec 0 h '''') @ (shows_list_nat t l)"

instance proof
  fix x :: nat
  fix p r s
  show "shows_prec p x (r @ s) = shows_prec p x r @ s"
    by (simp add: shows_prec_nat_def)
next
  fix xs :: "nat list"
  fix p r s
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
    by (simp add: shows_prec_nat_def)
next
  case (Cons a xs)
  then show ?case
    by simp
qed
qed
qed
end
lemma show_nat_deterministic: "show (v1::nat) = show (v2::nat) \<Longrightarrow> v1 = v2"
  sorry

lemma show_nat_not_neg: "hd (show (x::nat)) \<noteq> CHR ''-''"
proof (induct x)
  case 0
  then show ?case
    by (simp add: shows_prec_nat_def)
next
  case (Suc x)
  then show ?case
    apply (simp add: shows_prec_nat_def)
    sorry
qed

lemma show_nat_not_quoted: "hd (show (n :: nat)) = CHR ''0'' \<or>
hd (show (n :: nat)) = CHR ''1'' \<or>
hd (show (n :: nat)) = CHR ''2'' \<or>
hd (show (n :: nat)) = CHR ''3'' \<or>
hd (show (n :: nat)) = CHR ''4'' \<or>
hd (show (n :: nat)) = CHR ''5'' \<or>
hd (show (n :: nat)) = CHR ''6'' \<or>
hd (show (n :: nat)) = CHR ''7'' \<or>
hd (show (n :: nat)) = CHR ''8'' \<or>
hd (show (n :: nat)) = CHR ''9''"
proof (induct n)
  case 0
  then show ?case
    by (simp add: shows_prec_nat_def)
next
  case (Suc n)
  then show ?case
    apply (simp add: shows_prec_nat_def)
    sorry
qed
end