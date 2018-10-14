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

fun "show" :: "nat \<Rightarrow> string" where
  "show 0 = ''0''" |
  "show n = natToString n"

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

lemma x_neq_0: "x \<noteq> 0 \<Longrightarrow> show x \<noteq> ''0''"
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

lemma x_neq_1: "x \<noteq> 1 \<Longrightarrow> show x \<noteq> ''1''"
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

lemma show_2: "show 2 = ''2''"
  apply (simp add: numeral_2_eq_2 sod_def char_of_def)
  by presburger

lemma show_3: "show 3 = ''3''"
  apply (simp only: eval_nat_numeral)
  by (simp add: sod_def char_of_def)

lemma show_4: "show 4 = ''4''"
  apply (simp only: eval_nat_numeral)
  apply (simp only: show.simps natToString.simps)
  by (simp add: sod_def char_of_def)

lemma show_5: "show 5 = ''5''"
  apply (simp only: eval_nat_numeral)
  apply (simp only: show.simps natToString.simps)
  by (simp add: sod_def char_of_def)

lemma x_div_10_0: "(x::nat) \<noteq> 0 \<Longrightarrow> x \<noteq> 1 \<Longrightarrow> x \<noteq> 2 \<Longrightarrow> x \<noteq> 3 \<Longrightarrow> x \<noteq> 4 \<Longrightarrow> x \<noteq> 5 \<Longrightarrow> x \<noteq> 6 \<Longrightarrow> x \<noteq> 7 \<Longrightarrow> x \<noteq> 8 \<Longrightarrow> x \<noteq> 9 \<Longrightarrow> (x \<ge> 10)"
  by simp

lemma test: "(x div 10 = 0) = (length (show x) = 1)"
  apply (case_tac "x div 10 = 0")
  apply (case_tac "x=0")
   apply simp
  apply (case_tac "x=1")
   apply simp
  apply (case_tac "x=2")
   apply (simp add: sod_def show_2)
  apply (case_tac "x=3")
   apply (simp add: sod_def show_3)
  apply (case_tac "x=4")
   apply (simp add: sod_def show_4)
  apply (case_tac "x=5")
   apply (simp add: sod_def show_5)
  apply (case_tac "x=6")
  apply (simp only: eval_nat_numeral)
  apply (simp only: show.simps natToString.simps)
   apply (simp add: sod_def char_of_def)
  apply (case_tac "x=7")
  apply (simp only: eval_nat_numeral)
  apply (simp only: show.simps natToString.simps)
   apply (simp add: sod_def char_of_def)
  apply (case_tac "x=8")
  apply (simp only: eval_nat_numeral)
  apply (simp only: show.simps natToString.simps)
   apply (simp add: sod_def char_of_def)
  apply (case_tac "x=9")
  apply (simp only: eval_nat_numeral)
  apply (simp only: show.simps natToString.simps)
   apply (simp add: sod_def char_of_def)
   apply simp
   apply presburger
  apply simp
  apply (cases x)
   apply simp
  apply simp
  by (simp add: natToString_0)

lemma length_equality:  "x div 10 = y div 10 \<Longrightarrow> length (show y) = length (show x)"
    apply (cases x)
     apply simp
     apply (cases y)
      apply simp
     apply simp
    apply simp
    apply (cases y)
     apply simp
  by simp

lemma min_length: "Suc 0 \<le> length (Show_Nat.show y)"
  by (metis eq_iff le0 length_0_conv length_Cons natToString_0 not_less_eq_eq show.elims)

lemma x_div_10: "Suc x div 10 \<noteq> x div 10 \<Longrightarrow> Suc x div 10 = Suc (x div 10)"
  by simp

lemma "x div 10 \<noteq> y div 10 \<Longrightarrow> length (show y) \<noteq> length (show x)"
  apply (case_tac "x < y")
  oops

lemma sod_x_equality: "x div 10 = y div 10 \<Longrightarrow> sod x = sod y \<Longrightarrow> x = y"
  apply (simp add: sod_def)
  by (metis mult_div_mod_eq)

lemma "x \<noteq> y \<Longrightarrow> show x \<noteq> show y"
proof (induct "show x" rule: rev_induct)
  case Nil
  then show ?case by (metis One_nat_def list.size(3) min_length not_one_le_zero)
next
  case (snoc as a)
  then show ?case
    apply simp
    apply (cases x)
     apply (metis show.simps(1) x_neq_0)
    apply simp
    sorry
qed

lemma "show x = show y \<Longrightarrow> x = y"
proof (induct x)
  case 0
  then show ?case
    using x_neq_0 by auto
next
  case (Suc m)
  then show ?case
    apply simp
    apply (cases y)
     apply (metis Suc.prems show.simps(1) x_neq_0)
    apply simp
    apply clarify
    apply (case_tac "(Suc m div 10) = (Suc nat div 10)")
     apply simp
    using sod_x_equality apply blast
    sorry
qed
end