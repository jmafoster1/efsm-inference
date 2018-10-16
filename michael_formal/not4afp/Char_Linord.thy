theory Char_Linord
imports Main
begin
instantiation char :: linorder begin
definition "less_eq_char = (\<lambda>c d. of_char c \<le> (of_char d :: nat))"

definition "less_char = (\<lambda>c d. of_char c < (of_char d :: nat))"
instance proof
  fix x y:: char
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    apply (simp add: less_char_def)
    by (meson le_cases less_eq_char_def not_less)
next
  fix x :: char
  show "x \<le> x"
    by (simp add: less_eq_char_def)
next
  fix x y z::char
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (simp add: less_eq_char_def)
next
  fix x y:: char
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (simp add: less_eq_char_def)
next
  fix x y:: char
  show "x \<le> y \<or> y \<le> x"
    apply (simp add: less_eq_char_def)
    by auto
qed
end
end