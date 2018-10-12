theory Scratch
  imports "Show.Show_Instances" String_Of_Nat
begin

lemma show_zero_nat: "show (0::nat) = ''0''"
  apply (simp add: shows_prec_nat_def)
  apply (simp add: showsp_nat.simps)
  by (simp add: shows_string_def)

lemma test: "showsp_nat 0 a = showsp_nat 0 (a div 10) \<circ> (@) (string_of_digit (a mod 10)) \<Longrightarrow>
           \<not> a < 10 \<Longrightarrow> a mod 10 = chr \<Longrightarrow> showsp_nat 0 (a div 10) (hd (string_of_digit chr) # b) = [] \<Longrightarrow> False"
  apply (simp add: comp_def del: string_of_digit.simps)
  by (metis Nil_is_append_conv append_eq_append_conv2 list.simps(3) showsp_nat_append)

lemma length_string_of_digit: "length (string_of_digit x) = 1"
  by simp

lemma length_showsp_nat: "length (showsp_nat 0 a b) > 0"
  apply simp
  apply (rule_tac x=0 and xa=a in showsp_nat.elims)
   apply simp
  apply (simp add: shows_string_def)
  apply (case_tac "a < 10")
   apply simp
  apply (simp del: string_of_digit.simps add: shows_string_def)
  apply safe
           apply (metis list.sel(1) string_of_8 test)
          apply (metis list.sel(1) string_of_7 test)
         apply (metis list.sel(1) string_of_6 test)
        apply (metis list.sel(1) string_of_5 test)
       apply (metis list.sel(1) string_of_4 test)
      apply (metis list.sel(1) string_of_3 test)
     apply (metis list.sel(1) string_of_2 test)
    apply (simp del: string_of_digit.simps)
    apply (metis One_nat_def list.sel(1) string_of_1 test)
   apply (simp del: string_of_digit.simps)
   apply (metis dvd_eq_mod_eq_0 list.sel(1) string_of_0 test)
  apply (simp del: string_of_digit.simps)
  by (metis One_nat_def list.sel(1) nat_neq_iff string_of_digit.simps test)

lemma string_append: "(b::string) = ''''@b"
  by simp

lemma showsp_append: "(showsp_nat 0 a b) = (showsp_nat 0 a '''')@b"
  by (metis showsp_nat_append string_append)

lemma another_length_one: "length (showsp_nat 0 a b) = length b + length (show a)"
  by (metis add.commute length_append shows_prec_nat_def showsp_append)

lemma length_showsp_nat_2: "length (showsp_nat 0 a (string_of_digit b)) > 1"
  apply simp
  apply safe
           apply (metis Suc_lessI add_eq_self_zero another_length_one length_Cons length_showsp_nat less_numeral_extra(3) list.size(3) shows_prec_nat_def)
          apply (metis Suc_lessI add_eq_self_zero another_length_one length_Cons length_showsp_nat less_numeral_extra(3) list.size(3) shows_prec_nat_def)
         apply (metis Suc_lessI add_eq_self_zero another_length_one length_Cons length_showsp_nat less_numeral_extra(3) list.size(3) shows_prec_nat_def)
        apply (metis Suc_lessI add_eq_self_zero another_length_one length_Cons length_showsp_nat less_numeral_extra(3) list.size(3) shows_prec_nat_def)
       apply (metis Suc_lessI add_eq_self_zero another_length_one length_Cons length_showsp_nat less_numeral_extra(3) list.size(3) shows_prec_nat_def)
      apply (metis Suc_lessI add_eq_self_zero another_length_one length_Cons length_showsp_nat less_numeral_extra(3) list.size(3) shows_prec_nat_def)
     apply (metis Suc_lessI add_eq_self_zero another_length_one length_Cons length_showsp_nat less_numeral_extra(3) list.size(3) shows_prec_nat_def)
    apply (metis Suc_lessI add_eq_self_zero another_length_one length_Cons length_showsp_nat less_numeral_extra(3) list.size(3) shows_prec_nat_def)
   apply (metis Suc_lessI add_eq_self_zero another_length_one length_Cons length_showsp_nat less_numeral_extra(3) list.size(3) shows_prec_nat_def)
  by (metis Suc_lessI add_eq_self_zero another_length_one length_Cons length_showsp_nat less_numeral_extra(3) list.size(3) shows_prec_nat_def)

lemma bar: "showsp_nat 0 a (string_of_digit b) \<noteq> string_of_digit y"
  by (metis length_showsp_nat_2 length_string_of_digit less_numeral_extra(4))

lemma move_string_of_digit: "showsp_nat 0 (x div 10) (string_of_digit (x mod 10)) = show (x div 10) @ (string_of_digit (x mod 10))"
  apply (simp add: shows_prec_nat_def)
  using showsp_append by blast

lemma showsp_nat_append_fun: "(\<lambda>x. showsp_nat 0 (n div 10) (string_of_digit (n mod 10) @ x)) = (\<lambda>x. showsp_nat 0 (n div 10) (string_of_digit (n mod 10)) @ x)"
  apply (rule ext)
  using showsp_nat_append by auto

lemma append_equality: "showsp_nat 0 (x div 10) (string_of_digit (x mod 10)) = showsp_nat 0 (y div 10) (string_of_digit (y mod 10)) \<Longrightarrow> string_of_digit (x mod 10) = string_of_digit (y mod 10)"
  apply (simp only: move_string_of_digit)
  apply (case_tac "string_of_digit (x mod 10) = ''0''")
   apply (simp del: string_of_digit.simps)
   apply simp
  apply (case_tac "string_of_digit (x mod 10) = ''1''")
   apply (simp del: string_of_digit.simps)
   apply simp
  apply (case_tac "string_of_digit (x mod 10) = ''2''")
   apply (simp del: string_of_digit.simps)
   apply simp
  apply (case_tac "string_of_digit (x mod 10) = ''3''")
   apply (simp del: string_of_digit.simps)
   apply simp
  apply (case_tac "string_of_digit (x mod 10) = ''4''")
   apply (simp del: string_of_digit.simps)
   apply simp
  apply (case_tac "string_of_digit (x mod 10) = ''5''")
   apply (simp del: string_of_digit.simps)
  apply simp
  apply (case_tac "string_of_digit (x mod 10) = ''6''")
   apply (simp del: string_of_digit.simps)
   apply simp
  apply (case_tac "string_of_digit (x mod 10) = ''7''")
   apply (simp del: string_of_digit.simps)
   apply simp
  apply (case_tac "string_of_digit (x mod 10) = ''8''")
   apply (simp del: string_of_digit.simps)
   apply simp
  apply (case_tac "string_of_digit (x mod 10) = ''9''")
   apply (simp del: string_of_digit.simps)
   apply simp
  using string_of_digit_values by blast

lemma show_div: "showsp_nat 0 (x div 10) (string_of_digit (x mod 10)) = showsp_nat 0 (y div 10) (string_of_digit (y mod 10)) \<Longrightarrow>  showsp_nat 0 (x div 10) = showsp_nat 0 (y div 10)"
  apply (rule ext)
  by (metis append_equality append_same_eq showsp_append)

lemma induct_step: "showsp_nat 0 x = showsp_nat 0 y \<Longrightarrow> (showsp_nat 0 (x div 10) (string_of_digit (x mod 10))) = (showsp_nat 0 (y div 10) (string_of_digit (y mod 10)))"
  by (smt append_same_eq comp_apply length_showsp_nat_2 length_string_of_digit less_numeral_extra(4) mod_div_trivial mod_less mod_less_divisor shows_string_def showsp_append showsp_nat.simps zero_less_numeral)

lemma "showsp_nat 0 x = showsp_nat 0 y \<Longrightarrow> x = y"
  apply (simp add: showsp_nat.simps)
  apply (case_tac "x < 10")
   apply (case_tac "y < 10")
    apply (simp del: string_of_digit.simps add: shows_string_def)
    apply (metis append_same_eq string_of_digit_determinism)
   apply (simp del: string_of_digit.simps add: shows_string_def comp_def)
   apply (metis append_same_eq bar showsp_nat_append)
   apply (case_tac "y < 10")
  apply (metis (no_types, lifting) One_nat_def add.right_neutral another_length_one length_Cons length_append length_showsp_nat_2 length_string_of_digit less_numeral_extra(4) list.size(3) list.size(4) o_def shows_prec_nat_def shows_string_def showsp_nat.elims)
  apply (simp del: string_of_digit.simps add: shows_string_def comp_def showsp_nat_append_fun)
  oops

lemma last_string_of_digit: "xs @ [x] = showsp_nat 0 y [] \<Longrightarrow> [x] = (string_of_digit (y mod 10))"
  apply (simp add: showsp_nat.simps)
  apply (case_tac "y < 10")
   apply (simp add: shows_string_def)
   apply auto[1]
  apply (simp add: shows_string_def)
  apply safe
           apply simp
           apply (metis append1_eq_conv showsp_append)
          apply simp
          apply (metis append1_eq_conv showsp_append)
         apply simp
         apply (metis append1_eq_conv showsp_append)
        apply simp
        apply (metis append1_eq_conv showsp_append)
       apply simp
       apply (metis append1_eq_conv showsp_append)
      apply simp
      apply (metis append1_eq_conv showsp_append)
     apply simp
     apply (metis append1_eq_conv showsp_append)
    apply simp
    apply (metis append1_eq_conv showsp_append)
   apply simp
   apply (metis append1_eq_conv showsp_append)
  apply simp
  by (metis append1_eq_conv showsp_append)
  

lemma "x \<noteq> y \<Longrightarrow> show (x::nat) \<noteq> show y"
  apply safe
  apply (simp add: shows_prec_nat_def)
  apply (simp add: showsp_nat.simps)
  apply (case_tac "x < 10")
   apply (case_tac "y < 10")
    apply (simp del: string_of_digit.simps add: shows_string_def)
  using string_of_digit_determinism apply blast
    apply (simp del: string_of_digit.simps add: shows_string_def)
   apply (metis bar)
  apply (case_tac "y < 10")
   apply (simp del: string_of_digit.simps add: shows_string_def)
  using bar apply blast
   apply (simp del: string_of_digit.simps add: shows_string_def)
  oops




lemma foo: "showsp_nat 0 (x div 10) (string_of_digit (x mod 10)) = showsp_nat 0 (y div 10) (string_of_digit (y mod 10)) \<Longrightarrow> 10 \<le> x \<Longrightarrow> 10 \<le> y \<Longrightarrow> x = y"
  proof-
  assume first: "showsp_nat 0 (x div 10) (string_of_digit (x mod 10)) = showsp_nat 0 (y div 10) (string_of_digit (y mod 10))"
  assume second: "10 \<le> x"
  assume third: "10 \<le> y"
  have fourth: "string_of_digit (x mod 10) = string_of_digit (y mod 10)"
    using append_equality first by blast
  have fifth: "showsp_nat 0 (x div 10) = showsp_nat 0 (y div 10)"
    using first show_div by blast
  show "x = y"
    using first
    apply (simp only: move_string_of_digit)
    using fourth fifth
    apply (simp del: string_of_digit.simps add: shows_prec_nat_def)
    oops

lemma same_div_same_length: "(x :: nat) div 10 = (y :: nat) div 10 \<Longrightarrow> length (show x) = length (show y)"
  proof-
  fix x
  show "(x :: nat) div 10 = (y :: nat) div 10 \<Longrightarrow> length (show x) = length (show y)"
  proof (induct "y div 10")
    case 0
    then show ?case
      apply (simp add: show_zero_nat)
      apply (simp add: shows_prec_nat_def)
      using length_string_of_digit shows_string_def showsp_nat.simps by auto
  next
    case (Suc m)
    then show ?case
      apply (simp add: shows_prec_nat_def)
      by (smt Zero_not_Suc append_Nil2 div_less length_append length_string_of_digit move_string_of_digit o_def shows_string_def showsp_nat.simps)
  qed
qed

lemma drop_last: "show (x div 10) @ string_of_digit (x mod 10) = show (y div 10) @ string_of_digit (y mod 10) \<Longrightarrow> string_of_digit (x mod 10) = string_of_digit (y mod 10)"
  using append_equality move_string_of_digit by presburger

lemma "show (x::nat) = show y \<Longrightarrow> x = y"
  apply (simp add: shows_prec_nat_def)
  apply (simp add: showsp_nat.simps)
  apply (case_tac "x < 10")
   apply (case_tac "y < 10")
    apply (simp del: string_of_digit.simps add: shows_string_def)
  using string_of_digit_determinism apply blast
    apply (simp del: string_of_digit.simps add: shows_string_def)
   apply (metis bar)
   apply (case_tac "y < 10")
   apply (simp del: string_of_digit.simps add: shows_string_def)
  using bar apply blast
  apply (simp del: string_of_digit.simps add: shows_string_def)
  apply (simp only: move_string_of_digit)
  apply (simp only: shows_prec_nat_def)
  oops


end