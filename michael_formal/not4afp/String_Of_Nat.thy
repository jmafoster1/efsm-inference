theory String_Of_Nat
imports "Show.Show_Instances"
begin

lemma string_of_0: "(string_of_digit x = ''0'') = (x = 0)"
  by simp

lemma string_of_1: "(string_of_digit x = ''1'') = (x = 1)"
  by simp

lemma string_of_suc_0: "string_of_digit (Suc 0) = ''1''"
  by simp

lemma string_of_2: "(string_of_digit x = ''2'') = (x = 2)"
  by simp

lemma string_of_3: "(string_of_digit x = ''3'') = (x = 3)"
  by simp

lemma string_of_4: "(string_of_digit x = ''4'') = (x = 4)"
  by simp

lemma string_of_5: "(string_of_digit x = ''5'') = (x = 5)"
  by simp

lemma string_of_6: "(string_of_digit x = ''6'') = (x = 6)"
  by simp

lemma string_of_7: "(string_of_digit x = ''7'') = (x = 7)"
  by simp

lemma string_of_8: "(string_of_digit x = ''8'') = (x = 8)"
  by simp

lemma string_of_9: "(string_of_digit x = ''9'') = (x \<ge> 9)"
  by simp

lemma string_of_digit_values: "string_of_digit x = ''0'' \<or>
string_of_digit x = ''1'' \<or>
string_of_digit x = ''2'' \<or>
string_of_digit x = ''3'' \<or>
string_of_digit x = ''4'' \<or>
string_of_digit x = ''5'' \<or>
string_of_digit x = ''6'' \<or>
string_of_digit x = ''7'' \<or>
string_of_digit x = ''8'' \<or>
string_of_digit x = ''9''"
  by simp

lemma string_of_digit_determinism: "string_of_digit x = string_of_digit y \<Longrightarrow> x < 10 \<Longrightarrow> y < 10 \<Longrightarrow> x = y"
  apply (case_tac "x=0")
  using string_of_0 apply fastforce
  apply (case_tac "x=1")
   apply (simp del: string_of_digit.simps One_nat_def)
  using string_of_1 apply fastforce
  apply (case_tac "x=2")
   apply (simp del: string_of_digit.simps One_nat_def)
  using string_of_2 apply fastforce
  apply (case_tac "x=3")
   apply (simp del: string_of_digit.simps One_nat_def)
  using string_of_3 apply fastforce
  apply (case_tac "x=4")
   apply (simp del: string_of_digit.simps One_nat_def)
  using string_of_4 apply fastforce
  apply (case_tac "x=5")
   apply (simp del: string_of_digit.simps One_nat_def)
  using string_of_5 apply fastforce
  apply (case_tac "x=6")
   apply (simp del: string_of_digit.simps One_nat_def)
  using string_of_6 apply fastforce
  apply (case_tac "x=7")
   apply (simp del: string_of_digit.simps One_nat_def)
  using string_of_7 apply fastforce
  apply (case_tac "x=8")
   apply (simp del: string_of_digit.simps One_nat_def)
  using string_of_8 apply fastforce
  apply (case_tac "x=9")
   apply (simp del: string_of_digit.simps One_nat_def)
   apply (metis Suc_leI le_neq_trans not_less numeral_eq_Suc order_refl pred_numeral_simps(2) semiring_norm(28) string_of_9)
  by simp

end