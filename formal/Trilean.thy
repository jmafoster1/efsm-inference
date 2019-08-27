theory Trilean
imports Main
begin

datatype trilean = true | false | invalid

instantiation trilean :: semiring begin
fun times_trilean :: "trilean \<Rightarrow> trilean \<Rightarrow> trilean" where
  "times_trilean _ invalid = invalid" |
  "times_trilean invalid _ = invalid" |
  "times_trilean true true = true" |
  "times_trilean _ false = false" |
  "times_trilean false _ = false" 

fun plus_trilean :: "trilean \<Rightarrow> trilean \<Rightarrow> trilean" where
  "plus_trilean invalid _ = invalid" |
  "plus_trilean _ invalid = invalid" |
  "plus_trilean true _ = true" |
  "plus_trilean _ true = true" |
  "plus_trilean false false = false"

abbreviation maybe_and :: "trilean \<Rightarrow> trilean \<Rightarrow> trilean" (infixl "\<and>\<^sub>?" 70) where
  "maybe_and x y \<equiv> x * y"

abbreviation maybe_or :: "trilean \<Rightarrow> trilean \<Rightarrow> trilean" (infixl "\<or>\<^sub>?" 65) where
  "maybe_or x y \<equiv> x + y"

lemma plus_trilean_assoc: "a \<or>\<^sub>? b \<or>\<^sub>? c = a \<or>\<^sub>? (b \<or>\<^sub>? c)"
proof(induct a b  arbitrary: c rule: plus_trilean.induct)
case (1 uu)
  then show ?case
    by simp
next
  case "2_1"
  then show ?case
    by simp
next
  case "2_2"
  then show ?case
    by simp
next
  case "3_1"
  then show ?case
    by (metis plus_trilean.simps(2) plus_trilean.simps(4) trilean.exhaust)
next
  case "3_2"
  then show ?case
    by (metis plus_trilean.simps(3) plus_trilean.simps(5) plus_trilean.simps(6) plus_trilean.simps(7) trilean.exhaust)
next
  case 4
  then show ?case
    by (metis plus_trilean.simps(2) plus_trilean.simps(3) plus_trilean.simps(4) plus_trilean.simps(5) plus_trilean.simps(6) trilean.exhaust)
next
  case 5
  then show ?case
    by (metis plus_trilean.simps(6) plus_trilean.simps(7) trilean.exhaust)
qed

lemma plus_trilean_commutative: "a \<or>\<^sub>? b = b \<or>\<^sub>? a"
proof(induct a b rule: plus_trilean.induct)
  case (1 uu)
  then show ?case
    by (metis plus_trilean.simps(1) plus_trilean.simps(2) plus_trilean.simps(3) trilean.exhaust)
next
  case "2_1"
  then show ?case
    by simp
next
  case "2_2"
  then show ?case
    by simp
next
  case "3_1"
  then show ?case
    by simp
next
  case "3_2"
  then show ?case
    by simp
next
  case 4
  then show ?case
    by simp
next
  case 5
  then show ?case
    by simp
qed

lemma times_trilean_commutative: "a \<and>\<^sub>? b = b \<and>\<^sub>? a"
  by (metis (mono_tags) times_trilean.simps trilean.distinct(5) trilean.exhaust)

lemma times_trilean_assoc: "a \<and>\<^sub>? b \<and>\<^sub>? c = a \<and>\<^sub>? (b \<and>\<^sub>? c)"
proof(induct a b  arbitrary: c rule: plus_trilean.induct)
  case (1 uu)
  then show ?case
    by (metis (mono_tags, lifting) times_trilean.simps(1) times_trilean_commutative)
next
case "2_1"
  then show ?case
    by (metis (mono_tags, lifting) times_trilean.simps(1) times_trilean_commutative)
next
  case "2_2"
  then show ?case
    by (metis (mono_tags, lifting) times_trilean.simps(1) times_trilean_commutative)
next
  case "3_1"
  then show ?case
    by (metis times_trilean.simps(1) times_trilean.simps(4) times_trilean.simps(5) trilean.exhaust)
next
  case "3_2"
  then show ?case
    by (metis times_trilean.simps(1) times_trilean.simps(5) times_trilean.simps(6) times_trilean.simps(7) trilean.exhaust)
next
  case 4
  then show ?case
    by (metis times_trilean.simps(1) times_trilean.simps(4) times_trilean.simps(5) times_trilean.simps(7) trilean.exhaust)
next
case 5
  then show ?case
    by (metis (full_types) times_trilean.simps(1) times_trilean.simps(6) times_trilean.simps(7) trilean.exhaust)
qed

lemma trilean_distributivity_1: "(a \<or>\<^sub>? b) \<and>\<^sub>? c = a \<and>\<^sub>? c \<or>\<^sub>? b \<and>\<^sub>? c"
proof(induct a b rule: times_trilean.induct)
case (1 uu)
  then show ?case
    by (metis (mono_tags, lifting) plus_trilean.simps(1) plus_trilean_commutative times_trilean.simps(1) times_trilean_commutative)
next
  case "2_1"
  then show ?case
    by (metis (mono_tags, lifting) plus_trilean.simps(1) times_trilean.simps(1) times_trilean_commutative)
next
  case "2_2"
  then show ?case
    by (metis (mono_tags, lifting) plus_trilean.simps(1) times_trilean.simps(1) times_trilean_commutative)
next
  case 3
  then show ?case
    apply simp
    by (metis (no_types, hide_lams) plus_trilean.simps(1) plus_trilean.simps(4) plus_trilean.simps(7) times_trilean.simps(1) times_trilean.simps(4) times_trilean.simps(5) trilean.exhaust)
next
  case "4_1"
  then show ?case 
    apply simp
    by (metis (no_types, hide_lams) plus_trilean.simps(1) plus_trilean.simps(5) plus_trilean.simps(7) times_trilean.simps(1) times_trilean.simps(4) times_trilean.simps(5) times_trilean.simps(6) times_trilean.simps(7) trilean.exhaust)
next
  case "4_2"
  then show ?case
    apply simp
    by (metis (no_types, hide_lams) plus_trilean.simps(1) plus_trilean.simps(7) times_trilean.simps(1) times_trilean.simps(6) times_trilean.simps(7) trilean.exhaust)
next
  case 5
  then show ?case
    apply simp
    by (metis (no_types, hide_lams) plus_trilean.simps(1) plus_trilean.simps(6) plus_trilean.simps(7) times_trilean.simps(1) times_trilean.simps(4) times_trilean.simps(5) times_trilean.simps(6) times_trilean.simps(7) trilean.exhaust)
qed

instance
  apply standard
      apply (simp add: plus_trilean_assoc)
     apply (simp add: plus_trilean_commutative)
    apply (simp add: times_trilean_assoc)
   apply (simp add: trilean_distributivity_1)
  using times_trilean_commutative trilean_distributivity_1 by auto
end

lemma maybe_or_idempotent: "a \<or>\<^sub>? a = a"
  apply (cases a)
  by auto

lemma maybe_and_idempotent: "a \<and>\<^sub>? a = a"
  apply (cases a)
  by auto

instantiation trilean :: ord begin
definition less_eq_trilean :: "trilean \<Rightarrow> trilean \<Rightarrow> bool" where
  "less_eq_trilean a b = (a + b = b)"

definition less_trilean :: "trilean \<Rightarrow> trilean \<Rightarrow> bool" where
  "less_trilean a b = (a \<le> b \<and> a \<noteq> b)"

declare less_trilean_def less_eq_trilean_def [simp]

instance
  by standard
end

instantiation trilean :: uminus begin
  fun maybe_not :: "trilean \<Rightarrow> trilean" ("\<not>\<^sub>? _" [60] 60) where
    "\<not>\<^sub>? true = false" |
    "\<not>\<^sub>? false = true" |
    "\<not>\<^sub>? invalid = invalid"

instance
  by standard
end

lemma maybe_and_one: "true \<and>\<^sub>? x = x"
  apply (cases x)
  by auto

lemma maybe_or_zero: "false \<or>\<^sub>? x = x"
  apply (cases x)
  by auto

lemma maybe_double_negation: "\<not>\<^sub>? \<not>\<^sub>? x = x"
  apply (cases x)
  by auto

lemma maybe_negate_true: "(\<not>\<^sub>? x = true) = (x = false)"
  apply (cases x)
  by auto

lemma maybe_negate_false: "(\<not>\<^sub>? x = false) = (x = true)"
  apply (cases x)
  by auto

lemma maybe_and_true: "(x \<and>\<^sub>? y = true) = (x = true \<and> y = true)"
  using times_trilean.elims by blast

lemma maybe_and_not_true: "(x \<and>\<^sub>? y \<noteq> true) = (x \<noteq> true \<or> y \<noteq> true)"
  by (simp add: maybe_and_true)

lemma negate_valid: "(\<not>\<^sub>? x \<noteq> invalid) = (x \<noteq> invalid)"
  by (metis maybe_double_negation maybe_not.simps(3))

lemma maybe_and_valid: "x \<and>\<^sub>? y \<noteq> invalid \<Longrightarrow> x \<noteq> invalid \<and> y \<noteq> invalid"
  using times_trilean.elims by blast

lemma maybe_or_valid: "x \<or>\<^sub>? y \<noteq> invalid \<Longrightarrow> x \<noteq> invalid \<and> y \<noteq> invalid"
  using plus_trilean.elims by blast

lemma maybe_or_false: "(x \<or>\<^sub>? y = false) = (x = false \<and> y = false)"
  using plus_trilean.elims by blast

lemma maybe_or_true: "(x \<or>\<^sub>? y = true) = ((x = true \<or> y = true) \<and> x \<noteq> invalid \<and> y \<noteq> invalid)"
  using plus_trilean.elims by blast

lemma maybe_not_invalid: "(\<not>\<^sub>? x = invalid) = (x = invalid)"
  by (metis maybe_double_negation maybe_not.simps(3))

lemma maybe_or_invalid: "(x \<or>\<^sub>? y = invalid) = (x = invalid \<or> y = invalid)"
  using plus_trilean.elims by blast

lemma maybe_and_invalid: "(x \<and>\<^sub>? y = invalid) = (x = invalid \<or> y = invalid)"
  using times_trilean.elims by blast

lemma maybe_and_false: "(x \<and>\<^sub>? y = false) = ((x = false \<or> y = false) \<and> x \<noteq> invalid \<and> y \<noteq> invalid)"
  using times_trilean.elims by blast

lemma invalid_maybe_and: "invalid \<and>\<^sub>? x = invalid"
  using maybe_and_valid by blast

lemma maybe_not_eq: "(\<not>\<^sub>? x = \<not>\<^sub>? y) = (x = y)"
  by (metis maybe_double_negation)

lemma de_morgans_1: "\<not>\<^sub>? (a \<or>\<^sub>? b) = (\<not>\<^sub>?a) \<and>\<^sub>? (\<not>\<^sub>?b)"
  by (metis (no_types, hide_lams) add.commute invalid_maybe_and maybe_and_idempotent maybe_and_one maybe_not.elims maybe_not.simps(1) maybe_not.simps(3) maybe_not_invalid maybe_or_zero plus_trilean.simps(1) plus_trilean.simps(4) times_trilean.simps(1) times_trilean_commutative trilean.exhaust trilean.simps(6))

lemma de_morgans_2: "\<not>\<^sub>? (a \<and>\<^sub>? b) = (\<not>\<^sub>?a) \<or>\<^sub>? (\<not>\<^sub>?b)"
  by (metis de_morgans_1 maybe_double_negation)

lemma not_true: "(x \<noteq> true) = (x = false \<or> x = invalid)"
  by (metis (no_types, lifting) maybe_not.cases trilean.distinct(1) trilean.distinct(3))

lemma pull_negation: "(x = \<not>\<^sub>? y) = (\<not>\<^sub>? x = y)"
  using maybe_double_negation by auto

end