subsection \<open>Option Logic\<close>
text \<open>
This theory defines a three-valued logic such that nonsensical guard expressions cannot ever
evaluate to true. Such expressions evaluate instead to None which, when negated, is still None.
\<close>

theory Option_Logic
imports Main
begin

datatype trilean = true | false | invalid

fun maybe_not :: "trilean \<Rightarrow> trilean" ("\<not>\<^sub>? _" [60] 60) where
  "\<not>\<^sub>? true = false" |
  "\<not>\<^sub>? false = true" |
  "\<not>\<^sub>? invalid = invalid"

fun maybe_and :: "trilean \<Rightarrow> trilean \<Rightarrow> trilean" (infixl "\<and>\<^sub>?" 60) where
  "_ \<and>\<^sub>? invalid = invalid" |
  "invalid \<and>\<^sub>? _ = invalid" |
  "true \<and>\<^sub>? true = true" |
  "_ \<and>\<^sub>? false = false" |
  "false \<and>\<^sub>? _ = false" 

fun maybe_or :: "trilean \<Rightarrow> trilean \<Rightarrow> trilean" (infixl "\<or>\<^sub>?" 60) where
  "invalid \<or>\<^sub>? _ = invalid" |
  "_ \<or>\<^sub>? invalid = invalid" |
  "true \<or>\<^sub>? _ = true" |
  "_ \<or>\<^sub>? true = true" |
  "false \<or>\<^sub>? false = false"


lemma maybe_and_associative: "a \<and>\<^sub>? b \<and>\<^sub>? c = a \<and>\<^sub>? (b \<and>\<^sub>? c)"
proof(induct a b arbitrary: c rule: maybe_or.induct)
case (1 uu)
  then show ?case
  proof -
    have "invalid \<and>\<^sub>? (uu \<and>\<^sub>? c) \<noteq> invalid \<longrightarrow> invalid \<and>\<^sub>? (uu \<and>\<^sub>? c) = invalid"
      by (metis (no_types) maybe_and.simps(1) maybe_and.simps(2) maybe_and.simps(3) trilean.exhaust)
    then show ?thesis
      by (metis (full_types) maybe_and.simps(1) maybe_and.simps(2) maybe_and.simps(3) trilean.exhaust)
  qed
next
  case "2_1"
  then show ?case
    by (metis (full_types) maybe_and.simps(1) maybe_and.simps(4) maybe_and.simps(5) maybe_not.cases)
next
  case "2_2"
  then show ?case
    by (metis maybe_and.simps(1) maybe_and.simps(2) maybe_and.simps(3) maybe_not.cases)
next
  case "3_1"
  then show ?case
    by (metis maybe_and.simps(4) maybe_and.simps(5) trilean.exhaust)
next
  case "3_2"
  then show ?case
    by (metis maybe_and.simps(1) maybe_and.simps(4) maybe_and.simps(5) maybe_not.cases)
next
  case 4
  then show ?case
    by (metis maybe_and.simps(1) maybe_and.simps(4) maybe_and.simps(5) maybe_and.simps(7) maybe_not.cases)
next
  case 5
  then show ?case
    by (metis maybe_and.simps(1) maybe_and.simps(6) trilean.exhaust)
qed

lemma maybe_and_commutative: "a \<and>\<^sub>? b = b \<and>\<^sub>? a"
  by (metis (full_types) maybe_and.simps(1) maybe_and.simps(2) maybe_and.simps(3) maybe_and.simps(5) maybe_and.simps(7) trilean.distinct(5) trilean.exhaust)

lemma maybe_or_associative: "a \<or>\<^sub>? b \<or>\<^sub>? c = a \<or>\<^sub>? (b \<or>\<^sub>? c)"
proof(induct a b  arbitrary: c rule: maybe_or.induct)
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
    by (metis maybe_not.cases maybe_or.simps(2) maybe_or.simps(4))
next
  case "3_2"
  then show ?case
    by (metis maybe_not.cases maybe_or.simps(3) maybe_or.simps(5) maybe_or.simps(6) maybe_or.simps(7))
next
  case 4
  then show ?case
    by (metis maybe_not.cases maybe_or.simps(2) maybe_or.simps(3) maybe_or.simps(4) maybe_or.simps(5) maybe_or.simps(6))
next
  case 5
  then show ?case
    by (metis maybe_not.cases maybe_or.simps(6) maybe_or.simps(7))
qed

lemma maybe_or_commutative: "a \<or>\<^sub>? b = b \<or>\<^sub>? a"
proof(induct a b rule: maybe_or.induct)
  case (1 uu)
  then show ?case
    by (metis maybe_or.simps(1) maybe_or.simps(2) maybe_or.simps(3) trilean.exhaust)
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

lemma trilean_distributivity: "a \<or>\<^sub>? b \<and>\<^sub>? c = a \<and>\<^sub>? c \<or>\<^sub>? (b \<and>\<^sub>? c)"
proof(induct a b  arbitrary: c rule: maybe_or.induct)
case (1 uu)
  then show ?case
    by (metis maybe_and.simps(1) maybe_and_commutative maybe_or.simps(1))
next
case "2_1"
  then show ?case
    by (metis maybe_and.simps(1) maybe_and_commutative maybe_or.simps(1) maybe_or_commutative)
next
  case "2_2"
  then show ?case
    by (metis maybe_and.simps(1) maybe_and_commutative maybe_or.simps(1) maybe_or_commutative)
next
  case "3_1"
  then show ?case
    by (metis maybe_and.simps(1) maybe_and.simps(4) maybe_and.simps(7) maybe_and_commutative maybe_not.simps(1) maybe_not.simps(3) maybe_or.simps(1) maybe_or.simps(4) maybe_or.simps(7) trilean.exhaust trilean.simps(2) trilean.simps(6))
next
  case "3_2"
  then show ?case
    by (metis maybe_and.simps(1) maybe_and.simps(4) maybe_and.simps(6) maybe_and.simps(7) maybe_and_commutative maybe_or.simps(1) maybe_or.simps(5) maybe_or.simps(7) trilean.exhaust trilean.simps(6))
next
  case 4
  then show ?case
    by (metis maybe_and.simps(1) maybe_and.simps(4) maybe_and.simps(6) maybe_and.simps(7) maybe_and_commutative maybe_or.simps(1) maybe_or.simps(6) maybe_or.simps(7) trilean.exhaust)
next
case 5
  then show ?case
    by (metis maybe_and.simps(1) maybe_and.simps(6) maybe_and.simps(7) maybe_and_commutative maybe_or.simps(1) maybe_or.simps(7) trilean.exhaust trilean.simps(6))
qed

instantiation trilean :: semiring begin
definition [simp]: "times_trilean = maybe_and"

definition [simp]: "plus_trilean = maybe_or"

instance
  apply standard
      apply (simp add: maybe_or_associative)
     apply (simp add: maybe_or_commutative)
    apply (simp add: maybe_and_associative)
   apply (simp add: trilean_distributivity)
  using maybe_and_commutative trilean_distributivity by auto
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

lemma maybe_and_true: "(x \<and>\<^sub>? y = true) = (x = true \<and> y = true)"
  using maybe_and.elims by blast

lemma maybe_and_not_true: "(x \<and>\<^sub>? y \<noteq> true) = (x \<noteq> true \<or> y \<noteq> true)"
  by (simp add: maybe_and_true)

lemma maybe_and_valid: "x \<and>\<^sub>? y \<noteq> invalid \<Longrightarrow> x \<noteq> invalid \<and> y \<noteq> invalid"
  using maybe_and.elims by blast

lemma maybe_or_valid: "x \<or>\<^sub>? y \<noteq> invalid \<Longrightarrow> x \<noteq> invalid \<and> y \<noteq> invalid"
  using maybe_or.elims by blast
end