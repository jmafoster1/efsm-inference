subsection \<open>Option Logic\<close>
text \<open>
This theory defines a three-valued logic such that nonsensical guard expressions cannot ever
evaluate to true. Such expressions evaluate instead to None which, when negated, is still None.
\<close>

theory Option_Logic
imports AExp
begin

fun MaybeBoolInt :: "(int \<Rightarrow> int \<Rightarrow> bool) \<Rightarrow> value option \<Rightarrow> value option \<Rightarrow> bool option" where
  "MaybeBoolInt f (Some (Num a)) (Some (Num b)) = Some (f a b)" |
  "MaybeBoolInt _ _ _ = None"

abbreviation ValueGt :: "value option \<Rightarrow> value option \<Rightarrow> bool option"  where
  "ValueGt a b \<equiv> MaybeBoolInt (\<lambda>x::int.\<lambda>y::int.(x>y)) a b"

abbreviation ValueLt :: "value option \<Rightarrow> value option \<Rightarrow> bool option"  where
  "ValueLt a b \<equiv> MaybeBoolInt (\<lambda>x::int.\<lambda>y::int.(x<y)) a b"

abbreviation ValueEq :: "value option \<Rightarrow> value option \<Rightarrow> bool option"  where
  "ValueEq a b \<equiv> MaybeBoolInt (\<lambda>x::int.\<lambda>y::int.(x=y)) a b"

abbreviation maybe_or :: "bool option \<Rightarrow> bool option \<Rightarrow> bool option" where
  "maybe_or x y \<equiv> (case (x, y) of
    (Some a, Some b) \<Rightarrow> Some (a \<or> b) |
    _ \<Rightarrow> None
  )"

abbreviation maybe_and :: "bool option \<Rightarrow> bool option \<Rightarrow> bool option" where
  "maybe_and x y \<equiv> (case (x, y) of
    (Some a, Some b) \<Rightarrow> Some (a \<and> b) |
    _ \<Rightarrow> None
  )"

abbreviation maybe_implies :: "bool option \<Rightarrow> bool option \<Rightarrow> bool option" where
  "maybe_implies x y \<equiv> (case (x, y) of
    (Some a, Some b) \<Rightarrow> Some (a \<longrightarrow> b) |
    _ \<Rightarrow> None
  )"

abbreviation maybe_not :: "bool option \<Rightarrow> bool option" where
  "maybe_not x \<equiv> (case x of Some a \<Rightarrow> Some (\<not>a) | None \<Rightarrow> None)"

lemma maybe_double_negation: "maybe_not (maybe_not x) = x"
  by (simp add: option.case_eq_if)

lemma maybe_negate: "(maybe_not c = Some b) = (c = Some (\<not>b))"
  by (metis (mono_tags, lifting) maybe_double_negation option.simps(5))

lemma maybe_not_values: "(maybe_not c \<noteq> Some False) = (maybe_not c = Some True \<or> maybe_not c = None)"
  by auto

lemma maybe_not_c: "(maybe_not c \<noteq> Some b) = (c = None \<or> c = Some b)"
  using maybe_not_values option.collapse by force

lemma maybe_negate_2: "(maybe_not c \<noteq> Some b) = (c \<noteq> Some (\<not>b))"
  by (simp add: maybe_negate)

lemma maybe_and_None: "maybe_and None x = None"
  by simp

lemma maybe_and_true: "(maybe_and x y = Some True) = (x = Some True \<and> y = Some True)"
  apply simp
  apply (case_tac x)
   apply simp+
  apply (case_tac y)
  by auto

lemma maybe_and_not_true: "(maybe_and x y \<noteq> Some True) = (x \<noteq> Some True \<or> y \<noteq> Some True)"
  apply simp
  apply (case_tac x)
   apply simp+
  apply (case_tac y)
  by auto

lemma maybe_and_commutative: "maybe_and x y = maybe_and y x"
  apply simp
  apply (case_tac x)
   apply simp
   apply (case_tac y)
    apply simp+
  apply (case_tac y)
  by auto

lemma maybe_and_zero: "maybe_and (Some True) x = x"
  apply (case_tac x)
  by auto

lemma maybe_and_one: "maybe_and x x = x"
  apply (case_tac x)
  by auto

end
