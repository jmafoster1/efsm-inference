theory Value
imports Trilean
begin

text_raw\<open>\snip{valuetype}{1}{2}{%\<close>
datatype "value" = Num int | Str String.literal
text_raw\<open>}%endsnip\<close>

fun is_Num :: "value \<Rightarrow> bool" where
  "is_Num (Num _) = True" |
  "is_Num (Str _) = False"

fun MaybeBoolInt :: "(int \<Rightarrow> int \<Rightarrow> bool) \<Rightarrow> value option \<Rightarrow> value option \<Rightarrow> trilean" where
  "MaybeBoolInt f (Some (Num a)) (Some (Num b)) = (if f a b then true else false)" |
  "MaybeBoolInt _ _ _ = invalid"

lemma MaybeBoolInt_lt: "MaybeBoolInt (\<lambda>x y. y < x) (Some (Num n')) r = false \<Longrightarrow> \<exists>n. r = Some (Num n) \<and> n' \<le> n"
proof(induct n')
  case (nonneg n)
  then show ?case
    using MaybeBoolInt.elims by force
next
  case (neg n)
  then show ?case
    using MaybeBoolInt.elims by force
qed

lemma MaybeBoolInt_not_num_1: "\<forall>n. r \<noteq> Some (Num n) \<Longrightarrow> MaybeBoolInt f n r = invalid"
  apply (cases r)
   apply simp
  apply (case_tac a)
  by auto

definition value_gt :: "value option \<Rightarrow> value option \<Rightarrow> trilean"  where
  "value_gt a b \<equiv> MaybeBoolInt (\<lambda>x::int.\<lambda>y::int.(x>y)) a b"

definition value_eq :: "value option \<Rightarrow> value option \<Rightarrow> trilean"  where
  "value_eq a b \<equiv> (if a = b then true else false)"
declare value_eq_def [simp]

instantiation "value" :: linorder begin
fun less_eq_value :: "value \<Rightarrow> value \<Rightarrow> bool" where
  "less_eq_value (Num n) (Str s) = True" |
  "less_eq_value (Str s) (Num n) = False" |
  "less_eq_value (Str n) (Str s) = less_eq n s" |
  "less_eq_value (Num n) (Num s) = less_eq n s"

fun less_value :: "value \<Rightarrow> value \<Rightarrow> bool" where
  "less_value (Num n) (Str s) = True" |
  "less_value (Str s) (Num n) = False" |
  "less_value (Str n) (Str s) = less n s" |
  "less_value (Num n) (Num s) = less n s"

instance proof
  fix x y::"value"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
  proof (induct x)
    case (Num x)
    then show ?case
      apply (cases y)
      by auto
  next
    case (Str x)
    then show ?case
      apply (cases y)
      by auto
  qed
  fix x :: "value"
  show "x \<le> x"
    apply (cases x)
    by auto
  fix x y z::"value"
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  proof (induct x)
    case (Num n)
    then show ?case
    proof (induct y)
      case (Num x)
      then show ?case
        apply (cases z)
        by auto
    next
      case (Str x)
      then show ?case
        apply (cases z)
        by auto
    qed
  next
    case (Str s)
    then show ?case
    proof (induct y)
      case (Num x)
      then show ?case
        apply (cases z)
        by auto
    next
      case (Str x)
      then show ?case
        apply (cases z)
        by auto
    qed
  qed
next
  fix x y :: "value"
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  proof (induct x)
    case (Num x)
    then show ?case
      apply (cases y)
      by auto
  next
    case (Str x)
    then show ?case
      apply (cases y)
      by auto
  qed
next
  fix x y::"value"
  show "x \<le> y \<or> y \<le> x"
  proof (induct x)
    case (Num x)
    then show ?case
      apply (cases y)
      by auto
  next
    case (Str x)
    then show ?case
      apply (cases y)
      by auto
  qed
qed
end

end