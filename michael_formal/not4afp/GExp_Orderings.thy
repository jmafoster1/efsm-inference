theory GExp_Orderings
imports "../GExp"
begin

(* datatype vname = I nat | R nat *)
(* datatype gexp = Bc bool | Eq aexp aexp | Gt aexp aexp | Nor gexp gexp | Null vname *)

instantiation vname :: linorder begin
fun less_eq_vname :: "vname \<Rightarrow> vname \<Rightarrow> bool" where
  "less_eq_vname (I n1) (R n2) = True" |
  "less_eq_vname (R n1) (I n2) = False" |
  "less_eq_vname (I n1) (I n2) = less_eq n1 n2" |
  "less_eq_vname (R n1) (R n2) = less_eq n1 n2"

fun less_vname :: "vname \<Rightarrow> vname \<Rightarrow> bool" where
  "less_vname (I n1) (R n2) = True" |
  "less_vname (R n1) (I n2) = False" |
  "less_vname (I n1) (I n2) = less n1 n2" |
  "less_vname (R n1) (R n2) = less n1 n2"

instance proof
  fix x y :: vname
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
  proof (induct x)
    case (I n)
    then show ?case
    proof (induct y)
      case (I m)
      then show ?case
        by auto
    next
      case (R m)
      then show ?case
        by simp
    qed
  next
    case (R n)
    then show ?case
    proof (induct y)
      case (I x)
      then show ?case
        by simp
    next
      case (R x)
      then show ?case
        by auto
    qed
  qed
next
  fix x :: vname
  show "x \<le> x"
  proof (induct x)
    case (I x)
    then show ?case
      by auto
  next
    case (R x)
    then show ?case
      by auto
  qed
next
  fix x y z::vname
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  proof (induct x)
    case (I x)
    then show ?case
    proof (induct y)
      case (I xa)
      then show ?case
        apply (cases z)
        by auto
    next
      case (R xa)
      then show ?case
        apply (cases z)
        by auto
    qed
  next
    case (R x)
    then show ?case
    proof (induct y)
      case (I xa)
      then show ?case
        apply (cases z)
        by auto
    next
      case (R xa)
      then show ?case
        apply (cases z)
        by auto
    qed
  qed
next
  fix x y:: vname
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  proof (induct x)
    case (I x)
    then show ?case
      apply (cases y)
      by auto
  next
    case (R x)
    then show ?case
      apply (cases y)
      by auto
  qed
next
  fix x y:: vname
  show "x \<le> y \<or> y \<le> x"
  proof (induct x)
    case (I x)
    then show ?case
      apply (cases y)
      by auto
  next
    case (R x)
    then show ?case
      apply (cases y)
      by auto
  qed
qed
end

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

instantiation aexp :: linorder begin

fun less_eq_aexp :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" and
     less_aexp :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" where

  "less_eq_aexp (L l1) (L l2) = less_eq l1 l2" |
  "less_eq_aexp (V v1) (V v2) = less_eq v1 v2" |
  "less_eq_aexp (Plus a1 a2) (Plus b1 b2) = (if a1 = b1 then less_eq a2 b2 else (if a1 < a2 then True else False))" |
  "less_eq_aexp (Minus a1 a2) (Minus b1 b2) = (if a1 = b1 then less_eq a2 b2 else (if a1 < a2 then True else False))" |
  "less_eq_aexp (L _) _ = True" |
  "less_eq_aexp (V _) (L _) = False" |
  "less_eq_aexp (V _) _ = True" |
  "less_eq_aexp (Plus a b) (Minus c d) = True" |
  "less_eq_aexp (Plus a b) _ = False" |
  "less_eq_aexp (Minus a b) _ = False" |

  "less_aexp (L l1) (L l2) = less l1 l2" |
  "less_aexp (V v1) (V v2) = less v1 v2" |
  "less_aexp (Plus a1 a2) (Plus b1 b2) = (if a1 = b1 then less_eq a2 b2 else (if a1 \<le> a2 then True else False))" |
  "less_aexp (Minus a1 a2) (Minus b1 b2) = (if a1 = b1 then less_eq a2 b2 else (if a1 \<le> a2 then True else False))" |
  "less_aexp (L _) _ = True" |
  "less_aexp (V _) (L _) = False" |
  "less_aexp (V _) _ = True" |
  "less_aexp (Plus a b) (Minus c d) = True" |
  "less_aexp (Plus a b) _ = False" |
  "less_aexp (Minus a b) _ = False"

instance
proof
  fix x y::aexp
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
  proof (induct x)
    case (L x)
    then show ?case
      apply (cases y)
      by auto
  next
    case (V x)
    then show ?case
      apply (cases y)
      by auto
  next
    case (Plus x1 x2)
    then show ?case
      apply (cases y)
         apply simp
        apply simp
next
  case (Minus x1 x2)
  then show ?case sorry
qed

end

end