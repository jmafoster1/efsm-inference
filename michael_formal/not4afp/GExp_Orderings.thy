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
fun less_eq_aexp :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" where
  "less_eq_aexp (L l1) (L l2) = less_eq l1 l2" |
  "less_eq_aexp (L _) _ = True" |
  "less_eq_aexp (V _) (L _) = False" |
  "less_eq_aexp (V v1) (V v2) = less_eq v1 v2" |
  "less_eq_aexp (V _) _ = True" |
  "less_eq_aexp (Plus _ _) (Minus _ _) = True" |
  "less_eq_aexp (Plus f1 s1) (Plus f2 s2) = (if f1 = f2 then s1 \<le> s2 else f1 \<le> f2)" |
  "less_eq_aexp (Plus _ _) _ = False" |
  "less_eq_aexp (Minus f1 s1) (Minus f2 s2) = (if f1 = f2 then s1 \<le> s2 else f1 \<le> f2)" |
  "less_eq_aexp (Minus a1 a2) _ = False"

fun less_aexp :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" where
  "less_aexp (L l1) (L l2) = less l1 l2" |
  "less_aexp (L _) _ = True" |
  "less_aexp (V _) (L _) = False" |
  "less_aexp (V v1) (V v2) = less v1 v2" |
  "less_aexp (V _) _ = True" |
  "less_aexp (Plus _ _) (Minus _ _) = True" |
  "less_aexp (Plus f1 s1) (Plus f2 s2) = (if f1 = f2 then s1 < s2 else f1 < f2)" |
  "less_aexp (Plus _ _) _ = False" |
  "less_aexp (Minus f1 s1) (Minus f2 s2) = (if f1 = f2 then s1 < s2 else f1 < f2)" |
  "less_aexp (Minus a1 a2) _ = False"

instance proof
  fix x y :: aexp
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
    proof (induct y)
      case (L x)
      then show ?case
        by simp
    next
      case (V x)
      then show ?case
        by simp
    next
      case (Plus y1 y2)
      then show ?case
        sorry
    next
      case (Minus y1 y2)
      then show ?case
        by simp
    qed
  next
    case (Minus x1 x2)
    then show ?case
    proof (induct y)
      case (L x)
      then show ?case by simp
    next
      case (V x)
      then show ?case by simp
    next
      case (Plus y1 y2)
      then show ?case by simp
    next
      case (Minus y1 y2)
      then show ?case sorry
    qed
  qed
next
  fix x:: aexp
  show "x \<le> x"
  proof (induct x)
    case (L x)
    then show ?case by simp
  next
    case (V x)
    then show ?case by simp
  next
    case (Plus x1 x2)
    then show ?case by simp
  next
    case (Minus x1 x2)
    then show ?case by simp
  qed
next
  fix x y z::aexp
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    sorry
next
  fix x y::aexp
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
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
    then show ?case sorry
  next
    case (Minus x1 x2)
    then show ?case sorry
  qed
next
  fix x y::aexp
  show "x \<le> y \<or> y \<le> x"
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
    proof (induct y)
      case (L x)
      then show ?case by simp
    next
      case (V x)
      then show ?case by simp
    next
      case (Plus y1 y2)
      then show ?case sorry
    next
      case (Minus y1 y2)
      then show ?case by simp
    qed
  next
    case (Minus x1 x2)
    then show ?case
    proof (induct y)
      case (L x)
      then show ?case by simp
    next
      case (V x)
      then show ?case by simp
    next
      case (Plus y1 y2)
      then show ?case by simp
    next
      case (Minus y1 y2)
      then show ?case sorry
    qed
  qed
qed
end

instantiation gexp :: linorder begin
fun  less_eq_gexp :: "gexp \<Rightarrow> gexp \<Rightarrow> bool" where
  "(Bc x) \<le> (Bc y) = (x \<le> y)" |
  "(Bc x) \<le> _ = True" |
  "_ \<le> (Bc _) = False" |
  "(Eq a1 a2) \<le> (Eq b1 b2) = (if a1 = b1 then a2 \<le> b2 else a1 \<le> b1 )" |
  "(Eq _ _) \<le> _ = True" |
  "Gt _ _ \<le> Eq _ _ = False" |
  "(Gt a1 a2) \<le> (Gt b1 b2) = (if a1 = b1 then a2 \<le> b2 else a1 \<le> b1 )" |
  "(Gt _ _) \<le> _ = True" |
  "(Nor _ _) \<le> (Gt _ _) = False" |
  "(Nor a1 a2) \<le> (Nor b1 b2) = (if a1 = b1 then a2 \<le> b2 else a1 \<le> b1 )" |
  "(Nor _ _) \<le> (Null _) = True" |
  "(Null x) \<le> (Null y) = (x \<le> y)" |
  "(Null x) \<le> _ = False" |
  "_ \<le> (Eq _ _) = False"

fun  less_gexp :: "gexp \<Rightarrow> gexp \<Rightarrow> bool" where
  "(Bc x) < (Bc y) = (x < y)" |
  "(Bc x) < _ = True" |
  "_ < (Bc _) = False" |
  "(Eq a1 a2) < (Eq b1 b2) = (if a1 = b1 then a2 < b2 else a1 < b1 )" |
  "(Eq _ _) < _ = True" |
  "Gt _ _ < Eq _ _ = False" |
  "(Gt a1 a2) < (Gt b1 b2) = (if a1 = b1 then a2 < b2 else a1 < b1 )" |
  "(Gt _ _) < _ = True" |
  "(Nor _ _) < (Gt _ _) = False" |
  "(Nor a1 a2) < (Nor b1 b2) = (if a1 = b1 then a2 < b2 else a1 < b1 )" |
  "(Nor _ _) < (Null _) = True" |
  "(Null x) < (Null y) = (x < y)" |
  "(Null x) < _ = False" |
  "_ < (Eq _ _) = False"

instance proof
  fix x y::gexp
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
  proof (induct x)
    case (Bc x)
    then show ?case
    proof (induct y)
      case (Bc xa)
      then show ?case by auto
    next
      case (Eq x1a x2)
      then show ?case by simp
    next
      case (Gt x1a x2)
      then show ?case by simp
    next
      case (Nor y1 y2)
      then show ?case by simp
    next
      case (Null y)
      then show ?case by simp
    qed
  next
    case (Eq x1a x2)
    then show ?case
    proof (induct y)
      case (Bc x)
      then show ?case by simp
    next
      case (Eq x1a x2)
      then show ?case by auto
    next
      case (Gt y1 y2)
      then show ?case by simp
    next
      case (Nor y1 y2)
      then show ?case by simp
    next
      case (Null x)
      then show ?case by simp
    qed
  next
    case (Gt x1a x2)
    then show ?case
    proof (induct y)
      case (Bc x)
      then show ?case by simp
    next
      case (Eq x1a x2)
      then show ?case by simp
    next
      case (Gt x1a x2)
      then show ?case by auto
    next
      case (Nor y1 y2)
      then show ?case by simp
    next
      case (Null x)
      then show ?case by simp
    qed
  next
    case (Nor x1 x2)
    then show ?case
    proof (induct y)
      case (Bc x)
      then show ?case by simp
    next
      case (Eq x1a x2)
      then show ?case by simp
    next
      case (Gt x1a x2)
      then show ?case by simp
    next
      case (Nor y1 y2)
      then show ?case sorry
    next
      case (Null x)
      then show ?case
        by simp
    qed
  next
    case (Null x)
    then show ?case
    proof (induct y)
      case (Bc x)
      then show ?case by simp
    next
      case (Eq x1a x2)
      then show ?case by simp
    next
      case (Gt x1a x2)
      then show ?case by simp
    next
      case (Nor y1 y2)
      then show ?case by simp
    next
      case (Null x)
      then show ?case by auto
    qed
  qed
next
  fix x::gexp
  show "x \<le> x"
  proof (induct x)
    case (Bc x)
    then show ?case by simp
  next
    case (Eq x1a x2)
    then show ?case by simp
  next
    case (Gt x1a x2)
    then show ?case by simp
  next
    case (Nor x1 x2)
    then show ?case by simp
  next
    case (Null x)
    then show ?case by simp
  qed
next
  fix x y z::gexp
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  proof (induct x)
    case (Bc x)
    then show ?case
    proof (induct y)
      case (Bc x)
      then show ?case
        apply (cases z)
        by auto
    next
      case (Eq x1a x2)
      then show ?case
        apply (cases z)
        by auto
    next
      case (Gt x1a x2)
      then show ?case
        apply (cases z)
        by auto
    next
      case (Nor y1 y2)
      then show ?case
        apply (cases z)
        by auto
    next
      case (Null x)
      then show ?case
        apply (cases z)
        by auto
    qed
  next
    case (Eq x1a x2)
    then show ?case
    proof (induct y)
      case (Bc x)
      then show ?case
        apply (cases z)
        by auto
    next
      case (Eq x1a x2)
      then show ?case
        apply (cases z)
            apply simp
           apply (metis dual_order.trans eq_iff less_eq_gexp.simps(10))
        by auto
    next
      case (Gt x1a x2)
      then show ?case
        apply (cases z)
        by auto
    next
      case (Nor y1 y2)
      then show ?case
        apply (cases z)
        by auto
    next
      case (Null x)
      then show ?case
        apply (cases z)
        by auto
    qed
  next
    case (Gt x1a x2)
    then show ?case
    proof (induct y)
      case (Bc x)
      then show ?case
        apply (cases z)
        by auto
    next
      case (Eq x1a x2)
      then show ?case
        apply (cases z)
        by auto
    next
      case (Gt x1a x2)
      then show ?case
        apply (cases z)
            apply simp
           apply simp
        apply (metis dual_order.trans less_eq_gexp.simps(15) order_class.order.antisym)
        by auto
    next
      case (Nor y1 y2)
      then show ?case
        apply (cases z)
        by auto
    next
      case (Null x)
      then show ?case
        apply (cases z)
        by auto
    qed
  next
    case (Nor x1 x2)
    then show ?case
    proof (induct y)
      case (Bc x)
      then show ?case
        apply (cases z)
        by auto
    next
      case (Eq x1a x2)
      then show ?case
        apply (cases z)
        by auto
    next
      case (Gt x1a x2)
      then show ?case
        apply (cases z)
        by auto
    next
      case (Nor y1 y2)
      then show ?case
        apply (cases z)
            apply simp
           apply simp
          apply simp
        sorry
    next
      case (Null x)
      then show ?case
        apply (cases z)
        by auto
    qed
  next
    case (Null x)
    then show ?case sorry
  qed
next
  fix x y::gexp
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  proof (induct x)
    case (Bc x)
    then show ?case
      apply (cases y)
      by auto
  next
    case (Eq x1a x2)
    then show ?case
      apply (cases y)
          apply simp
         apply (metis antisym less_eq_gexp.simps(10))
      by auto
  next
    case (Gt x1a x2)
    then show ?case
      apply (cases y)
          apply simp
         apply simp
        apply (metis eq_iff less_eq_gexp.simps(15))
      by auto
  next
    case (Nor x1 x2)
    then show ?case
      apply (cases y)
          apply simp
         apply simp
        apply simp
      sorry
  next
    case (Null x)
    then show ?case
      apply (cases y)
      by auto
  qed
next
  fix x y::gexp
  show "x \<le> y \<or> y \<le> x"
  proof (induct x)
    case (Bc x)
    then show ?case
      apply (cases y)
      by auto
  next
    case (Eq x1a x2)
    then show ?case
      apply (cases y)
      by auto
  next
    case (Gt x1a x2)
    then show ?case
      apply (cases y)
      by auto
  next
    case (Nor x1 x2)
    then show ?case
      apply (cases y)
          apply simp
         apply simp
        apply simp
      sorry
  next
    case (Null x)
    then show ?case
      apply (cases y)
      by auto
  qed
qed
end

end