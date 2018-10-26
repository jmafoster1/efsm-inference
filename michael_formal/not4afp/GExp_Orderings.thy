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

fun less_eq_aexp_aux :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" where
  "less_eq_aexp_aux (L l1) (L l2) = less_eq l1 l2" |
  "less_eq_aexp_aux (L _) _ = True" |
  "less_eq_aexp_aux (V _) (L _) = False" |
  "less_eq_aexp_aux (V v1) (V v2) = less_eq v1 v2" |
  "less_eq_aexp_aux (V _) _ = True" |
  "less_eq_aexp_aux (Plus _ _) (Minus _ _) = True" |
  "less_eq_aexp_aux (Plus f1 s1) (Plus f2 s2) = (if f1 = f2 then less_eq_aexp_aux s1 s2 else less_eq_aexp_aux f1 f2)" |
  "less_eq_aexp_aux (Plus _ _) _ = False" |
  "less_eq_aexp_aux (Minus f1 s1) (Minus f2 s2) = (if f1 = f2 then less_eq_aexp_aux s1 s2 else less_eq_aexp_aux f1 f2)" |
  "less_eq_aexp_aux (Minus a1 a2) _ = False"

definition less_aexp_aux :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" where
  "less_aexp_aux x y \<equiv> (less_eq_aexp_aux x y) \<and> (\<not>less_eq_aexp_aux y x)"

instantiation aexp :: linorder begin
definition less_eq_aexp :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" where
  "less_eq_aexp x y \<equiv> less_eq_aexp_aux x y"

definition less_aexp :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" where
  "less_aexp x y \<equiv> less_aexp_aux x y"

lemmas less_eq_defs = less_aexp_def less_eq_aexp_def less_aexp_aux_def

instance proof
  fix x y :: aexp
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (simp add: less_eq_defs)
next
  fix x:: aexp
  show "x \<le> x"
  proof (induct x)
    case (L x)
    then show ?case by (simp add: less_eq_defs)
  next
    case (V x)
    then show ?case by (simp add: less_eq_defs)
  next
    case (Plus x1 x2)
    then show ?case by (simp add: less_eq_defs)
  next
    case (Minus x1 x2)
    then show ?case by (simp add: less_eq_defs)
  qed
next
  fix x y z::aexp
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    apply (simp add: less_eq_defs)
  proof (induct x)
    case (L x)
    then show ?case
      apply (cases y)
         apply (metis L.prems(1) L.prems(2) aexp.exhaust less_eq_aexp_aux.simps(1) less_eq_aexp_aux.simps(2) less_eq_aexp_aux.simps(3) less_eq_aexp_aux.simps(4) order.trans)
        apply (metis aexp.exhaust less_eq_aexp_aux.simps(2) less_eq_aexp_aux.simps(3) less_eq_aexp_aux.simps(4) less_eq_aexp_aux.simps(5))
       apply (metis aexp.exhaust less_eq_aexp_aux.simps(11) less_eq_aexp_aux.simps(12) less_eq_aexp_aux.simps(3) less_eq_aexp_aux.simps(4))
      by (metis L.prems(2) aexp.exhaust less_eq_aexp_aux.simps(14) less_eq_aexp_aux.simps(15) less_eq_aexp_aux.simps(16) less_eq_aexp_aux.simps(4))
    next
    case (V x)
    then show ?case
      apply (cases y)
         apply simp
    proof -
      fix x2 :: vname
      assume a1: "less_eq_aexp_aux y z"
      assume a2: "y = V x2"
      assume a3: "less_eq_aexp_aux (V x) y"
      have f4: "\<forall>a. (\<exists>v. a = L v) \<or> (\<exists>v. a = V v) \<or> (\<exists>aa ab. a = Plus aa ab) \<or> (\<exists>aa ab. a = Minus aa ab)"
        by (meson aexp.exhaust)
      obtain aa :: "aexp \<Rightarrow> aexp" and aaa :: "aexp \<Rightarrow> aexp" where
        f5: "\<forall>x0. (\<exists>v1 v2. x0 = Minus v1 v2) = (x0 = Minus (aa x0) (aaa x0))"
        by moura
      obtain aab :: "aexp \<Rightarrow> aexp" and aac :: "aexp \<Rightarrow> aexp" where
        f6: "\<forall>x0. (\<exists>v1 v2. x0 = Plus v1 v2) = (x0 = Plus (aab x0) (aac x0))"
        by moura
      obtain vv :: "aexp \<Rightarrow> vname" where
        "\<forall>x0. (\<exists>v1. x0 = V v1) = (x0 = V (vv x0))"
        by moura
      then obtain vva :: "aexp \<Rightarrow> value" where
        "z = L (vva z) \<or> z = V (vv z) \<or> z = Plus (aab z) (aac z) \<or> z = Minus (aa z) (aaa z)"
        using f6 f5 f4 by meson
      then show ?thesis
        using a3 a2 a1 by (metis (no_types) dual_order.trans less_eq_aexp_aux.simps(5) less_eq_aexp_aux.simps(6) less_eq_aexp_aux.simps(7) less_eq_aexp_aux.simps(8))
    next
      show "\<And>x31 x32. less_eq_aexp_aux (V x) y \<Longrightarrow> less_eq_aexp_aux y z \<Longrightarrow> y = Plus x31 x32 \<Longrightarrow> less_eq_aexp_aux (V x) z"
        apply simp
        by (metis aexp.exhaust less_eq_aexp_aux.simps(11) less_eq_aexp_aux.simps(12) less_eq_aexp_aux.simps(7) less_eq_aexp_aux.simps(8))
    next
      show "\<And>x41 x42. less_eq_aexp_aux (V x) y \<Longrightarrow> less_eq_aexp_aux y z \<Longrightarrow> y = Minus x41 x42 \<Longrightarrow> less_eq_aexp_aux (V x) z "
        apply simp
        by (metis aexp.exhaust less_eq_aexp_aux.simps(14) less_eq_aexp_aux.simps(15) less_eq_aexp_aux.simps(16) less_eq_aexp_aux.simps(8))
    qed
  next
    case (Plus x1 x2)
    then show ?case
    proof (induct z)
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
      case (Plus y1 y2)
      then show ?case
        sorry
    next
      case (Minus y1 y2)
      then show ?case
        apply (cases z)
        by auto
    qed
  next
    case (Minus x1 x2)
    then show ?case
      sorry
  qed
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