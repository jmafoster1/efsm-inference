theory VName
imports Main
begin
datatype vname = I nat | R nat

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

end