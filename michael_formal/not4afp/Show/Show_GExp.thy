theory Show_GExp
imports "../../GExp" Show_AExp
begin

instantiation gexp :: "show" begin
fun shows_prec_gexp :: "nat \<Rightarrow> gexp \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_prec_gexp n (Bc i) c = shows_prec n i c" |
  "shows_prec_gexp n (Eq v va) c = ''(''@(shows_prec n v '''')@''=''@(shows_prec n va '''')@'')''@c" |
  "shows_prec_gexp n (Gt v va) c = ''Gt(''@(shows_prec n v '''')@''>''@(shows_prec n va '''')@'')''@c" |
  "shows_prec_gexp n (Nor v va) c = ''Nor(''@(shows_prec n v '''')@'' ''@(shows_prec n va '''')@'')''@c" |
  "shows_prec_gexp n (Null v) c = ''NULL(''@(shows_prec n v '''')@'')''@c"

fun shows_list_gexp :: "gexp list \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_list_gexp [] l = l" |
  "shows_list_gexp [u] l = shows_prec 0 u l" |
  "shows_list_gexp (h#t) l = (shows_prec 0 h '''')@'',''@(shows_list_gexp t l)"

lemma shows_prec_cases:  "shows_prec p (x::gexp) (r @ s) = shows_prec p x r @ s"
  proof (cases x)
    case (Bc x1)
    then show ?thesis by (simp add: shows_prec_append)
  next
    case (Eq x21 x22)
    then show ?thesis by (simp add: shows_prec_append)
  next
    case (Gt x31 x32)
    then show ?thesis by (simp add: shows_prec_append)
  next
    case (Nor x41 x42)
    then show ?thesis by simp
  next
    case (Null x5)
    then show ?thesis
      by simp
  qed

instance proof
  fix x::gexp
  fix p r s
  show "shows_prec p x (r @ s) = shows_prec p x r @ s"
    by (simp add: shows_prec_cases)
next
  fix xs::"gexp list"
  fix p r s
  show "shows_list xs (r @ s) = shows_list xs r @ s"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case
    proof (induct xs)
      case Nil
      then show ?case
        by (simp add: shows_prec_cases)
    next
      case (Cons a xs)
      then show ?case
        by simp
    qed
  qed
qed
end

lemma show_g_not_empty: "show (g::gexp) \<noteq> ''''"
proof (cases g)
case (Bc x1)
  then show ?thesis
    apply (cases x1)
     apply (simp add: shows_string_def shows_prec_bool_def)
    by (simp add: shows_string_def shows_prec_bool_def)
next
  case (Eq x21 x22)
  then show ?thesis by simp
next
  case (Gt x31 x32)
  then show ?thesis by simp
next
  case (Nor x41 x42)
  then show ?thesis by simp
next
  case (Null x5)
  then show ?thesis by simp
qed

lemma deterministic_show_bool: "(show (a::gexp) = show (g::gexp)) \<Longrightarrow> (a = g)"
  oops

lemma show_gexp_determinism: "show (g1::gexp) = show (g2::gexp) \<Longrightarrow> g1 = g2"
  sorry

end
