theory Show_AExp
imports "../../AExp" "Show_VName" "Show_Value"
begin

instantiation aexp :: "show" begin
fun shows_prec_aexp :: "nat \<Rightarrow> aexp \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_prec_aexp n (L i) c = shows_prec n i c" |
  "shows_prec_aexp n (V i) c = shows_prec n i c" |
  "shows_prec_aexp a (Plus v va) c = ''(''@(shows_prec a v '''')@''+''@(shows_prec a va '''')@'')''@c"|
  "shows_prec_aexp a (Minus v va) c = ''(''@(shows_prec a v '''')@''-''@(shows_prec a va '''')@'')''@c"

fun shows_list_aexp :: "aexp list \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_list_aexp [] l = l" |
  "shows_list_aexp [u] l = shows_prec 0 u l" |
  "shows_list_aexp (h#t) l = (shows_prec 0 h '''')@'',''@(shows_list_aexp t l)"

lemma shows_prec_aexp_cases: "shows_prec p (y::aexp) (r @ s) = shows_prec p y r @ s"
  proof (induction y)
    case (L x)
    then show ?case by (simp add: shows_prec_append)
  next
    case (V x)
    then show ?case by (simp add: shows_prec_append)
  next
    case (Plus y1 y2)
    then show ?case by (simp add: shows_prec_append)
  next
    case (Minus y1 y2)
    then show ?case by (simp add: shows_prec_append)
  qed

instance proof
  fix y :: aexp
  fix r s p
  show "shows_prec p y (r @ s) = shows_prec p y r @ s"
    by (simp add: shows_prec_aexp_cases)
next
  fix xs :: "aexp list"
  fix r s p
  show "shows_list xs (r @ s) = shows_list xs r @ s"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case
    proof (induct xs)
      case Nil
      then show ?case by (simp add: shows_prec_aexp_cases)
    next
      case (Cons a xs)
      then show ?case by simp
    qed
  qed
qed
end

end