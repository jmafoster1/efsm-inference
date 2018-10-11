subsection {* Guard Expressions *}
text{*
This theory defines the guard language of EFSMs which can be translated directly to and from
contexts. This is similar to boolean expressions from IMP \cite{fixme}. Boolean values true and
false respectively represent the guards which are always and never satisfied. Guards may test
for (in)equivalence of two arithmetic expressions or be connected using nor logic into compound
expressions. Additionally, a guard may also test to see if a particular variable is null. This is
useful if an EFSM transition is intended only to initialise a register.  We also define syntax hacks
for the relations less than, less than or equal to, greater than or equal to, and not equal to as
well as the expression of logical conjunction, disjunction, and negation in terms of nor logic.
*}

theory GExp
imports AExp Option_Logic Utils
begin
datatype gexp = Bc bool | Eq aexp aexp | Gt aexp aexp | Nor gexp gexp | Null vname

instantiation gexp :: "show" begin
fun shows_prec_gexp :: "nat \<Rightarrow> gexp \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_prec_gexp n (Bc i) c = shows_prec n i c" |
  "shows_prec_gexp n (Eq v va) c = ''Eq(''@(shows_prec n v '''')@'' ''@(shows_prec n va '''')@'')''@c" |
  "shows_prec_gexp n (Gt v va) c = ''Gt(''@(shows_prec n v '''')@'' ''@(shows_prec n va '''')@'')''@c" |
  "shows_prec_gexp n (Nor v va) c = ''NOR(''@(shows_prec n v '''')@'' ''@(shows_prec n va '''')@'')''@c" |
  "shows_prec_gexp n (Null v) c = ''NULL(''@(shows_prec n v '''')@'')''@c"

primrec shows_list_gexp_aux :: "gexp list \<Rightarrow> string list" where
  "shows_list_gexp_aux [] = ''''" |
  "shows_list_gexp_aux (h#t) = (shows_prec 0 h '''')#(shows_list_gexp_aux t)"

definition shows_list_gexp :: "gexp list \<Rightarrow> char list \<Rightarrow> char list" where
"shows_list_gexp lst c = (join (shows_list_gexp_aux lst) '', '')@c"

instance proof
  fix x::gexp
  fix p r s
  show "shows_prec p x (r @ s) = shows_prec p x r @ s"
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
next
  fix xs::"gexp list"
  fix p r s
  show "shows_list xs (r @ s) = shows_list xs r @ s"
  proof (induction xs)
    case Nil
    then show ?case by (simp add: shows_list_gexp_def)
  next
    case (Cons a xs)
    then show ?case by (simp add: shows_list_gexp_def)
  qed
qed
end

lemma empty_guard_list: "(shows_list_gexp_aux g1 = []) = (g1 = [])"
proof
  show "shows_list_gexp_aux g1 = [] \<Longrightarrow> g1 = []"
  proof (induct g1)
    case Nil
    then show ?case by simp
  next
    case (Cons a g1)
    then show ?case by simp
  qed
  show "g1 = [] \<Longrightarrow> shows_list_gexp_aux g1 = []"
  proof (induct g1)
    case Nil
    then show ?case by simp
  next
    case (Cons a g1)
    then show ?case by simp
  qed
qed

lemma show_g_not_empty: "show (g::gexp) \<noteq> ''''"
proof (cases g)
case (Bc x1)
  then show ?thesis
    apply (cases x1)
     apply (simp add: shows_prec_bool_def shows_string_def)
    by (simp add: shows_prec_bool_def shows_string_def)
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

lemma show_guard_list_empty: "(join (shows_list_gexp_aux g1) '', '' = []) = (g1 = [])"
proof
  show "join (shows_list_gexp_aux g1) '', '' = [] \<Longrightarrow> g1 = []"
  proof (induction g1)
    case Nil
    then show ?case by simp
  next
    case (Cons a g1)
    then show ?case
      using join.elims show_g_not_empty by force
  qed
  show "g1 = [] \<Longrightarrow> join (shows_list_gexp_aux g1) '', '' = [] "
    by simp
qed

lemma show_true: "show True = ''True''"
  by (simp add: shows_prec_bool_def shows_string_def)

lemma show_false: "show False = ''False''"
  by (simp add: shows_prec_bool_def shows_string_def)

lemma show_num: "show (Num x1) = show x1"
proof (cases x1)
  case (nonneg n)
  then show ?thesis
      by (simp add: shows_prec_int_def showsp_int_def showsp_nat.simps shows_string_def shows_prec_value_def)
next
  case (neg n)
  then show ?thesis
      by (simp add: shows_prec_int_def showsp_int_def showsp_nat.simps shows_string_def shows_prec_value_def)
  qed

lemma show_bool_fst: "hd (show (v::bool)) = CHR ''T'' \<or> hd (show (v::bool)) = CHR ''F''"
  apply (simp add: shows_prec_bool_def showsp_bool_def shows_string_def)
  apply (cases v)
  by auto

lemma prefix_notation: "(show (x::aexp) @ CHR '' '' # show (y::aexp) = show (x1a::aexp) @ CHR '' '' # show (x2::aexp)) = (x = x1a \<and> y = x2)"
  sorry

lemma prefix_notation_gexp: "(show (g1::gexp) @ CHR '' '' # show (g2::gexp) = show (g1'::gexp) @ CHR '' '' # show (g2'::gexp)) = (g1 = g1' \<and> g2 = g2')"
  sorry

lemma "(show (a::gexp) = show (g::gexp)) = (a = g)"
proof (induction a)
  case (Bc v)
  then show ?case
  proof (induction g)
    case (Bc x)
    then show ?case
      apply simp
      apply (simp add: shows_prec_bool_def showsp_bool_def shows_string_def)
      using old.bool.simps(6) by fastforce
  next
    case (Eq x1a x2)
    then show ?case
    proof -
      have f1: "CHR ''F'' \<noteq> CHR ''E''"
        by simp
      have "CHR ''T'' \<noteq> CHR ''E''"
        by force
      then show ?thesis
        using f1 by (metis hd_append list.sel(1) list.simps(3) show_bool_fst shows_prec_gexp.simps(1) shows_prec_gexp.simps(2))
    qed
  next
    case (Gt x1a x2)
    then show ?case
    proof -
      have f1: "CHR ''F'' \<noteq> CHR ''G''"
        by force
      have "CHR ''T'' \<noteq> CHR ''G''"
        by force
      then show ?thesis
        using f1 by (metis hd_append list.sel(1) list.simps(3) show_bool_fst shows_prec_gexp.simps(1) shows_prec_gexp.simps(3))
    qed
  next
    case (Nor g1 g2)
    then show ?case
      apply simp
      apply (cases v)
       apply (simp add: show_true)
      by (simp add: show_false)
  next
    case (Null x)
    then show ?case
      apply simp
      apply (cases v)
       apply (simp add: show_true)
      by (simp add: show_false)
  qed
next
  case (Eq x y)
  then show ?case
  proof (induct g)
    case (Bc x)
    then show ?case
      apply simp
      apply (cases x)
       apply (simp add: show_true)
      by (simp add: show_false)
  next
    case (Eq x1a x2)
    then show ?case
      by (simp add: prefix_notation)
  next
    case (Gt x1a x2)
    then show ?case by simp
  next
    case (Nor g1 g2)
    then show ?case by simp
  next
    case (Null x)
    then show ?case by simp
  qed
next
  case (Gt x y)
  then show ?case
  proof (induction g)
    case (Bc x)
    then show ?case 
      apply simp
      apply (cases x)
       apply (simp add: show_true)
      by (simp add: show_false)
  next
    case (Eq x1a x2)
    then show ?case by simp
  next
    case (Gt x1a x2)
    then show ?case
      by (simp add: prefix_notation)
  next
    case (Nor g1 g2)
    then show ?case by simp
  next
    case (Null x)
    then show ?case by simp
  qed
next
  case (Nor g1 g2)
  then show ?case
  proof (induction g)
    case (Bc x)
    then show ?case
      apply simp
      apply (cases x)
       apply (simp add: show_true)
      by (simp add: show_false)
  next
    case (Eq x1a x2)
    then show ?case by simp
  next
    case (Gt x1a x2)
    then show ?case by simp
  next
    case (Nor g1' g2')
    then show ?case
      by (simp add: prefix_notation_gexp)
  next
    case (Null x)
    then show ?case by simp
  qed
next
  case (Null g1)
  then show ?case
  proof (induction g)
    case (Bc x)
    then show ?case
      apply (cases x)
       apply (simp add: show_true)
      by (simp add: show_false)
  next
    case (Eq x1a x2)
    then show ?case by simp
  next
    case (Gt x1a x2)
    then show ?case by simp
  next
    case (Nor g1 g2)
    then show ?case by simp
  next
    case (Null x)
    then show ?case
      apply simp
  qed
qed

lemma "shows_list ((a::gexp) # g1) l = shows_list [g] l \<Longrightarrow> a = g \<and> g1 = []"
proof (induction g1)
  case Nil
  then show ?case      
    apply (simp add: shows_list_gexp_def)
 
next
  case (Cons a g1)
  then show ?case sorry
qed



lemma "(shows_list (g1::gexp list) l = shows_list g2 l) = (g1 = g2)"
proof
  fix g1 :: "gexp list"
  fix l
  show "shows_list g1 l = shows_list g2 l \<Longrightarrow> g1 = g2"
  proof (induct g2)
    case Nil
    then show ?case
      apply (simp add: shows_list_gexp_def)
      apply (case_tac "shows_list_gexp_aux g1 = []")
       apply (simp add: empty_guard_list)
      by (simp add: empty_guard_list show_guard_list_empty)
    next
      case (Cons g gs)
      then show ?case
      proof (induction gs)
        case Nil
        then show ?case
        proof (induction g1)
          case Nil
          then show ?case
            by (simp add: show_g_not_empty shows_list_gexp_def)
        next
          case (Cons a g1)
          then show ?case
            apply simp
        qed

      next
        case (Cons a gs)
        then show ?case sorry
      qed

    qed

lemma "x \<ge> 100 = (x > 100 \<or> x = (100::nat))"
  by auto

syntax (xsymbols)
  Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (*infix "=" 60*)
  Gt :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (*infix ">" 60*)

fun gval :: "gexp \<Rightarrow> datastate \<Rightarrow> bool option" where
  "gval (Bc b) _ = Some b" |
  "gval (Gt a\<^sub>1 a\<^sub>2) s = ValueGt (aval a\<^sub>1 s) (aval a\<^sub>2 s)" |
  "gval (Eq a\<^sub>1 a\<^sub>2) s = Some (aval a\<^sub>1 s = aval a\<^sub>2 s)" |
  "gval (Nor a\<^sub>1 a\<^sub>2) s = (case (gval a\<^sub>1 s, gval a\<^sub>2 s) of
    (Some x, Some y) \<Rightarrow> Some (\<not> (x \<or> y)) |
    _ \<Rightarrow> None
  )" |
  "gval (Null v) s = Some (s v = None)"

instantiation gexp :: ord begin
definition  less_eq_gexp :: "gexp \<Rightarrow> gexp \<Rightarrow> bool" where
  "less_eq_gexp g1 g2 \<equiv> \<forall>s. maybe_implies (gval g1 s) (gval g2 s) = Some True"

definition  less_gexp :: "gexp \<Rightarrow> gexp \<Rightarrow> bool" where
  "less_gexp g1 g2 \<equiv> \<forall>s. maybe_implies (gval g1 s) (gval g2 s) = Some True \<and> (gval g1 s) \<noteq> (gval g2 s)"

instance proof
qed
end

abbreviation gNot :: "gexp \<Rightarrow> gexp"  where
  "gNot g \<equiv> Nor g g"

abbreviation gOr :: "gexp \<Rightarrow> gexp \<Rightarrow> gexp" (*infix "\<or>" 60*) where
  "gOr v va \<equiv> Nor (Nor v va) (Nor v va)"

abbreviation gAnd :: "gexp \<Rightarrow> gexp \<Rightarrow> gexp" (*infix "\<and>" 60*) where
  "gAnd v va \<equiv> Nor (Nor v v) (Nor va va)"

abbreviation Lt :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (*infix "<" 60*) where
  "Lt a b \<equiv> Gt b a"

abbreviation Le :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (*infix "\<le>" 60*) where
  "Le v va \<equiv> gNot (Gt v va)"

abbreviation Ge :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (*infix "\<ge>" 60*) where
  "Ge v va \<equiv> gNot (Lt v va)"

abbreviation Ne :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (*infix "\<noteq>" 60*) where
  "Ne v va \<equiv> gNot (Eq v va)"

lemma or_equiv: "gval (gOr x y) r = maybe_or (gval x r) (gval y r)"
  apply simp
  apply (cases "gval x r")
   apply (cases "gval y r")
    apply simp
   apply simp
  apply (cases "gval y r")
   apply simp
  by simp

lemma not_equiv: "maybe_not (gval x s) = gval (gNot x) s"
  apply simp
  apply (cases "gval x s")
   apply simp
  by simp

lemma nor_equiv: "gval (gNot (gOr a b)) s = gval (Nor a b) s"
  by (simp add: option.case_eq_if)

definition satisfiable :: "gexp \<Rightarrow> bool" where
  "satisfiable g \<equiv> (\<exists>s. gval g s = Some True)"

lemma not_satisfiable_gt_string: "\<not> satisfiable (Gt v (L (Str s)))"
  by (simp add: satisfiable_def)

definition gexp_valid :: "gexp \<Rightarrow> bool" where
  "gexp_valid g \<equiv> (\<forall>s. gval g s = Some True)"

definition gexp_equiv :: "gexp \<Rightarrow> gexp \<Rightarrow> bool" where
  "gexp_equiv a b \<equiv> \<forall>s. gval a s = gval b s"

lemma gexp_equiv_reflexive: "gexp_equiv x x"
  by (simp add: gexp_equiv_def)

lemma gexp_equiv_symmetric: "gexp_equiv x y \<Longrightarrow> gexp_equiv y x"
  by (simp add: gexp_equiv_def)

lemma gexp_equiv_transitive: "gexp_equiv x y \<and> gexp_equiv y z \<Longrightarrow> gexp_equiv x z"
  by (simp add: gexp_equiv_def)

lemma gval_subst: "gexp_equiv x y \<Longrightarrow> P (gval x s) \<Longrightarrow> P (gval y s)"
  by (simp add: gexp_equiv_def)

lemma gexp_equiv_satisfiable: "gexp_equiv x y \<Longrightarrow> satisfiable x = satisfiable y"
  by (simp add: gexp_equiv_def satisfiable_def)

lemma gAnd_reflexivity: "gexp_equiv (gAnd x x) x"
  apply (simp add: gexp_equiv_def)
  apply (rule allI)
  apply (case_tac "gval x s")
   apply simp
  by simp

lemma gAnd_zero: "gexp_equiv (gAnd (Bc True) x) x"
  apply (simp add: gexp_equiv_def)
  apply (rule allI)
  apply (case_tac "gval x s")
  by simp_all

lemma gAnd_symmetry: "gexp_equiv (gAnd x y) (gAnd y x)"
  apply (simp add: gexp_equiv_def)
  apply (rule allI)
  apply (case_tac "gval y s")
   apply (case_tac "gval x s")
    apply simp
   apply simp
  apply (case_tac "gval x s")
   apply simp
  by auto

lemma satisfiable_gAnd_self: "satisfiable (gAnd x x) = satisfiable x"
  by (simp add: gAnd_reflexivity gexp_equiv_satisfiable)

definition mutually_exclusive :: "gexp \<Rightarrow> gexp \<Rightarrow> bool" where
  "mutually_exclusive x y = (\<forall>i. (gval x i = Some True \<longrightarrow> gval y i \<noteq> Some True) \<and>
                                 (gval y i = Some True \<longrightarrow> gval x i \<noteq> Some True))"

lemma mutually_exclusive_unsatisfiable_conj: "mutually_exclusive x y = (\<not> satisfiable (gAnd x y))"
  apply (simp add: mutually_exclusive_def satisfiable_def)
  apply safe
    apply (case_tac "gval x s")
     apply simp
    apply (case_tac "gval y s")
     apply simp
    apply simp
   apply (metis (mono_tags, lifting) option.simps(5))
  by (metis (mono_tags, lifting) option.simps(5))

lemma unsatisfiable_conj_mutually_exclusive: "\<not> satisfiable (gAnd x y) = mutually_exclusive x y"
  by (simp add: mutually_exclusive_unsatisfiable_conj)

lemma mutually_exclusive_reflexive: "satisfiable x \<Longrightarrow> \<not> mutually_exclusive x x"
  by (simp add: mutually_exclusive_def satisfiable_def)

lemma mutually_exclusive_symmetric: "mutually_exclusive x y \<Longrightarrow> mutually_exclusive y x"
  by (simp add: mutually_exclusive_def)

lemma not_mutually_exclusive_true: "satisfiable x = (\<not> mutually_exclusive x (Bc True))"
  by (simp add: mutually_exclusive_def satisfiable_def)

end
