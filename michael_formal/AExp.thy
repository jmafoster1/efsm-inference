section {* Arithmetic Expressions *}
(* Author: Michael Foster *)
theory AExp
  imports Main
begin

datatype "value" = Num int | Str string
datatype vname = I nat | R nat
type_synonym datastate = "vname \<Rightarrow> value option"

datatype aexp = L "value" | V vname | Plus aexp aexp | Minus aexp aexp

syntax (xsymbols)
  Plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" (infix "+" 60)
  Minus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" (infix "-" 60)

fun value_plus :: "value option \<Rightarrow> value option \<Rightarrow> value option" (infix "+" 40) where
  "value_plus (Some (Num x)) (Some (Num y)) = Some (Num (x+y))" |
  "value_plus _ _ = None"

lemma plus_no_string [simp]:"value_plus a b \<noteq> Some (Str x)"
  using value_plus.elims by blast

lemma value_plus_symmetry: "value_plus x y = value_plus y x"
  proof (cases x)
    case None
    then show ?thesis by simp
  next
    case (Some a)
    then show ?thesis
      apply (cases y)
       apply simp
      apply (case_tac a)
       apply (case_tac aa)
        apply simp
       apply simp
      apply (case_tac aa)
      by simp_all
  qed

fun value_minus :: "value option \<Rightarrow> value option \<Rightarrow> value option" (infix "-" 40) where
  "value_minus (Some (Num x)) (Some (Num y)) = Some (Num (x-y))" |
  "value_minus _ _ = None"

lemma minus_no_string [simp]:"value_minus a b \<noteq> Some (Str x)"
  using value_minus.elims by blast

fun aval :: "aexp \<Rightarrow> datastate \<Rightarrow> value option" where
  "aval (L x) s = Some x" |
  "aval (V x) s = s x" | (* Leave out when the case is None so we get a nice error *)
  "aval (Plus a\<^sub>1 a\<^sub>2) s = (aval a\<^sub>1 s + aval a\<^sub>2 s)" |
  "aval (Minus a\<^sub>1 a\<^sub>2) s = (aval a\<^sub>1 s - aval a\<^sub>2 s)"

lemma aval_plus_symmetry: "aval (Plus x y) s = aval (Plus y x) s"
  by (simp add: value_plus_symmetry)

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. None"
declare null_state_def [simp]

syntax
  "_maplet"  :: "['a, 'a] \<Rightarrow> maplet"             ("_ /:=/ _")
  "_maplets" :: "['a, 'a] \<Rightarrow> maplet"             ("_ /[:=]/ _")
  "_Map"     :: "maplets \<Rightarrow> 'a \<rightharpoonup> 'b"            ("(1<_>)")

fun asimp_const :: "aexp \<Rightarrow> aexp" where
  "asimp_const (L x) = L x" |
  "asimp_const (V x) = V x" |
  "asimp_const (Plus a\<^sub>1 a\<^sub>2) =
    (case (asimp_const a\<^sub>1, asimp_const a\<^sub>2) of
      (L (Num n\<^sub>1), L (Num n\<^sub>2)) \<Rightarrow> L (Num (n\<^sub>1+n\<^sub>2)) |
      (b\<^sub>1,b\<^sub>2) \<Rightarrow> Plus b\<^sub>1 b\<^sub>2)" |
  "asimp_const (Minus a\<^sub>1 a\<^sub>2) =
    (case (asimp_const a\<^sub>1, asimp_const a\<^sub>2) of
      (L (Num n\<^sub>1), L (Num n\<^sub>2)) \<Rightarrow> L (Num (n\<^sub>1-n\<^sub>2)) |
      (b\<^sub>1,b\<^sub>2) \<Rightarrow> Minus b\<^sub>1 b\<^sub>2)"

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (L n) = L n" |
"asimp (V x) = V x" |
"asimp (Plus a\<^sub>1 a\<^sub>2) = Plus (asimp a\<^sub>1) (asimp a\<^sub>2)" |
"asimp (Minus a\<^sub>1 a\<^sub>2) = Minus (asimp a\<^sub>1) (asimp a\<^sub>2)"

theorem aval_asimp[simp]: "aval (asimp a) s = aval a s"
  apply(induction a)
  by simp_all

end