theory AExp
  imports Main
begin

datatype "value" = Num int | Str string
datatype vname = I nat | R nat
type_synonym datastate = "vname \<Rightarrow> value option"

datatype aexp = L "value" | V vname | Plus aexp aexp | Minus aexp aexp

fun value_plus :: "value option \<Rightarrow> value option \<Rightarrow> value option" (infix "+" 40) where
  "value_plus (Some (Num x)) (Some (Num y)) = Some (Num (x+y))" |
  "value_plus _ _ = None"

lemma plus_no_string [simp]:"value_plus a b \<noteq> Some (Str x)"
  using value_plus.elims by blast

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

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (L (Num i\<^sub>1)) (L (Num i\<^sub>2)) = L (Num (i\<^sub>1+i\<^sub>2))" |
"plus a\<^sub>1 a\<^sub>2 = Plus a\<^sub>1 a\<^sub>2"

lemma aval_plus[simp]: "aval (plus a1 a2) s = value_plus (aval a1 s)  (aval a2 s)"
  apply (induction a1 a2 rule: plus.induct)
  by simp_all

fun minus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"minus (L (Num i\<^sub>1)) (L (Num i\<^sub>2)) = L (Num (i\<^sub>1-i\<^sub>2))" |
"minus a\<^sub>1 a\<^sub>2 = Minus a\<^sub>1 a\<^sub>2"

lemma aval_minus[simp]: "aval (minus a1 a2) s = value_minus (aval a1 s) (aval a2 s)"
  apply(induction a1 a2 rule: minus.induct)
  by simp_all

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (L n) = L n" |
"asimp (V x) = V x" |
"asimp (Plus a\<^sub>1 a\<^sub>2) = plus (asimp a\<^sub>1) (asimp a\<^sub>2)" |
"asimp (Minus a\<^sub>1 a\<^sub>2) = minus (asimp a\<^sub>1) (asimp a\<^sub>2)"

lemma aval_asimp[simp]: "aval (asimp a) s = aval a s"
  apply(induction a)
  by simp_all

definition aexp_equiv :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" where
  "aexp_equiv a b = (\<forall>s. (aval a s) = (aval b s))"

lemma aexp_equiv_reflexivity: "aexp_equiv a a"
  by (simp add: aexp_equiv_def)

lemma aexp_equiv_symmetry: "aexp_equiv a b \<Longrightarrow> aexp_equiv b a"
  by (simp add: aexp_equiv_def)

lemma aexp_equiv_transitivity: "aexp_equiv a b \<Longrightarrow> aexp_equiv b c \<Longrightarrow> aexp_equiv a c"
  by (simp add: aexp_equiv_def)

lemma literal_neq_variable: "\<not> aexp_equiv (L x) (V xa)"
  apply (simp add: aexp_equiv_def)
  apply (rule_tac x="<>" in exI)
  by simp

lemma aexp_equiv_literals: "aexp_equiv (L x) (L y) \<Longrightarrow> x = y"
  by (simp add: aexp_equiv_def)

lemma aexp_equiv_plus_num: "aexp_equiv (L x) (Plus t1 t2) \<Longrightarrow> x \<noteq> Str s"
  apply (simp add: aexp_equiv_def)
  by (metis plus_no_string)
end
