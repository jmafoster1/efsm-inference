theory AExp
  imports Main
begin

datatype "value" = Num int | Str string | Nope
datatype vname = I nat | R nat
type_synonym datastate = "vname \<Rightarrow> value option"

datatype aexp = N int | V vname | Plus aexp aexp | Minus aexp aexp | S string

fun value_plus :: "value \<Rightarrow> value \<Rightarrow> value" (infix "+" 40) where
  "value_plus (Num x) (Num y) = Num (x+y)" |
  "value_plus _ _ = Nope"

lemma plus_no_string [simp]:"value_plus a b \<noteq> Str x"
  using value_plus.elims by blast

fun value_minus :: "value \<Rightarrow> value \<Rightarrow> value" (infix "-" 40) where
  "value_minus (Num x) (Num y) = Num (x-y)" |
  "value_minus _ _ = Nope"

lemma minus_no_string [simp]:"value_minus a b \<noteq> Str x"
  using value_minus.elims by blast

fun aval :: "aexp \<Rightarrow> datastate \<Rightarrow> value" where
  "aval (N n) s = Num n" |
  "aval (S n) s = Str n" |
  "aval (V x) s = (case s x of Some x \<Rightarrow> x)" | (* Leave out when the case is None so we get a nice error *)
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
"asimp_const (N n) = N n" |
"asimp_const (S n) = S n" |
"asimp_const (V x) = V x" |
"asimp_const (Plus a\<^sub>1 a\<^sub>2) =
  (case (asimp_const a\<^sub>1, asimp_const a\<^sub>2) of
    (N n\<^sub>1, N n\<^sub>2) \<Rightarrow> N(n\<^sub>1+n\<^sub>2) |
    (b\<^sub>1,b\<^sub>2) \<Rightarrow> Plus b\<^sub>1 b\<^sub>2)" |
"asimp_const (Minus a\<^sub>1 a\<^sub>2) =
  (case (asimp_const a\<^sub>1, asimp_const a\<^sub>2) of
    (N n\<^sub>1, N n\<^sub>2) \<Rightarrow> N(n\<^sub>1-n\<^sub>2) |
    (b\<^sub>1,b\<^sub>2) \<Rightarrow> Minus b\<^sub>1 b\<^sub>2)"

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i\<^sub>1) (N i\<^sub>2) = N (i\<^sub>1+i\<^sub>2)" |
"plus a\<^sub>1 a\<^sub>2 = Plus a\<^sub>1 a\<^sub>2"

lemma aval_plus[simp]: "aval (plus a1 a2) s = value_plus (aval a1 s)  (aval a2 s)"
  apply (induction a1 a2 rule: plus.induct)
  by simp_all

fun minus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"minus (N i\<^sub>1) (N i\<^sub>2) = N(i\<^sub>1-i\<^sub>2)" |
"minus a\<^sub>1 a\<^sub>2 = Minus a\<^sub>1 a\<^sub>2"

lemma aval_minus[simp]: "aval (minus a1 a2) s = value_minus (aval a1 s) (aval a2 s)"
  apply(induction a1 a2 rule: minus.induct)
  by simp_all

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (S n) = S n" |
"asimp (V x) = V x" |
"asimp (Plus a\<^sub>1 a\<^sub>2) = plus (asimp a\<^sub>1) (asimp a\<^sub>2)" |
"asimp (Minus a\<^sub>1 a\<^sub>2) = minus (asimp a\<^sub>1) (asimp a\<^sub>2)"

theorem aval_asimp[simp]: "aval (asimp a) s = aval a s"
  apply(induction a)
  by simp_all
end
