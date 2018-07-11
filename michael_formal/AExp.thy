theory AExp
  imports Main
begin

datatype vname = I nat | R nat
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val option"

datatype aexp = N int | V vname | Plus aexp aexp | Minus aexp aexp

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = (case s x of Some y \<Rightarrow> y)" | (* Leave out when the case is None so we get a nice error *)
"aval (Plus a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s + aval a\<^sub>2 s" |
"aval (Minus a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s - aval a\<^sub>2 s"

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. None"
declare null_state_def [simp]

syntax
  "_maplet"  :: "['a, 'a] \<Rightarrow> maplet"             ("_ /:=/ _")
  "_maplets" :: "['a, 'a] \<Rightarrow> maplet"             ("_ /[:=]/ _")
  "_Map"     :: "maplets \<Rightarrow> 'a \<rightharpoonup> 'b"            ("(1<_>)")

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V x) = V x" |
"asimp_const (Plus a\<^sub>1 a\<^sub>2) =
  (case (asimp_const a\<^sub>1, asimp_const a\<^sub>2) of
    (N n\<^sub>1, N n\<^sub>2) \<Rightarrow> N(n\<^sub>1+n\<^sub>2) |
    (b\<^sub>1,b\<^sub>2) \<Rightarrow> Plus b\<^sub>1 b\<^sub>2)" |
"asimp_const (Minus a\<^sub>1 a\<^sub>2) =
  (case (asimp_const a\<^sub>1, asimp_const a\<^sub>2) of
    (N n\<^sub>1, N n\<^sub>2) \<Rightarrow> N(n\<^sub>1-n\<^sub>2) |
    (b\<^sub>1,b\<^sub>2) \<Rightarrow> Minus b\<^sub>1 b\<^sub>2)"

theorem aval_asimp_const:
  "aval (asimp_const a) s = aval a s"
apply(induction a)
apply (auto split: aexp.split)
done

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i\<^sub>1) (N i\<^sub>2) = N(i\<^sub>1+i\<^sub>2)" |
"plus (N i) a = (if i=0 then a else Plus (N i) a)" |
"plus a (N i) = (if i=0 then a else Plus a (N i))" |
"plus a\<^sub>1 a\<^sub>2 = Plus a\<^sub>1 a\<^sub>2"

lemma aval_plus[simp]:
  "aval (plus a1 a2) s = aval a1 s + aval a2 s"
apply(induction a1 a2 rule: plus.induct)
apply simp_all (* just for a change from auto *)
  done

fun minus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"minus (N i\<^sub>1) (N i\<^sub>2) = N(i\<^sub>1-i\<^sub>2)" |
"minus a (N i) = (if i=0 then a else Minus a (N i))" |
"minus a\<^sub>1 a\<^sub>2 = Minus a\<^sub>1 a\<^sub>2"

lemma aval_minus[simp]:
  "aval (minus a1 a2) s = aval a1 s - aval a2 s"
apply(induction a1 a2 rule: minus.induct)
apply simp_all (* just for a change from auto *)
done

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus a\<^sub>1 a\<^sub>2) = plus (asimp a\<^sub>1) (asimp a\<^sub>2)" |
"asimp (Minus a\<^sub>1 a\<^sub>2) = minus (asimp a\<^sub>1) (asimp a\<^sub>2)"

theorem aval_asimp[simp]:
  "aval (asimp a) s = aval a s"
apply(induction a)
apply simp_all
done

end