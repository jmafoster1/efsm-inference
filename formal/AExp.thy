section\<open>Extended Finite State Machines\<close>
text\<open>
This section presents the theories associated with EFSMs. First we define a language of arithmetic
expressions for guards, outputs, and updates similar to that in IMP \cite{fixme}. We then go on to
define the guard logic such that nonsensical guards (such as testing to see if an integer is greater
than a string) can never evaluate to true. Next, the guard language is defined in terms of
arithmetic expressions and binary relations. In the interest of simplifying the conversion of guards
to constraints, we use a Nor logic, although we define syntax hacks for the expression of guards
using other logical operators. With the underlying types defined, we then define EFSMs and prove
that they are prefix-closed, that is to say that if a string of inputs is accepted by the machine
then all of its prefixes are also accepted.
\<close>
subsection \<open>Arithmetic Expressions\<close>
text\<open>
This theory defines a language of arithmetic expressions over literal values and variables. Here,
values are limited to integers and strings. Variables may be either inputs or registers. We also
limit ourselves to a simple arithmetic of plus and minus as a proof of concept.
\<close>

theory AExp
  imports Value VName
begin

type_synonym datastate = "vname \<Rightarrow> value option"

datatype aexp = L "value" | V vname | Plus aexp aexp | Minus aexp aexp

syntax (xsymbols)
  Plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" (*infix "+" 60*)
  Minus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" (*infix "-" 60*)

fun value_plus :: "value option \<Rightarrow> value option \<Rightarrow> value option" (*infix "+" 40*) where
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

fun value_minus :: "value option \<Rightarrow> value option \<Rightarrow> value option" (*infix "-" 40*) where
  "value_minus (Some (Num x)) (Some (Num y)) = Some (Num (x-y))" |
  "value_minus _ _ = None"

lemma minus_no_string [simp]:"value_minus a b \<noteq> Some (Str x)"
  using value_minus.elims by blast

fun aval :: "aexp \<Rightarrow> datastate \<Rightarrow> value option" where
  "aval (L x) s = Some x" |
  "aval (V x) s = s x" |
  "aval (Plus a\<^sub>1 a\<^sub>2) s = value_plus (aval a\<^sub>1 s)(aval a\<^sub>2 s)" |
  "aval (Minus a\<^sub>1 a\<^sub>2) s = value_minus (aval a\<^sub>1 s) (aval a\<^sub>2 s)"

lemma aval_plus_symmetry: "aval (Plus x y) s = aval (Plus y x) s"
  by (simp add: value_plus_symmetry)

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. None"
declare null_state_def [simp]

syntax
  "_maplet"  :: "['a, 'a] \<Rightarrow> maplet"             ("_ /:=/ _")
  "_maplets" :: "['a, 'a] \<Rightarrow> maplet"             ("_ /[:=]/ _")
  "_Map"     :: "maplets \<Rightarrow> 'a \<rightharpoonup> 'b"            ("(1<_>)")

instantiation aexp :: plus begin
fun plus_aexp :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus_aexp (L (Num n1)) (L (Num n2)) = L (Num (n1+n2))" |
  "plus_aexp x y = Plus x y"

instance by standard
end

instantiation aexp :: minus begin
fun minus_aexp :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "minus_aexp (L (Num n1)) (L (Num n2)) = L (Num (n1-n2))" |
  "minus_aexp x y = Minus x y"

instance by standard
end

lemma aval_plus_aexp: "aval (a+b) s = aval (Plus a b) s"
  apply (case_tac a)
     apply (case_tac x1)
      apply (case_tac b)
         apply (case_tac x1b)
  by auto

lemma aval_minus_aexp: "aval (a-b) s = aval (Minus a b) s"
  apply (case_tac a)
     apply (case_tac x1)
      apply (case_tac b)
         apply (case_tac x1b)
  by auto

fun aexp_constrains :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" where
  "aexp_constrains (L l) a = (L l = a)" |
  "aexp_constrains (V v) v' = (V v = v')" |
  "aexp_constrains (Plus a1 a2) v = ((Plus a1 a2) = v \<or> (Plus a1 a2) = v \<or> (aexp_constrains a1 v \<or> aexp_constrains a2 v))" |
  "aexp_constrains (Minus a1 a2) v = ((Minus a1 a2) = v \<or> (aexp_constrains a1 v \<or> aexp_constrains a2 v))"

lemma constrains_implies_not_equal: "\<not> aexp_constrains x a \<Longrightarrow> x \<noteq> a"
  using aexp_constrains.elims(3) by blast

fun aexp_same_structure :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" where
  "aexp_same_structure (L v) (L v') = True" |
  "aexp_same_structure (V v) (V v') = True" |
  "aexp_same_structure (Plus a1 a2) (Plus a1' a2') = (aexp_same_structure a1 a1' \<and> aexp_same_structure a2 a2')" |
  "aexp_same_structure (Minus a1 a2) (Minus a1' a2') = (aexp_same_structure a1 a1' \<and> aexp_same_structure a2 a2')" |
  "aexp_same_structure _ _ = False"

end
