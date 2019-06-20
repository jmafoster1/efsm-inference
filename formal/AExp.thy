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

declare One_nat_def [simp del]

type_synonym registers = "nat \<Rightarrow> value option"
type_synonym datastate = "vname \<Rightarrow> value option"

text_raw{*\snip{aexptype}{1}{2}{%*}
datatype aexp = L "value" | V vname | Plus aexp aexp | Minus aexp aexp
text_raw{*}%endsnip*}

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

definition input2state :: "value list \<Rightarrow> registers" where
  "input2state n = map_of (enumerate 0 n)"

lemma input2state_out_of_bounds: "i \<ge> length ia \<Longrightarrow> input2state ia i = None"
proof(induct "ia")
  case Nil
  then show ?case
    by (simp add: input2state_def)
next
  case (Cons a ia)
  then show ?case
    apply (simp add: input2state_def)
    by (metis (mono_tags, lifting) imageE in_set_enumerate_eq length_Cons linorder_not_le list.size(4) map_of_eq_None_iff)
qed

lemma input2state_nth: "i < length ia \<Longrightarrow> input2state ia i = Some (ia ! i)"
proof(induct ia)
  case Nil
  then show ?case
    by simp
next
  case (Cons a ia)
  then show ?case
    apply (simp add: input2state_def)
    apply clarify
    by (simp add: add.commute in_set_enumerate_eq plus_1_eq_Suc One_nat_def)
qed

lemma input2state_cons:
  "x1 > 0 \<Longrightarrow>
   x1 < length ia \<Longrightarrow>
   input2state (a # ia) x1 = input2state ia (x1-1)"
  by (simp add: input2state_nth)

definition join_ir :: "value list \<Rightarrow> registers \<Rightarrow> datastate" where
  "join_ir i r \<equiv> (\<lambda>x. case x of
    R n \<Rightarrow> r n |
    I n \<Rightarrow> (input2state i) n
  )"

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

fun enumerate_aexp_inputs :: "aexp \<Rightarrow> nat set" where
  "enumerate_aexp_inputs (L _) = {}" |
  "enumerate_aexp_inputs (V (I n)) = {n}" |
  "enumerate_aexp_inputs (V (R n)) = {}" |
  "enumerate_aexp_inputs (Plus v va) = enumerate_aexp_inputs v \<union> enumerate_aexp_inputs va" |
  "enumerate_aexp_inputs (Minus v va) = enumerate_aexp_inputs v \<union> enumerate_aexp_inputs va"

fun enumerate_aexp_inputs_list :: "aexp \<Rightarrow> nat list" where
  "enumerate_aexp_inputs_list (L _) = []" |
  "enumerate_aexp_inputs_list (V (I n)) = [n]" |
  "enumerate_aexp_inputs_list (V (R n)) = []" |
  "enumerate_aexp_inputs_list (Plus v va) = enumerate_aexp_inputs_list v @ enumerate_aexp_inputs_list va" |
  "enumerate_aexp_inputs_list (Minus v va) = enumerate_aexp_inputs_list v @ enumerate_aexp_inputs_list va"

fun enumerate_aexp_regs :: "aexp \<Rightarrow> nat set" where
  "enumerate_aexp_regs (L _) = {}" |
  "enumerate_aexp_regs (V (R n)) = {n}" |
  "enumerate_aexp_regs (V (I _)) = {}" |
  "enumerate_aexp_regs (Plus v va) = enumerate_aexp_regs v \<union> enumerate_aexp_regs va" |
  "enumerate_aexp_regs (Minus v va) = enumerate_aexp_regs v \<union> enumerate_aexp_regs va"

fun enumerate_aexp_regs_list :: "aexp \<Rightarrow> nat list" where
  "enumerate_aexp_regs_list (L _) = []" |
  "enumerate_aexp_regs_list (V (R n)) = [n]" |
  "enumerate_aexp_regs_list (V (I _)) = []" |
  "enumerate_aexp_regs_list (Plus v va) = enumerate_aexp_regs_list v @ enumerate_aexp_regs_list va" |
  "enumerate_aexp_regs_list (Minus v va) = enumerate_aexp_regs_list v @ enumerate_aexp_regs_list va"

lemma enumerate_aexp_inputs_list: "set (enumerate_aexp_inputs_list l) = enumerate_aexp_inputs l"
proof(induct l)
case (L x)
  then show ?case
  by simp
next
  case (V x)
  then show ?case
    apply (cases x)
    by auto
next
  case (Plus l1 l2)
  then show ?case
    by simp
next
  case (Minus l1 l2)
  then show ?case
    by simp
qed

lemma enumerate_aexp_regs_list: "set (enumerate_aexp_regs_list l) = enumerate_aexp_regs l"
proof(induct l)
case (L x)
then show ?case
  by simp
next
  case (V x)
  then show ?case
    apply (cases x)
    by auto
next
  case (Plus l1 l2)
  then show ?case
    by simp
next
  case (Minus l1 l2)
  then show ?case 
    by simp
qed


lemma enumerate_aexp_regs_empty_reg_unconstrained:
  "enumerate_aexp_regs a = {} \<Longrightarrow> \<forall>r. \<not> aexp_constrains a (V (R r))"
proof(induct a)
case (L x)
  then show ?case
    by simp
next
  case (V x)
  then show ?case
    apply (cases x)
     apply simp
    by simp
next
  case (Plus a1 a2)
  then show ?case
    by simp
next
  case (Minus a1 a2)
  then show ?case
    by simp
qed

lemma set_enumerate_aexp_inputs_list: "set (fold (@) (map enumerate_aexp_inputs_list l) []) = (\<Union> set (map enumerate_aexp_inputs l))"
proof(induct l)
case Nil
  then show ?case
    by simp
next
case (Cons a l)
  then show ?case
    using enumerate_aexp_inputs_list
    by (simp add: fold_append_concat_rev inf_sup_aci(5))
qed

lemma enumerate_aexp_inputs_empty_input_unconstrained:
  "enumerate_aexp_inputs a = {} \<Longrightarrow> \<forall>r. \<not> aexp_constrains a (V (I r))"
proof(induct a)
case (L x)
  then show ?case
    by simp
next
  case (V x)
  then show ?case
    apply (cases x)
     apply simp
    by simp
next
  case (Plus a1 a2)
  then show ?case
    by simp
next
  case (Minus a1 a2)
  then show ?case
    by simp
qed

lemma input_unconstrained_aval_input_swap:
  "\<forall>i. \<not> aexp_constrains a (V (I i)) \<Longrightarrow> aval a (join_ir i r) = aval a (join_ir i' r)"
proof(induct a)
case (L x)
  then show ?case
    by simp
next
  case (V x)
  then show ?case
    apply (cases x)
     apply simp
    by (simp add: join_ir_def)
next
  case (Plus a1 a2)
  then show ?case
    by simp
next
  case (Minus a1 a2)
  then show ?case
    by simp
qed

lemma input_unconstrained_aval_register_swap:
  "\<forall>i. \<not> aexp_constrains a (V (R i)) \<Longrightarrow> aval a (join_ir i r) = aval a (join_ir i r')"
proof(induct a)
case (L x)
  then show ?case
    by simp
next
  case (V x)
  then show ?case
    apply (cases x)
     apply (simp add: join_ir_def)
    by simp
next
  case (Plus a1 a2)
  then show ?case
    by simp
next
  case (Minus a1 a2)
  then show ?case
    by simp
qed

lemma unconstrained_variable_swap_aval: 
  "\<forall>i. \<not> aexp_constrains a (V (I i)) \<Longrightarrow>
   \<forall>r. \<not> aexp_constrains a (V (R r)) \<Longrightarrow>
   aval a s = aval a s'"
proof(induct a)
case (L x)
  then show ?case
    by simp
next
  case (V x)
  then show ?case
    apply (cases x)
    by auto
next
  case (Plus a1 a2)
  then show ?case
    by simp
next
  case (Minus a1 a2)
  then show ?case
    by simp
qed

end
