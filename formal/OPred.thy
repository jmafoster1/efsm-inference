theory OPred
imports AExp Trilean Option_Lexorder
begin

datatype opred = Bc bool | Eq aexp | Gt aexp | Null | In "value list" | Nor opred opred

fun oval :: "opred \<Rightarrow> value option \<Rightarrow> datastate \<Rightarrow> trilean" where
  "oval (Bc True) v _ = true" |
  "oval (Bc False) v _ = false" |
  "oval (Gt a) v s = value_gt v (aval a s)" |
  "oval (Eq a) v s = value_eq v (aval a s)" |
  "oval (Null) v _ = value_eq v None" |
  "oval (In l) v _ = (if v \<in> set (map Some l) then true else false)" |
  "oval (Nor a\<^sub>1 a\<^sub>2) v s = \<not>\<^sub>? ((oval a\<^sub>1 v s) \<or>\<^sub>? (oval a\<^sub>2 v s))"

fun enumerate_inputs :: "opred \<Rightarrow> nat set" where
  "enumerate_inputs (Eq a) = enumerate_aexp_inputs a" |
  "enumerate_inputs (Gt a) = enumerate_aexp_inputs a" |
  "enumerate_inputs (Nor o\<^sub>1 o\<^sub>2) = enumerate_inputs o\<^sub>1 \<union> enumerate_inputs o\<^sub>2" |
  "enumerate_inputs _ = {}"

fun enumerate_regs :: "opred \<Rightarrow> nat set" where
  "enumerate_regs (Eq a) = enumerate_aexp_regs a" |
  "enumerate_regs (Gt a) = enumerate_aexp_regs a" |
  "enumerate_regs (Nor o\<^sub>1 o\<^sub>2) = enumerate_regs o\<^sub>1 \<union> enumerate_regs o\<^sub>2" |
  "enumerate_regs _ = {}"

lemma finite_enumerate_regs: "finite (enumerate_regs op)"
proof(induct op)
case (Bc x)
  then show ?case by simp
next
  case (Eq x)
  then show ?case
    by (metis Cardinality.finite'_def enumerate_aexp_regs_list enumerate_regs.simps(1) finite'_code(1))
next
  case (Gt x)
  then show ?case
    by (metis Cardinality.finite'_def enumerate_aexp_regs_list enumerate_regs.simps(2) finite'_code(1))
next
  case Null
  then show ?case by simp
next
  case (In x)
  then show ?case by simp
next
  case (Nor op1 op2)
  then show ?case by simp
qed

fun enumerate_strings :: "opred \<Rightarrow> String.literal set" where
  "enumerate_strings (Bc _) = {}" |
  "enumerate_strings (Eq a) = enumerate_aexp_strings a" |
  "enumerate_strings (Gt a) = enumerate_aexp_strings a" |
  "enumerate_strings Null = {}" |
  "enumerate_strings (Nor o\<^sub>1 o\<^sub>2) = enumerate_strings o\<^sub>1 \<union> enumerate_strings o\<^sub>2" |
  "enumerate_strings (In l) = set ((map (\<lambda>x. case x of Str s \<Rightarrow> s)) (filter is_Str l))"

fun enumerate_ints :: "opred \<Rightarrow> int set" where
  "enumerate_ints (Bc _) = {}" |
  "enumerate_ints (Eq a) = enumerate_aexp_ints a" |
  "enumerate_ints (Gt a) = enumerate_aexp_ints a" |
  "enumerate_ints Null = {}" |
  "enumerate_ints (Nor o\<^sub>1 o\<^sub>2) = enumerate_ints o\<^sub>1 \<union> enumerate_ints o\<^sub>2" |
  "enumerate_ints (In l) = set ((map (\<lambda>x. case x of Num n \<Rightarrow> n)) (filter is_Num l))"

fun check_outs :: "opred list \<Rightarrow> datastate \<Rightarrow> (value option) list \<Rightarrow> bool" where
  "check_outs [] _ [] = True" |
  "check_outs (h#t) _ [] = False" |
  "check_outs [] _ (h#t) = False" |
  "check_outs (op#ops) d (v#vs) = ((oval op v d = true) \<and> (check_outs ops d vs))"

definition check_outs_alt :: "opred list \<Rightarrow> datastate \<Rightarrow> (value option) list \<Rightarrow> bool" where
  "check_outs_alt ops d vs = (if length ops \<noteq> length vs then False else \<forall>t \<in> set (map (\<lambda>(op, v). oval op v d) (zip ops vs)). t = true)"

lemma check_outs_alt: "check_outs ops d vs = check_outs_alt ops d vs"
  apply (induction rule: check_outs.induct)
  using check_outs_alt_def by auto

lemma check_outs_equiv: "length ops = length ops' \<Longrightarrow>
map (\<lambda>(op, v). oval op v d) (zip ops' vs) = map (\<lambda>(op, v). oval op v d) (zip ops vs) \<Longrightarrow>
check_outs ops' d vs = check_outs ops d vs"
  by (simp add: check_outs_alt check_outs_alt_def)

end