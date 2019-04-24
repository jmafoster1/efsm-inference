theory Transition
imports GExp
begin

type_synonym label = String.literal
type_synonym arity = nat
type_synonym inputs = "value list"
type_synonym outputs = "value option list"
type_synonym guard = "gexp"
type_synonym output_function = "aexp"
type_synonym update_function = "(vname \<times> aexp)"
type_synonym updates = "update_function list"

record transition =
  Label :: label
  Arity :: nat
  Guard :: "guard list"
  Outputs :: "output_function list"
  Updates :: "update_function list"

lemma transition_equality: "((x::transition) = y) = ((Label x) = (Label y) \<and>
                                (Arity x) = (Arity y) \<and>
                                (Guard x) = (Guard y) \<and>
                                (Outputs x) = (Outputs y) \<and>
                                (Updates x) = (Updates y))"
proof
  fix x y :: transition
  assume "x = y"
  show "Label x = Label y \<and> Arity x = Arity y \<and> Guard x = Guard y \<and> Outputs x = Outputs y \<and> Updates x = Updates y"
    by (simp add: \<open>x = y\<close>)
next
  fix x y :: transition
  assume "Label x = Label y \<and> Arity x = Arity y \<and> Guard x = Guard y \<and> Outputs x = Outputs y \<and> Updates x = Updates y"
  show "x = y"
    by (simp add: \<open>Label x = Label y \<and> Arity x = Arity y \<and> Guard x = Guard y \<and> Outputs x = Outputs y \<and> Updates x = Updates y\<close>)
qed

lemma unequal_labels[simp]: "Label t1 \<noteq> Label t2 \<Longrightarrow> t1 \<noteq> t2"
  by auto

lemma unequal_arities[simp]: "Arity t1 \<noteq> Arity t2 \<Longrightarrow> t1 \<noteq> t2"
  by auto

definition same_structure :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "same_structure t1 t2 = (Label t1 = Label t2 \<and>
                           Arity t1 = Arity t2 \<and>
                           list_all (\<lambda>(g1, g2). gexp_same_structure g1 g2) (zip (Guard t1) (Guard t2)))"

end
