theory Transition
imports GExp
begin

type_synonym label = String.literal
type_synonym arity = nat
type_synonym inputs = "value list"
type_synonym outputs = "value option list"
type_synonym output_function = "aexp"
type_synonym update_function = "(nat \<times> aexp)"
type_synonym updates = "update_function list"

text_raw{*\snip{transitiontype}{1}{2}{%*}
record transition =
  Label :: label
  Arity :: nat
  Guard :: "gexp list"
  Outputs :: "aexp list"
  Updates :: updates
text_raw{*}%endsnip*}

lemma transition_equality: "((x::transition) = y) = ((Label x) = (Label y) \<and>
                                (Arity x) = (Arity y) \<and>
                                (Guard x) = (Guard y) \<and>
                                (Outputs x) = (Outputs y) \<and>
                                (Updates x) = (Updates y))"
  by auto

lemma unequal_labels[simp]: "Label t1 \<noteq> Label t2 \<Longrightarrow> t1 \<noteq> t2"
  by auto

lemma unequal_arities[simp]: "Arity t1 \<noteq> Arity t2 \<Longrightarrow> t1 \<noteq> t2"
  by auto

definition same_structure :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "same_structure t1 t2 = (Label t1 = Label t2 \<and>
                           Arity t1 = Arity t2 \<and>
                           list_all (\<lambda>(g1, g2). gexp_same_structure g1 g2) (zip (Guard t1) (Guard t2)))"

definition enumerate_inputs :: "transition \<Rightarrow> nat set" where
  "enumerate_inputs t = (\<Union> set (map enumerate_gexp_inputs (Guard t))) \<union>
                        (\<Union> set (map enumerate_aexp_inputs (Outputs t))) \<union>
                        (\<Union> set (map (\<lambda>(_, u). enumerate_aexp_inputs u) (Updates t)))"

definition max_input :: "transition \<Rightarrow> nat option" where
  "max_input t = (if enumerate_inputs t = {} then None else Some (Max (enumerate_inputs t)))"

definition enumerate_registers :: "transition \<Rightarrow> nat set" where
  "enumerate_registers t = (\<Union> set (map enumerate_gexp_regs (Guard t))) \<union>
                           (\<Union> set (map enumerate_aexp_regs (Outputs t))) \<union>
                           (\<Union> set (map (\<lambda>(_, u). enumerate_aexp_regs u) (Updates t))) \<union>
                           (\<Union> set (map (\<lambda>(r, _). enumerate_aexp_regs (V (R r))) (Updates t)))"

definition max_reg :: "transition \<Rightarrow> nat option" where
  "max_reg t = (if enumerate_registers t = {} then None else Some (Max (enumerate_registers t)))"

definition valid_transition :: "transition \<Rightarrow> bool" where
  "valid_transition t = (case max_input t of None \<Rightarrow> Arity t = 0 | Some x \<Rightarrow> x \<le> Arity t)"

end
