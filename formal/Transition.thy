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

text_raw\<open>\snip{transitiontype}{1}{2}{%\<close>
record transition =
  Label :: String.literal
  Arity :: nat
  Guard :: "gexp list"
  Outputs :: "aexp list"
  Updates :: "(nat \<times> aexp) list"
text_raw\<open>}%endsnip\<close>

definition same_structure :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "same_structure t1 t2 = (
    Label t1 = Label t2 \<and>
    Arity t1 = Arity t2 \<and>
    length (Outputs t1) = length (Outputs t2)
  )"

definition enumerate_inputs :: "transition \<Rightarrow> nat set" where
  "enumerate_inputs t = (\<Union> (set (map enumerate_gexp_inputs (Guard t)))) \<union>
                        (\<Union> (set (map enumerate_aexp_inputs (Outputs t)))) \<union>
                        (\<Union> (set (map (\<lambda>(_, u). enumerate_aexp_inputs u) (Updates t))))"

definition max_input :: "transition \<Rightarrow> nat option" where
  "max_input t = (if enumerate_inputs t = {} then None else Some (Max (enumerate_inputs t)))"

definition total_max_input :: "transition \<Rightarrow> nat" where
  "total_max_input t = (case max_input t of None \<Rightarrow> 0 | Some a \<Rightarrow> a)"

definition enumerate_registers :: "transition \<Rightarrow> nat set" where
  "enumerate_registers t = (\<Union> (set (map enumerate_gexp_regs (Guard t)))) \<union>
                           (\<Union> (set (map enumerate_aexp_regs (Outputs t)))) \<union>
                           (\<Union> (set (map (\<lambda>(_, u). enumerate_aexp_regs u) (Updates t)))) \<union>
                           (\<Union> (set (map (\<lambda>(r, _). enumerate_aexp_regs (V (R r))) (Updates t))))"

lemma gexp_regs_list: "\<exists>l. \<Union> (set (map enumerate_gexp_regs G)) = set l"
proof(induct G)
  case Nil
  then show ?case
    by simp
next
  case (Cons a G)
  then show ?case
    by (metis enumerate_gexp_regs_list Sup_insert list.simps(15) list.simps(9) set_append)
qed

lemma outputs_regs_list: "\<exists>l. \<Union> (set (map enumerate_aexp_regs P)) = set l"
proof(induct P)
  case Nil
  then show ?case
    by simp
next
  case (Cons a P)
  then show ?case
    by (metis enumerate_aexp_regs_list Sup_insert list.simps(15) list.simps(9) set_append)
qed

lemma updates_regs_list_1: "\<exists>l. \<Union> (set (map (\<lambda>(uu, y). enumerate_aexp_regs y) U)) = set l"
proof(induct U)
  case Nil
  then show ?case
    by simp
next
  case (Cons a U)
  then show ?case
    apply clarify
    apply simp
    apply (cases a)
    apply simp
    by (metis enumerate_aexp_regs_list set_append)
qed

lemma updates_regs_list_2: "\<exists>l. \<Union> (set (map (\<lambda>(r, uu). enumerate_aexp_regs (V (R r))) U)) = set l"
proof(induct U)
case Nil
  then show ?case
    by simp
next
  case (Cons a U)
  then show ?case
    apply clarify
    apply simp
    apply (cases a)
    apply simp
    by (metis List.set_insert)
qed

lemma enumerate_registers_list: "\<exists>l. enumerate_registers t = set l"
  unfolding enumerate_registers_def
  using gexp_regs_list[of "Guard t"]
        outputs_regs_list[of "Outputs t"]
        updates_regs_list_1[of "Updates t"]
        updates_regs_list_2[of "Updates t"]
  by (metis set_union)

definition max_reg :: "transition \<Rightarrow> nat option" where
  "max_reg t = (if enumerate_registers t = {} then None else Some (Max (enumerate_registers t)))"

lemma max_reg_none_no_updates: "Transition.max_reg t = None \<Longrightarrow> Updates t = []"
  apply (simp add: Transition.max_reg_def)
  apply (case_tac "enumerate_registers t = {}")
   apply (simp add: enumerate_registers_def)
   apply (case_tac "Updates t")
  by auto

definition total_max_reg :: "transition \<Rightarrow> nat" where
  "total_max_reg t = (case max_reg t of None \<Rightarrow> 0 | Some a \<Rightarrow> a)"

definition valid_transition :: "transition \<Rightarrow> bool" where
  "valid_transition t = (case max_input t of None \<Rightarrow> Arity t = 0 | Some x \<Rightarrow> x < Arity t)"

definition enumerate_strings :: "transition \<Rightarrow> String.literal set" where
  "enumerate_strings t = (\<Union> (set (map enumerate_gexp_strings (Guard t)))) \<union>
                         (\<Union> (set (map enumerate_aexp_strings (Outputs t)))) \<union>
                         (\<Union> (set (map (\<lambda>(_, u). enumerate_aexp_strings u) (Updates t)))) \<union>
                         (\<Union> (set (map (\<lambda>(r, _). enumerate_aexp_strings (V (R r))) (Updates t))))"

definition enumerate_ints :: "transition \<Rightarrow> int set" where
  "enumerate_ints t = (\<Union> (set (map enumerate_gexp_ints (Guard t)))) \<union>
                         (\<Union> (set (map enumerate_aexp_ints (Outputs t)))) \<union>
                         (\<Union> (set (map (\<lambda>(_, u). enumerate_aexp_ints u) (Updates t)))) \<union>
                         (\<Union> (set (map (\<lambda>(r, _). enumerate_aexp_ints (V (R r))) (Updates t))))"

end
