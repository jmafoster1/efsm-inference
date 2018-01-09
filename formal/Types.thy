theory Types
  imports "~~/src/HOL/Analysis/Finite_Cartesian_Product"
begin

datatype nil_or_int = Nil | I int

type_synonym inputs = "nat => nil_or_int"
type_synonym outputs = "nat \<Rightarrow> nil_or_int"
type_synonym data = "nat \<Rightarrow> nil_or_int"

definition empty_inputs :: "inputs" where
"empty_inputs \<equiv> \<lambda>x . Nil"

definition empty_outputs :: "inputs" where
"empty_outputs \<equiv> \<lambda>x . Nil"

definition empty_data :: "inputs" where
"empty_data \<equiv> \<lambda>x . Nil"

definition overwrite :: "('a => 'b) \<Rightarrow> 'a * 'b \<Rightarrow> ('a \<Rightarrow> 'b)" (infix "\<circ>" 10) where
(* Definitions not accepting patterns in Isabelle is truly horrible...*)
"overwrite vs \<equiv> \<lambda>(n,v) . \<lambda> m . if m = n then v else vs(m)"




(* We don't know or care how many inputs or outputs there are but there must 
  be at least one of each, otherwise it doesn't make sense to talk about observability.
  There also has to be at least one data register 
  ... otherwise the data vector stuff implodes...*)
(*
axiomatization inputsize :: "nat" where at_least_one_input: "inputsize > 0"
axiomatization outputsize :: "nat" where at_least_one_output: "outputsize > 0"
axiomatization datasize :: "nat" where at_least_one_register: "datasize > 0"

typedef inputindex = "{x::nat .x < inputsize}"
  apply simp
  apply (rule_tac x="0" in exI)
  apply (rule at_least_one_input)
  done
instance inputindex :: finite
  proof
    show "finite (UNIV :: inputindex set)"
      unfolding type_definition.univ[OF type_definition_inputindex]
      by auto
  qed

typedef outputindex = "{x::nat . x < outputsize}"
  apply simp
  apply (rule_tac x="0" in exI)
  apply (rule at_least_one_output)
  done
instance outputindex :: finite
  proof
    show "finite (UNIV :: outputindex set)"
      unfolding type_definition.univ[OF type_definition_outputindex]
      by auto
  qed

typedef dataindex = "{x::nat . x < datasize}"
  apply simp
  apply (rule_tac x="0" in exI)
  apply (rule at_least_one_register)
  done
instance dataindex :: finite
  proof
    show "finite (UNIV :: dataindex set)"
      unfolding type_definition.univ[OF type_definition_dataindex]
      by auto
  qed

type_synonym inputs = "(nil_or_int ^ inputindex)"
type_synonym outputs = "(nil_or_int ^ outputindex)"
type_synonym data = "(nil_or_int ^ dataindex)"
*)


end