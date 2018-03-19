theory types
  imports "~~/src/HOL/IMP/Hoare"
begin
type_synonym label = string
type_synonym arity = nat
type_synonym inputs = "int list"
type_synonym registers = state
type_synonym outputs = "int list"
type_synonym guard = "inputs \<Rightarrow> registers \<Rightarrow> bool"
type_synonym output_function = "inputs \<Rightarrow> registers \<Rightarrow> outputs"
type_synonym update_function = "inputs \<Rightarrow> registers \<Rightarrow> registers"
type_synonym statename = int
type_synonym trace = "(label \<times>(int list)) list" (*Ideally written as label(i1, i2, ...)*)
type_synonym observation = "outputs list"

record transition = 
  Label :: "label"
  Arity :: "arity"
  Guard :: "guard"
  Outputs :: "output_function"
  Updates :: "update_function"

record efsm =
  S :: "statename list"
  s0 :: "statename"
  T :: "(statename * statename) \<Rightarrow> transition list"
end