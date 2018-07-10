theory Types
  imports AExp "Show.Show_Instances" GExp
begin
type_synonym label = string
type_synonym arity = nat
type_synonym inputs = "int list"
type_synonym registers = state
type_synonym outputs = "int list"
type_synonym guard = "gexp"
type_synonym output_function = "aexp"
type_synonym update_function = "(vname \<times> aexp)"
type_synonym statename = int
type_synonym event = "(label \<times> inputs)"
type_synonym trace = "event list" (*Ideally written as label(i1, i2, ...)*)
type_synonym observation = "outputs list"

record transition =
  Label :: label
  Arity :: arity
  Guard :: "guard list"
  Outputs :: "output_function list"
  Updates :: "update_function list"

record efsm =
  S :: "statename list"
  s0 :: statename
  T :: "(statename \<times> statename) \<Rightarrow> transition list"

lemmas shows_stuff = showsp_int_def showsp_nat.simps shows_string_def null_state_def

definition index :: "int \<Rightarrow> string" where
  "index i = ''i''@(showsp_int (nat i) i '''')"

lemma i1 [simp]: "index 1 = ''i1''"
  by (simp add: shows_stuff index_def)

primrec index2state :: "int list \<Rightarrow> int \<Rightarrow> state" where
  "index2state [] _ = <>" |
  "index2state (h#t) i = (\<lambda>x. if x = index i then h else (index2state t (i+1)) x)"

abbreviation join_ir :: "int list \<Rightarrow> state \<Rightarrow> state" where
  "join_ir i r \<equiv> (\<lambda>x. if hd x = CHR ''i'' then index2state i 1 x else r x)"

lemma "join_ir [1, 2] <> = <''i1'':=1, ''i2'':=2>"
  apply (rule ext)
  by (simp add: shows_stuff index_def)
end
