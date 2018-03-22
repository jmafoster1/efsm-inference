theory types
  imports "~~/src/HOL/IMP/Hoare" "Show.Show_Instances"
begin
type_synonym label = string
type_synonym arity = nat
type_synonym inputs = "int list"
type_synonym registers = state
type_synonym outputs = state
type_synonym guard = "bexp list"
type_synonym output_function = "(string \<times> aexp) list"
type_synonym update_function = "(string \<times> aexp) list"
type_synonym statename = int
type_synonym trace = "(label \<times> inputs) list" (*Ideally written as label(i1, i2, ...)*)
type_synonym observation = "outputs list"


record transition =
  Label :: label
  Arity :: arity
  Guard :: guard
  Outputs :: output_function
  Updates :: update_function

type_synonym destination = "(statename \<times> transition)"

record efsm =
  S :: "statename list"
  s0 :: statename
  T :: "(statename \<times> statename) \<Rightarrow> transition list"

definition join :: "state \<Rightarrow> state \<Rightarrow> state" where
  "join s1 s2 = (\<lambda>x. if (aval (V x) s1) \<noteq> 0 then (aval (V x) s1) else (aval (V x) s2))"
declare join_def [simp]

lemma "\<forall>z. \<exists>x y. (aval (V v) (join x y) = aval (V v) z)"
  by auto

lemma "\<forall> x y. \<exists>z. (aval (V v) z) = aval (V v) (join x y)"
  by auto

definition index :: "int \<Rightarrow> string" where
  "index i = ''i''@(showsp_int (nat i) i '''')"
declare index_def [simp]

lemma i1: "index 2 = ''i2''"
  apply (simp add: showsp_int_def)
  apply (simp add: showsp_nat.simps)
  apply (simp add: shows_string_def)
  done

primrec input2state :: "int list \<Rightarrow> int \<Rightarrow> state" where
  "input2state [] _ = <>" |
  "input2state (h#t) i = (\<lambda>x. if x = (index i) then h else ((input2state t (i+1)) x))"
declare input2state_def [simp]

lemma "input2state [1, 2] 1 = <''i1'':=1, ''i2'':=2>"
  apply (rule ext)
  apply (simp add: showsp_int_def cong: if_cong)
  apply (simp add: showsp_nat.simps)
  apply (simp add: shows_string_def)
  done

end
