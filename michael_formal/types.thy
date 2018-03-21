theory types
  imports "~~/src/HOL/IMP/Hoare"
begin
type_synonym label = string
type_synonym arity = nat
type_synonym inputs = state
type_synonym registers = state
type_synonym outputs = state
type_synonym guard = "bexp list"
type_synonym output_function = "(string \<times> aexp) list"
type_synonym update_function = "(string \<times> aexp) list"
type_synonym statename = int
type_synonym trace = "(label \<times> state) list" (*Ideally written as label(i1, i2, ...)*)
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

end