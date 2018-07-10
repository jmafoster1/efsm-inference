theory Types
  imports AExp GExp
begin
type_synonym label = string
type_synonym arity = nat
type_synonym inputs = "int list"
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

type_synonym destination = "(statename \<times> transition)"

record efsm =
  S :: "statename list"
  s0 :: statename
  T :: "(statename \<times> statename) \<Rightarrow> transition list"

primrec index2state :: "int list \<Rightarrow> nat \<Rightarrow> state" where
  "index2state [] _ = <>" |
  "index2state (h#t) i = (\<lambda>x. if x = I i then h else (index2state t (i+1)) x)"

abbreviation join_ir :: "int list \<Rightarrow> state \<Rightarrow> state" where
  "join_ir i r \<equiv> (\<lambda>x. case x of
    R n \<Rightarrow> r (R n) |
    I n \<Rightarrow> (index2state i 1) (I n)
  )"

lemma "join_ir [1, 2] <> = <I 1:=1, I 2:=2>"
  apply (rule ext)
  apply (case_tac x)
   apply simp
  by simp
end
