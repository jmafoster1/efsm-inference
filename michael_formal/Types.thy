theory Types
  imports AExp GExp
begin

type_synonym label = string
type_synonym arity = nat
type_synonym inputs = "value list"
type_synonym outputs = "value list"
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

record 'statename efsm =
  s0 :: 'statename
  T :: "('statename \<times> 'statename) \<Rightarrow> transition set"

primrec index2state :: "value list \<Rightarrow> nat \<Rightarrow> datastate" where
  "index2state [] _ = <>" |
  "index2state (h#t) i = (\<lambda>x. if x = I i then Some h else (index2state t (i+1)) x)"

abbreviation join_ir :: "value list \<Rightarrow> datastate \<Rightarrow> datastate" where
  "join_ir i r \<equiv> (\<lambda>x. case x of
    R n \<Rightarrow> r (R n) |
    I n \<Rightarrow> (index2state i 1) (I n)
  )"

lemma "join_ir [Num 1, Num 2] <> = [I 1:=Num 1, I 2:= Num 2]"
  apply (rule ext)
  apply (case_tac x)
   apply simp
  by simp
end
