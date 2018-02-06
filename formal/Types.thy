theory Types
imports Main
begin

type_synonym inputname = int
type_synonym dataname = int
type_synonym outputname = int

type_synonym valuetype = "(int + string)"

type_synonym inputs = "inputname \<Rightarrow> valuetype option"
type_synonym data = "dataname \<Rightarrow> valuetype option"
type_synonym outvalues = "outputname \<Rightarrow> valuetype option"

type_synonym guard = "(inputs \<times> data) => bool"
type_synonym outputs = "(inputs \<times> data) => outvalues"
type_synonym updates = "(inputs \<times> data) => data"

type_synonym transition = "(guard \<times> outputs \<times> updates)"

type_synonym statename = "int"

record efsm =
  S :: "statename list"
  s0 :: "statename"
  d0 :: data
  M :: "(statename * statename) \<Rightarrow> transition list"

type_synonym trace = "inputs list"
type_synonym observation = "outvalues list"

fun MaybeApplyInt :: "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> valuetype option \<Rightarrow> valuetype option \<Rightarrow> valuetype option" where
"MaybeApplyInt _ None _ = None"
|"MaybeApplyInt _ _ None = None"
|"MaybeApplyInt f (Some (Inl a)) (Some (Inl b)) = Some (Inl (f a b))"
|"MaybeApplyInt _ _ _ = None"

fun MaybeBoolInt :: "(int \<Rightarrow> int \<Rightarrow> bool) \<Rightarrow> valuetype option \<Rightarrow> valuetype option \<Rightarrow> bool" where
"MaybeBoolInt _ None _ = False"
|"MaybeBoolInt _ _ None = False"
|"MaybeBoolInt f (Some (Inl a)) (Some (Inl b)) = (f a b)"
|"MaybeBoolInt _ _ _ = False"

abbreviation MaybePlus :: "valuetype option \<Rightarrow> valuetype option \<Rightarrow> valuetype option" (infix "+" 40) where
"a + b \<equiv> MaybeApplyInt (\<lambda>x::int.\<lambda>y::int.(x+y)) a b"
abbreviation MaybeMinus :: "valuetype option \<Rightarrow> valuetype option \<Rightarrow> valuetype option" (infix "-" 40) where
"a - b \<equiv> MaybeApplyInt (\<lambda>x::int.\<lambda>y::int.(x-y)) a b"
abbreviation MaybeMul :: "valuetype option \<Rightarrow> valuetype option \<Rightarrow> valuetype option" (infix "*" 40) where
"a * b \<equiv> MaybeApplyInt (\<lambda>x::int.\<lambda>y::int.(x*y)) a b"

abbreviation MaybeGt :: "valuetype option \<Rightarrow> valuetype option \<Rightarrow> bool" (infix ">" 40) where
"a > b \<equiv> MaybeBoolInt (\<lambda>x::int.\<lambda>y::int.(x>y)) a b"
abbreviation MaybeGtEq :: "valuetype option \<Rightarrow> valuetype option \<Rightarrow> bool" (infix "\<ge>" 40) where
"a \<ge> b \<equiv> MaybeBoolInt (\<lambda>x::int.\<lambda>y::int.(x\<ge>y)) a b"
abbreviation MaybeLt :: "valuetype option \<Rightarrow> valuetype option \<Rightarrow> bool" (infix "<" 40) where
"a < b \<equiv> MaybeBoolInt (\<lambda>x::int.\<lambda>y::int.(x<y)) a b"
abbreviation MaybeLtEq :: "valuetype option \<Rightarrow> valuetype option \<Rightarrow> bool" (infix "\<le>" 40) where
"a \<le> b \<equiv> MaybeBoolInt (\<lambda>x::int.\<lambda>y::int.(x\<le>y)) a b"

end
