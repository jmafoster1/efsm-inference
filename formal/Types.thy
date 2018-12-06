theory Types
imports Main
begin

type_synonym inputname = int
type_synonym dataname = int
type_synonym outputname = int
type_synonym label = string
type_synonym arity = int

datatype valuetype = In int | St string
datatype exp = Lit valuetype | R dataname | I inputname | Plus exp exp | Minus exp exp | Mul exp exp

type_synonym inputs = "(inputname, valuetype) map"
type_synonym data = "(dataname, valuetype) map"
type_synonym outvalues = "(outputname, valuetype) map"

type_synonym guard = "(inputs \<times> data) => bool"
type_synonym outputs = "(inputs \<times> data) => outvalues"
type_synonym updates = "(inputs \<times> data) => data"

record transition = 
  label :: "label"
  arity :: "arity"
  guard :: "guard"
  outputs :: "outputs"
  updates :: "updates"

type_synonym statename = "int"

record efsm =
  S :: "statename list"
  s0 :: "statename"
  M :: "((statename * statename), transition list) map"

type_synonym trace = "(label \<times> inputs) list"
type_synonym observation = "outvalues list"

(* This now treats None as 0. 
This isn't ideal but it means that we don't have to pre-initialise variables *)
fun MaybeApplyInt :: "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> valuetype option \<Rightarrow> valuetype option \<Rightarrow> valuetype option" where
(* "MaybeApplyInt f None None = Some (Inl (f 0 0))"
|"MaybeApplyInt f None (Some (Inl r)) = (Some (Inl (f 0 r)))"
|"MaybeApplyInt f (Some (Inl l)) None = (Some (Inl (f l 0)))" *)
"MaybeApplyInt f _ None = None"
|"MaybeApplyInt f None _ = None"
|"MaybeApplyInt f (Some (In a)) (Some (In b)) = Some (In (f a b))"
|"MaybeApplyInt _ _ _ = None"

fun MaybeBoolInt :: "(int \<Rightarrow> int \<Rightarrow> bool) \<Rightarrow> valuetype option \<Rightarrow> valuetype option \<Rightarrow> bool" where
"MaybeBoolInt _ None _ = False"
|"MaybeBoolInt _ _ None = False"
|"MaybeBoolInt f (Some (In a)) (Some (In b)) = (f a b)"
|"MaybeBoolInt _ _ _ = False"

abbreviation MaybePlus :: "valuetype option \<Rightarrow> valuetype option \<Rightarrow> valuetype option" (infix "+" 40) where
"a + b \<equiv> MaybeApplyInt (\<lambda>x::int.\<lambda>y::int.(x+y)) a b"
abbreviation MaybeMinus :: "valuetype option \<Rightarrow> valuetype option \<Rightarrow> valuetype option" (infix "-" 40) where
"a - b \<equiv> MaybeApplyInt (\<lambda>x::int.\<lambda>y::int.(x-y)) a b"
abbreviation MaybeMul :: "valuetype option \<Rightarrow> valuetype option \<Rightarrow> valuetype option" (infix "*" 40) where
"a * b \<equiv> MaybeApplyInt (\<lambda>x::int.\<lambda>y::int.(x*y)) a b"

fun eval :: "data \<times> inputs \<Rightarrow> exp \<Rightarrow> valuetype option" where
"eval _ (Lit v) = Some v"
|"eval (dt,_) (R n) = dt(n)"
|"eval (_,ip) (I n) = ip(n)"
|"eval ctx (Plus e1 e2) = MaybePlus (eval ctx e1) (eval ctx e2)"
|"eval ctx (Minus e1 e2) = MaybeMinus (eval ctx e1) (eval ctx e2)"
|"eval ctx (Mul e1 e2) = MaybeMul (eval ctx e1) (eval ctx e2)"

abbreviation MaybeGt :: "valuetype option \<Rightarrow> valuetype option \<Rightarrow> bool" (infix ">" 40) where
"a > b \<equiv> MaybeBoolInt (\<lambda>x::int.\<lambda>y::int.(x>y)) a b"
abbreviation MaybeGtEq :: "valuetype option \<Rightarrow> valuetype option \<Rightarrow> bool" (infix "\<ge>" 40) where
"a \<ge> b \<equiv> MaybeBoolInt (\<lambda>x::int.\<lambda>y::int.(x\<ge>y)) a b"
abbreviation MaybeLt :: "valuetype option \<Rightarrow> valuetype option \<Rightarrow> bool" (infix "<" 40) where
"a < b \<equiv> MaybeBoolInt (\<lambda>x::int.\<lambda>y::int.(x<y)) a b"
abbreviation MaybeLtEq :: "valuetype option \<Rightarrow> valuetype option \<Rightarrow> bool" (infix "\<le>" 40) where
"a \<le> b \<equiv> MaybeBoolInt (\<lambda>x::int.\<lambda>y::int.(x\<le>y)) a b"

end
