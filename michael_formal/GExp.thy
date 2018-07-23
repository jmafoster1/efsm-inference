theory GExp
imports AExp
begin
datatype gexp = Bc bool | Eq aexp aexp | Gt aexp aexp | Lt aexp aexp | Nor gexp gexp | Null vname

abbreviation gNot :: "gexp \<Rightarrow> gexp" where
  "gNot g \<equiv> Nor g g"

abbreviation
  Le :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" where
  "Le v va \<equiv> gNot (Gt v va)"

abbreviation
  Ge :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" where
  "Ge v va \<equiv> gNot (Lt v va)"

abbreviation
  Ne :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" where
  "Ne v va \<equiv> gNot (Eq v va)"

abbreviation gOr :: "gexp \<Rightarrow> gexp \<Rightarrow> gexp" where
  "gOr v va \<equiv> Nor (Nor v va) (Nor v va)"

lemma "\<not> (x \<or> y) = (\<not> x \<and> \<not> y)"
  by simp

abbreviation gAnd :: "gexp \<Rightarrow> gexp \<Rightarrow> gexp" where
  "gAnd v va \<equiv> Nor (Nor v v) (Nor va va)"

fun MaybeBoolInt :: "(int \<Rightarrow> int \<Rightarrow> bool) \<Rightarrow> value option \<Rightarrow> value option \<Rightarrow> bool option" where
  "MaybeBoolInt f (Some (Num a)) (Some (Num b)) = Some (f a b)" |
  "MaybeBoolInt _ _ _ = None"

abbreviation ValueGt :: "value option \<Rightarrow> value option \<Rightarrow> bool option"  where
  "ValueGt a b \<equiv> MaybeBoolInt (\<lambda>x::int.\<lambda>y::int.(x>y)) a b"

abbreviation ValueLt :: "value option \<Rightarrow> value option \<Rightarrow> bool option"  where
  "ValueLt a b \<equiv> MaybeBoolInt (\<lambda>x::int.\<lambda>y::int.(x<y)) a b"

fun gval :: "gexp \<Rightarrow> datastate \<Rightarrow> bool option" where
  "gval (Bc b) _ = Some b" |
  "gval (Lt a\<^sub>1 a\<^sub>2) s = ValueLt (aval a\<^sub>1 s) (aval a\<^sub>2 s)" |
  "gval (Gt a\<^sub>1 a\<^sub>2) s = ValueGt (aval a\<^sub>1 s) (aval a\<^sub>2 s)" |
  "gval (Eq a\<^sub>1 a\<^sub>2) s = Some (aval a\<^sub>1 s = aval a\<^sub>2 s)" |
  "gval (Nor a\<^sub>1 a\<^sub>2) s = (case (gval a\<^sub>1 s, gval a\<^sub>2 s) of 
    (Some x, Some y) \<Rightarrow> Some (\<not> (x \<or> y)) |
    _ \<Rightarrow> None
  )" |
  "gval (Null v) s = Some (s v = None)"

abbreviation maybe_or :: "bool option \<Rightarrow> bool option \<Rightarrow> bool option" where
  "maybe_or x y \<equiv> (case (x, y) of
    (Some a, Some b) \<Rightarrow> Some (a \<or> b) |
    _ \<Rightarrow> None
  )"

abbreviation maybe_not :: "bool option \<Rightarrow> bool option" where
  "maybe_not x \<equiv> (case x of Some a \<Rightarrow> Some (\<not>a) | None \<Rightarrow> None)"

lemma or_equiv: "gval (gOr x y) r = maybe_or (gval x r) (gval y r)"
  apply simp
  apply (cases "gval x r")
   apply (cases "gval y r")
    apply simp
   apply simp
  apply (cases "gval y r")
   apply simp
  by simp

lemma not_equiv: "maybe_not (gval x s) = gval (gNot x) s"
  apply simp
  apply (cases "gval x s")
   apply simp
  by simp

lemma nor_equiv: "gval (gNot (gOr a b)) s = gval (Nor a b) s"
  by (simp add: option.case_eq_if)

definition gexp_satisfiable :: "gexp \<Rightarrow> bool" where
  "gexp_satisfiable g \<equiv> (\<exists>s. gval g s = Some True)"

definition gexp_equiv :: "gexp \<Rightarrow> gexp \<Rightarrow> bool" where
  "gexp_equiv v va \<equiv> \<forall>s. gval v s = gval va s"
end