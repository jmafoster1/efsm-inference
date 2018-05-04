theory GExp
imports AExp
begin
datatype gexp = Eq aexp aexp | Gt aexp aexp | Lt aexp aexp | Nand gexp gexp

abbreviation Not :: "gexp \<Rightarrow> gexp" where
  "Not g \<equiv> Nand g g"

abbreviation
  Le :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" where
  "Le v va \<equiv> Not (Gt v va)"

abbreviation
  Ge :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" where
  "Ge v va \<equiv> Not (Lt v va)"

abbreviation
  Ne :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" where
  "Ne v va \<equiv> Not (Eq v va)"

abbreviation gOr :: "gexp \<Rightarrow> gexp \<Rightarrow> gexp" where
  "gOr v va \<equiv> Nand (Nand v v) (Nand va va)"

fun gval :: "gexp \<Rightarrow> state \<Rightarrow> bool" where
  "gval (Lt a\<^sub>1 a\<^sub>2) s = (aval a\<^sub>1 s < aval a\<^sub>2 s)" |
  "gval (Gt a\<^sub>1 a\<^sub>2) s = (aval a\<^sub>1 s > aval a\<^sub>2 s)" |
  "gval (Eq a\<^sub>1 a\<^sub>2) s = (aval a\<^sub>1 s = aval a\<^sub>2 s)" |
  "gval (Nand a\<^sub>1 a\<^sub>2) s = (\<not> (gval a\<^sub>1 s \<and> gval a\<^sub>2 s))"

abbreviation gexp_satisfiable :: "gexp \<Rightarrow> bool" where
  "gexp_satisfiable g \<equiv> (\<exists>s. gval g s)"

end