theory GExp
imports "~~/src/HOL/IMP/AExp"
begin
datatype gexp = Eq aexp aexp | Gt aexp aexp | Lt aexp aexp | Not gexp | Or gexp gexp

fun gval :: "gexp \<Rightarrow> state \<Rightarrow> bool" where
  "gval (Lt a\<^sub>1 a\<^sub>2) s = (aval a\<^sub>1 s < aval a\<^sub>2 s)" |
  "gval (Gt a\<^sub>1 a\<^sub>2) s = (aval a\<^sub>1 s > aval a\<^sub>2 s)" |
  "gval (Eq a\<^sub>1 a\<^sub>2) s = (aval a\<^sub>1 s = aval a\<^sub>2 s)" |
  "gval (Not a) s = (\<not> gval a s)" |
  "gval (Or a\<^sub>1 a\<^sub>2) s = (gval a\<^sub>1 s \<or> gval a\<^sub>2 s)"

end