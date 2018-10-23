theory Prod_Linorder
imports Main
begin
instantiation prod :: (linorder, linorder) linorder begin
fun less_eq_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
  "less_eq_prod (f1, s1) (f2, s2) = (if f1 = f2 then s1 \<le> s2 else f1 \<le> f2)"

fun less_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
  "less_prod (f1, s1) (f2, s2) = (if f1 = f2 then s1 < s2 else f1 < f2)"

instance
  apply standard
      apply force
     apply auto[1]
    apply (smt Prod_Linorder.less_eq_prod.elims(2) Prod_Linorder.less_eq_prod.simps antisym_conv order.trans)
   apply (smt Pair_inject antisym less_eq_prod.elims(2))
  by auto
end

end