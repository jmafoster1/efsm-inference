theory Option_Lexorder
imports Main
begin

instantiation option :: (linorder) linorder begin
fun less_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool" where
  "None < None = False" |
  "None < _ = True" |
  "Some _ < None = False" |
  "Some a < Some b = (a < b)"

fun less_eq_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool" where
  "less_eq_option a b = (a < b \<or> a = b)"

instance
  apply standard
  apply (metis less_eq_option.simps less_option.elims(2) dual_order.asym less_option.simps(3) option.inject)
     apply simp
    apply (case_tac x)
     apply (metis less_eq_option.simps less_option.elims(2) less_option.simps(2))
    apply simp
    apply (case_tac y)
     apply simp
    apply (case_tac z)
     apply simp
    apply auto[1]
   apply (metis less_eq_option.elims(2) less_option.elims(2) dual_order.asym option.discI option.inject option.simps(3))
  by (metis less_option.elims(3) less_eq_option.elims(3) less_option.simps(2) neqE option.inject)
end
declare less_eq_option.simps [simp del]

lemma max_None_l: "max None x = x"
  by (metis less_option.elims(2) max.absorb2 not_le option.simps(3))

lemma max_None_r: "max x None = x"
  by (simp add: max.commute max_None_l)

lemmas max_None = max_None_l max_None_r

lemma max_is_None: "(max x y = None) = (x = None \<and> y = None)"
  by (metis max.left_idem max_None_l max_None_r)

lemma max_Some_Some: "max (Some x) (Some y) = Some (max x y)"
  by (metis less_option.simps(4) max_def not_le)

lemma x_leq_None: "(x \<le> None) = (x = None)"
  by (meson eq_refl max_def max_is_None)

lemma None_leq_everything: "None \<le> x"
  by (metis linear x_leq_None)

lemma less_eq_Some_trans: "x < Some a \<Longrightarrow> a \<le> i \<Longrightarrow> x \<le> Some i"
  by (meson le_less_trans less_le less_option.simps(4) linear)

end