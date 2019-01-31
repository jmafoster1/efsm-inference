theory Transition_Ordering
  imports "../Transition" GExp_Orderings "~~/src/HOL/Library/List_Lexorder"
          "~~/src/HOL/Library/Product_Lexorder"
begin

instantiation "transition_ext" :: (linorder) linorder begin

definition less_transition_ext :: "'a::linorder transition_scheme \<Rightarrow> 'a transition_scheme \<Rightarrow> bool" where
"less_transition_ext t1 t2 = (if Label t1 = Label t2 then
                                   (if Arity t1 = Arity t2 then
                                      (if (Guard t1) = (Guard t2) then
                                         (if (Outputs t1) = (Outputs t2) then
                                            (if (Updates t1) = (Updates t2) then
                                               less (more t1) (more t2)
                                           else ((Updates t1)) < ((Updates t2)))
                                         else ((Outputs t1)) < ((Outputs t2)))
                                       else ((Guard t1)) < ((Guard t2)))
                                    else (Arity t1) < (Arity t2))
                                 else Label t1 < Label t2)"

definition less_eq_transition_ext :: "'a::linorder transition_scheme \<Rightarrow> 'a transition_scheme \<Rightarrow> bool" where
"less_eq_transition_ext t1 t2 = (t1 < t2 \<or> t1 = t2)"

instance proof
  fix x y::"'a transition_ext"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    using less_eq_transition_ext_def less_transition_ext_def by auto
  fix x::"'a transition_ext" 
  show "x \<le> x"
    by (simp add: less_eq_transition_ext_def)
  fix x y z::"'a transition_ext"
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    apply (simp add: less_eq_transition_ext_def less_transition_ext_def)
    apply (case_tac "x=y")
     apply auto[1]
    apply simp
    apply (case_tac "Label x = Label y")
     apply simp
     apply (case_tac "Arity x = Arity y")
      apply simp
      apply (case_tac "Guard x = Guard y")
       apply simp
       apply (case_tac "Outputs x = Outputs y")
        apply simp
        apply (case_tac "Updates x = Updates y")
         apply simp
         apply (case_tac "Label y = Label z")
          apply simp
          apply (case_tac "Arity y = Arity z")
           apply simp
           apply (case_tac "Guard y = Guard z")
            apply simp
            apply (case_tac "Outputs y = Outputs z")
             apply simp
             apply (case_tac "Updates y = Updates z")
              apply auto[1]
             apply auto[1]
            apply auto[1]
           apply auto[1]
          apply auto[1]
         apply auto[1]
        apply (case_tac "Label y = Label z")
         apply simp
         apply (case_tac "Arity y = Arity z")
          apply simp
          apply (case_tac "Guard y = Guard z")
           apply simp
           apply (case_tac "Outputs y = Outputs z")
            apply simp
            apply (case_tac "Updates y = Updates z")
             apply simp
            apply auto[1]
           apply auto[1]
          apply auto[1]
         apply auto[1]
        apply auto[1]
               apply (case_tac "Label y = Label z")
         apply simp
         apply (case_tac "Arity y = Arity z")
          apply simp
          apply (case_tac "Guard y = Guard z")
           apply simp
           apply (case_tac "Outputs y = Outputs z")
            apply simp
            apply (case_tac "Updates y = Updates z")
             apply simp
            apply auto[1]
           apply auto[1]
          apply auto[1]
         apply auto[1]
       apply auto[1]
        apply (case_tac "Label y = Label z")
         apply simp
         apply (case_tac "Arity y = Arity z")
          apply simp
          apply (case_tac "Guard y = Guard z")
           apply simp
           apply (case_tac "Outputs y = Outputs z")
            apply simp
            apply (case_tac "Updates y = Updates z")
            apply auto[1]
           apply auto[1]
          apply auto[1]
         apply auto[1]
      apply auto[1]
        apply (case_tac "Label y = Label z")
         apply simp
         apply (case_tac "Arity y = Arity z")
          apply simp
          apply (case_tac "Guard y = Guard z")
           apply simp
           apply (case_tac "Outputs y = Outputs z")
            apply (case_tac "Updates y = Updates z")
            apply auto[1]
           apply auto[1]
          apply auto[1]
         apply auto[1]
     apply auto[1]
        apply (case_tac "Label y = Label z")
         apply simp
         apply (case_tac "Arity y = Arity z")
          apply simp
          apply (case_tac "Guard y = Guard z")
           apply (case_tac "Outputs y = Outputs z")
            apply (case_tac "Updates y = Updates z")
            apply auto[1]
           apply auto[1]
          apply auto[1]
         apply auto[1]
    by auto[1]
  fix x y::"'a transition_ext"
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    apply (simp add: less_eq_transition_ext_def less_transition_ext_def)
    by (metis less_asym order.asym)
  fix x y::"'a transition_ext"
  show "x \<le> y \<or> y \<le> x"
    apply (simp add: less_eq_transition_ext_def less_transition_ext_def)
    by (meson equality injD linorder_cases)
qed
end
end