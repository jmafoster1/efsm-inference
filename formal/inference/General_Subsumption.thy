theory General_Subsumption
imports "../Contexts" Trace_Matches
begin

lemma ctx_simp: "(\<lambda>r. and (if r = V (I i) then snd (V (I i), cexp.Eq s) else cexp.Bc True) (\<lbrakk>\<rbrakk> r)) = \<lbrakk>V (I i) \<mapsto> Eq s\<rbrakk>"
  apply (rule ext)
  by simp

lemma incoming_transition_alt_def: "incoming_transition_to e n = (\<exists>t from. ((from, n), t) |\<in>| e)"
  apply (simp add: incoming_transition_to_def)
  apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse)
  apply (simp add: fmember_def)
  apply (simp add: Set.filter_def)
  by auto

lemma no_step_to: "\<not> incoming_transition_to t m \<Longrightarrow>
       step t n r aa b \<noteq> Some (uw, m, ux, r')"
  apply (simp add: incoming_transition_alt_def step_def)
  apply safe
  apply (case_tac "fthe_elem (possible_steps t n r aa b)")
  apply simp
  using singleton_dest by blast

lemma no_route_to_no_access: "\<not> incoming_transition_to t 0 \<Longrightarrow> \<forall>r s. s \<noteq> 0 \<longrightarrow> \<not>gets_us_to 0 t s r p"
proof(induct p)
  case Nil
  then show ?case
    by (simp add: no_further_steps)
next
  case (Cons a p)
  then show ?case
    apply clarify
    apply (rule gets_us_to.cases)
       apply simp
      apply simp
     apply clarify
     apply simp
     apply (metis no_step_to Cons.hyps)
    by simp
qed

lemma no_return_to_initial: "\<not> incoming_transition_to t 0 \<Longrightarrow> accepts_trace t p \<and> gets_us_to 0 t 0 Map.empty p \<Longrightarrow> p = []"
proof(induct p)
  case Nil
  then show ?case
    by simp
next
  case (Cons a p)
  then show ?case
    apply (simp add: accepts_trace_def)
    apply (rule gets_us_to.cases)
       apply auto[1]
      apply simp
     apply clarify
     apply simp
     apply (case_tac "s' = 0")
      apply (simp add: no_step_to)
     apply (simp add: no_route_to_no_access)
    apply clarify
    by (simp add: no_step_none)
qed

lemma anterior_context_no_return_to_zero: "\<not> incoming_transition_to t 0 \<Longrightarrow> accepts_trace t p \<and> gets_us_to 0 t 0 Map.empty p \<longrightarrow> anterior_context t' p = \<lbrakk>\<rbrakk>"
proof(induct p)
  case Nil
  then show ?case
    by (simp add: anterior_context_def)
next
  case (Cons a p)
  then show ?case
    using no_return_to_initial
    by auto
qed

lemma inconsistent_c_aux: "gval (cexp2gexp r (c r)) sa \<noteq> Some True \<Longrightarrow>
       (r = V (I i) \<longrightarrow> gval (cexp2gexp (V (I i)) (and (cexp.Eq s) (c (V (I i))))) sa \<noteq> Some True) \<and>
             (r \<noteq> V (I i) \<longrightarrow> gval (cexp2gexp r (c r)) sa \<noteq> Some True)"
proof-
  assume premise: "gval (cexp2gexp r (c r)) sa \<noteq> Some True"
  have aux: "\<And>v c sa s. gval (cexp2gexp v (c v)) sa \<noteq> Some True \<Longrightarrow>
       gval (cexp2gexp v (and (cexp.Eq s) (c v))) sa = Some True \<Longrightarrow> False"
  apply (case_tac "c v")
        apply simp+
      apply (case_tac "s=x3")
       apply simp+
     apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval v sa)")
      apply simp+
    apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval v sa) (Some x5)")
     apply simp+
   apply (case_tac "gval (cexp2gexp v x6) sa")
    apply simp+
  apply (case_tac "gval (cexp2gexp v x71) sa")
   apply simp+
  apply (case_tac "gval (cexp2gexp v x72) sa")
  by auto
  show ?thesis
    using premise aux
    by auto
qed

lemma inconsistent_c: "\<not>consistent c \<Longrightarrow> \<not>consistent (\<lambda>r. and (if r = V (I i) then snd (V (I i), cexp.Eq s) else cexp.Bc True) (c r))"
proof-
  assume premise: "\<not> consistent c"
  show ?thesis
    using premise
    apply (simp add: consistent_def)
    apply clarify
    using inconsistent_c_aux
    by blast
qed

lemma not_undef_gval: "\<forall>r. c r = Undef \<or> gval (cexp2gexp r (c r)) s = Some True \<Longrightarrow>
         c (V (I i)) \<noteq> Undef \<Longrightarrow> gval (cexp2gexp (V (I i)) (c (V (I i)))) s = Some True"
  by auto

lemma ctx_simp2: "(\<lambda>r. and (if r = V (I i) then snd (V (I i), cexp.Eq s) else cexp.Bc True) (c r)) = 
       (\<lambda>x. (if x = V (I i) then and (cexp.Eq s) (c x) else c x))"
  apply (rule ext)
  by simp

lemma test2: "consistent (\<lambda>r. and (if r = V (I i) then snd (V (I i), cexp.Eq s) else cexp.Bc True) (c r)) \<Longrightarrow> consistent c"
  using inconsistent_c
  by auto

lemma generalise_subsumption: "c (V (R ri)) = Undef \<Longrightarrow> 
                               c (V (I i)) = Bc True \<Longrightarrow> 
                               subsumes c (remove_guard_add_update \<lparr>Label=l, Arity=a, Guard=[GExp.Eq (V (I i)) (L v)], Outputs=[], Updates=[]\<rparr> i ri)
                                                                   \<lparr>Label=l, Arity=a, Guard=[GExp.Eq (V (I i)) (L v)], Outputs=[], Updates=[]\<rparr>"
  apply (simp add: subsumes_def)
  apply safe
          apply (simp add: remove_guard_add_update_def)
         apply (simp add: remove_guard_add_update_def)
        apply (simp add: remove_guard_add_update_def)
       apply (simp add: remove_guard_add_update_def)
       apply (case_tac "cval (c (V (I i))) ia")
        apply simp
       apply simp
      apply (case_tac "cval (c r) ia")
       apply simp
      apply (simp add: remove_guard_add_update_def)
     apply (simp add: remove_guard_add_update_def)
    apply (simp add: remove_guard_add_update_def)
   apply (simp add: remove_guard_add_update_def)
   apply (simp add: posterior_def Let_def ctx_simp)
   apply (case_tac "consistent (\<lambda>r. and (if r = V (I i) then snd (V (I i), cexp.Eq v) else cexp.Bc True) (c r))")
    apply (simp add: remove_input_constraints_def)
    apply (case_tac "constrains_an_input r")
     apply simp
    apply simp
    apply (case_tac "r = V (R ri)")
     apply simp
    apply (case_tac "r = V (I i)")
     apply simp
    apply simp
   apply simp
  apply (simp add: remove_guard_add_update_def)
  apply (simp add: posterior_def Let_def ctx_simp)
  apply (case_tac "consistent (\<lambda>r. and (if r = V (I i) then snd (V (I i), cexp.Eq v) else cexp.Bc True) (c r))")
   apply simp
   apply (simp add: inconsistent_false)
   apply (simp add: remove_input_constraints_alt)
   defer
   apply simp
   apply (simp add: inconsistent_false)
  apply (simp add: test2)
  apply (simp add: ctx_simp2)
  apply (simp add: consistent_def)
  apply clarify
  apply (rule_tac x=s in exI)
  apply clarify
  by (metis (full_types))

lemma empty_variable_constraints: "\<lbrakk>\<rbrakk> (V (R ri)) = Undef \<and> \<lbrakk>\<rbrakk> (V (I i)) = Bc True"
  by simp

lemma remove_guard_add_update:  "\<lparr>Label=l, Arity=a, Guard=[], Outputs=[], Updates=[(R r, (V (I i)))]\<rparr> = remove_guard_add_update \<lparr>Label=l, Arity=a, Guard=[GExp.Eq (V (I i)) (L s)], Outputs=[], Updates=[]\<rparr> i r"
  by (simp add: remove_guard_add_update_def)

lemma generalise_subsumption_empty: "subsumes \<lbrakk>\<rbrakk> \<lparr>Label=l, Arity=a, Guard=[], Outputs=[], Updates=[(R r, (V (I i)))]\<rparr> 
                  \<lparr>Label=l, Arity=a, Guard=[GExp.Eq (V (I i)) (L s)], Outputs=[], Updates=[]\<rparr>"
  using remove_guard_add_update empty_variable_constraints generalise_subsumption
  by simp

lemma "subsumes \<lbrakk>\<rbrakk> (remove_guard_add_update \<lparr>Label=l, Arity=a, Guard=[GExp.Eq (V (I i)) (L s)], Outputs=[], Updates=[]\<rparr> i r)
                  \<lparr>Label=l, Arity=a, Guard=[GExp.Eq (V (I i)) (L s)], Outputs=[], Updates=[]\<rparr>"
  using remove_guard_add_update empty_variable_constraints generalise_subsumption
  by simp

lemma "\<not> incoming_transition_to t 0 \<Longrightarrow> directly_subsumes t t' 0 \<lparr>Label=l, Arity=a, Guard=[], Outputs=[], Updates=[(R r, (V (I i)))]\<rparr> 
                                                                 \<lparr>Label=l, Arity=a, Guard=[GExp.Eq (V (I i)) (L s)], Outputs=[], Updates=[]\<rparr>"
  apply (simp add: directly_subsumes_def anterior_context_no_return_to_zero)
  apply (simp add: generalise_subsumption_empty)
  using generalise_subsumption_empty
  by blast

lemma posterior_input: "(posterior \<lbrakk>\<rbrakk> aaa) (V(I i)) = Bc False \<Longrightarrow> (posterior \<lbrakk>\<rbrakk> aaa) = (\<lambda>x. Bc False)"
  apply (simp add: posterior_def Let_def)
  apply (case_tac "consistent (medial \<lbrakk>\<rbrakk> (Guard aaa))")
   apply simp
   apply (simp add: remove_input_constraints_def)
  by simp

lemma not_cexp_equiv_gt_false: "\<not>cexp_equiv (cexp.Gt x5) (cexp.Bc False)"
  apply (simp add: cexp_equiv_def gexp_equiv_def)
  by (metis MaybeBoolInt.simps(3) aval.simps(1) cval.simps(5) cval_values)

lemma filter_not_f_a: " \<not> f a \<Longrightarrow> filter f g = filter f (a#g)"
  by simp

lemma and_false_not_undef: "and (cexp.Bc False) c \<noteq> Undef"
  apply (induct_tac c)
        apply simp
       apply (case_tac x)
  by auto

lemma and_And_false: "x \<noteq> cexp.Bc True \<and> x \<noteq> Bc False \<Longrightarrow> and (Bc False) x = And (Bc False) x"
  apply (case_tac x)
  by auto









(*definition context_equiv :: "context \<Rightarrow> context \<Rightarrow> bool" where
  "context_equiv c c' \<equiv> \<forall>s. \<forall>r. (gval (cexp2gexp r (c r)) s = gval (cexp2gexp r (c' r)) s)"*)

lemma context_equiv_symmetry: "context_equiv c c"
  by (simp add: context_equiv_def cexp_equiv_def gexp_equiv_def)

lemma remove_guard_same_labels_arities: "t' = remove_guard_add_update t i ri \<Longrightarrow> Label t = Label t' \<and>
       Arity t = Arity t' \<and>
       length (Outputs t) = length (Outputs t')"
  by (simp add: remove_guard_add_update_def)

lemma test: "cval (medial (\<lambda>r. and (cexp.Bc False) (c r)) G r) ia \<noteq> Some True"
  sorry

lemma "cval (medial c G r) ia = Some True \<Longrightarrow>
       cval (medial c (filter (\<lambda>g. \<forall>a. g \<noteq> gexp.Eq (V (I i)) a \<and> g \<noteq> gexp.Eq a (V (I i))) G) r) ia = Some True"
proof(induct G)
  case Nil
  then show ?case
    by simp
next
  case (Cons a G)
  then show ?case
    apply simp
    apply (case_tac a)
        apply (case_tac x1)
         apply simp
        apply (simp add: test)
       apply simp


qed


lemma "Guard t \<noteq> Guard t' \<Longrightarrow>
       Updates t \<noteq> Updates t' \<Longrightarrow>
       c (V (R ri)) = Undef \<Longrightarrow> 
       c (V (I i)) = Bc True \<Longrightarrow> 
       t' = remove_guard_add_update t i ri \<Longrightarrow>
       subsumes c t' t"
proof-
  assume generalise: "t' = remove_guard_add_update t i ri"
  show ?thesis
    apply (simp add: subsumes_def)
    apply safe
     apply (simp add: remove_guard_add_update_def generalise)
     apply (simp add: remove_guard_add_update_def generalise)
     apply (simp add: remove_guard_add_update_def generalise)
        prefer 2
        apply (simp add: remove_guard_add_update_def generalise)
       prefer 2
       apply (simp add: remove_guard_add_update_def generalise)
       apply (simp add: remove_guard_add_update_def generalise)




end