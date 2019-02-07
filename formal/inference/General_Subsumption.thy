theory General_Subsumption
imports "../Contexts" Trace_Matches
begin

lemma ctx_simp: "(\<lambda>r. and (if r = V (I i) then snd (V (I i), cexp.Eq s) else cexp.Bc True) (\<lbrakk>\<rbrakk> r)) = \<lbrakk>V (I i) \<mapsto> Eq s\<rbrakk>"
  apply (rule ext)
  by simp

lemma generalise_subsumption: "subsumes \<lbrakk>\<rbrakk> \<lparr>Label=l, Arity=a, Guard=[], Outputs=[], Updates=[(R r, (V (I i)))]\<rparr> 
                  \<lparr>Label=l, Arity=a, Guard=[GExp.Eq (V (I i)) (L s)], Outputs=[], Updates=[]\<rparr>"
  apply (simp add: subsumes_def)
  apply standard
   apply clarify
   apply (case_tac "cval (\<lbrakk>\<rbrakk> r) ia")
    apply simp
   apply simp

  apply standard
   apply clarify
   apply (simp add: posterior_def Let_def ctx_simp)
   apply (case_tac "consistent \<lbrakk>V (I i) \<mapsto> cexp.Eq s\<rbrakk>")
    apply (simp add: remove_input_constraints_def)
    apply (case_tac "constrains_an_input ra")
     apply simp
    apply simp
    apply (case_tac "ra = V (R r)")
     apply simp
    apply (case_tac "ra = V (I i)")
     apply simp
    apply simp
   apply simp
   apply (simp add: posterior_def Let_def ctx_simp)
  apply standard
   apply (simp add: consistent_def remove_input_constraints_def consistent_empty_4)
  by (simp add: inconsistent_false)

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


lemma "\<not> incoming_transition_to t 0 \<Longrightarrow> directly_subsumes t t' 0 \<lparr>Label=l, Arity=a, Guard=[], Outputs=[], Updates=[(R r, (V (I i)))]\<rparr> 
                  \<lparr>Label=l, Arity=a, Guard=[GExp.Eq (V (I i)) (L s)], Outputs=[], Updates=[]\<rparr>"
  apply (simp add: directly_subsumes_def anterior_context_no_return_to_zero)
  apply (simp add: generalise_subsumption)
  using generalise_subsumption
  by blast

lemma "subsumes \<lbrakk>\<rbrakk> (remove_guard_add_update \<lparr>Label=l, Arity=a, Guard=[GExp.Eq (V (I i)) (L s)], Outputs=[], Updates=[]\<rparr> i r)
                  \<lparr>Label=l, Arity=a, Guard=[GExp.Eq (V (I i)) (L s)], Outputs=[], Updates=[]\<rparr>"
  apply (simp add: subsumes_def)
  apply safe
          apply (simp add: remove_guard_add_update_def)
         apply (simp add: remove_guard_add_update_def)
        apply (simp add: remove_guard_add_update_def)
       apply (simp add: remove_guard_add_update_def)
      apply (case_tac "cval (\<lbrakk>\<rbrakk> ra) ia")
       apply simp
      apply (simp add: remove_guard_add_update_def)
     apply (simp add: remove_guard_add_update_def)
    apply (simp add: remove_guard_add_update_def)
   apply (simp add: remove_guard_add_update_def)
   apply (simp add: posterior_def Let_def ctx_simp)
   apply (case_tac "consistent \<lbrakk>V (I i) \<mapsto> cexp.Eq s\<rbrakk>")
    apply (simp add: remove_input_constraints_def)
    apply (case_tac "constrains_an_input ra")
     apply simp
    apply simp
    apply (case_tac "ra = V (R r)")
     apply simp
    apply (case_tac "ra = V (I i)")
     apply simp
    apply simp
   apply simp
  apply (simp add: remove_guard_add_update_def)
  apply (simp add: posterior_def Let_def ctx_simp)
  apply (case_tac "consistent \<lbrakk>V (I i) \<mapsto> cexp.Eq s\<rbrakk>")
   apply (simp add: remove_input_constraints_def consistent_def)
   apply auto[1]
  by (simp add: inconsistent_false)

lemma inconsistent_c: "\<not>consistent c \<Longrightarrow> \<not>consistent (\<lambda>r. and (if r = V (I i) then snd (V (I i), cexp.Eq s) else cexp.Bc True) (c r))"
proof-
  assume premise: "\<not> consistent c"
  have aux1:  "\<And>c r sa i s. c r \<noteq> Undef \<and> gval (cexp2gexp r (c r)) sa \<noteq> Some True \<Longrightarrow>
       (r = V (I i) \<longrightarrow>
               and (cexp.Eq s) (c (V (I i))) \<noteq> Undef \<and> gval (cexp2gexp (V (I i)) (and (cexp.Eq s) (c (V (I i))))) sa \<noteq> Some True) \<and>
              (r \<noteq> V (I i) \<longrightarrow> c r \<noteq> Undef \<and> gval (cexp2gexp r (c r)) sa \<noteq> Some True)"
  apply simp
  apply clarify
  apply (case_tac " c (V (I i))")
        apply simp
       apply simp
      apply simp
     apply simp
     apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (sa (I i))")
      apply simp
     apply simp
    apply simp
    apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (sa (I i)) (Some x5)")
     apply simp
    apply simp
   apply simp
   apply (case_tac "gval (cexp2gexp (V (I i)) x6) sa")
    apply simp
   apply simp
  apply simp
  apply (case_tac "gval (cexp2gexp (V (I i)) x71) sa")
   apply simp
  apply simp
  apply (case_tac "gval (cexp2gexp (V (I i)) x72) sa")
   apply simp
    by simp
  show ?thesis
    using premise
    apply (simp add: consistent_def)
    apply clarify
    using aux1
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

lemma "c (V (R ri)) = Undef \<Longrightarrow> 
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

lemma posterior_input: "(posterior \<lbrakk>\<rbrakk> aaa) (V(I i)) = Bc False \<Longrightarrow> (posterior \<lbrakk>\<rbrakk> aaa) = (\<lambda>x. Bc False)"
  apply (simp add: posterior_def Let_def)
  apply (case_tac "consistent (medial \<lbrakk>\<rbrakk> (Guard aaa))")
   apply simp
   apply (simp add: remove_input_constraints_def)
  by simp

lemma gval_and_false: "gval (cexp2gexp r (and (cexp.Bc False) c)) s \<noteq> Some True"
  apply (case_tac c)
        apply simp
       apply (case_tac x2)
        apply simp+
     apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval r s)")
      apply simp+
    apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x5)")
     apply simp+
   apply (case_tac "gval (cexp2gexp r x6) s")
    apply simp+
  apply (case_tac "gval (cexp2gexp r x71) s")
   apply simp+
  apply (case_tac "gval (cexp2gexp r x72) s")
  by auto

lemma context_equiv_conjoin_false: "context_equiv (Contexts.conjoin (\<lambda>r. cexp.Bc False) c) (\<lambda>r. cexp.Bc False)"
  apply (simp add: context_equiv_def cexp_equiv_def)
  apply clarify
  apply standard
   apply clarify
  sorry

declare conjoin.simps [simp del]

lemma context_equiv_false_medial: "\<And>c. context_equiv c (\<lambda>x. Bc False) \<Longrightarrow> context_equiv (medial c g) (\<lambda>x. Bc False)"
proof(induct g)
  case Nil
  then show ?case
    by simp
next
  case (Cons a g)
  then show ?case
    apply (case_tac a)
        apply (case_tac x1)
         apply (simp add: conjoin.simps)
        apply simp
        apply (simp add: context_equiv_conjoin_false)
    sorry

qed
declare conjoin.simps [simp]

lemma not_cexp_equiv_lt_false: "\<not>cexp_equiv (cexp.Lt s) (cexp.Bc False)"
  apply (case_tac s)
  apply (simp add: cexp_equiv_def)
  apply (metis MaybeBoolInt.simps(1) MaybeBoolInt.simps(3) lt_ex option.inject)
  by (simp add: cexp_equiv_def)

lemma not_cexp_equiv_gt_false: "\<not>cexp_equiv (cexp.Gt x5) (cexp.Bc False)"
  apply (case_tac x5)
  apply (simp add: cexp_equiv_def)
   apply (metis MaybeBoolInt.simps(3) option.simps(3))
  by (simp add: cexp_equiv_def)

lemma maybe_double_negation: "maybe_not (maybe_not x) = x"
  by (simp add: option.case_eq_if)

lemma maybe_negate: "(\<forall>i. maybe_not (cval x i) = Some False) = (\<forall>i. (cval x i) = Some True)"
proof(induct x)
  case Undef
  then show ?case
    by simp
next
  case (Bc x)
  then show ?case
    apply (case_tac x)
    by auto
next
  case (Eq x)
  then show ?case
    by simp
next
  case (Lt x)
  then show ?case
    apply simp
    by (metis MaybeBoolInt.simps(3) option.case_eq_if option.simps(3))
next
  case (Gt x)
  then show ?case
    apply simp
    by (metis MaybeBoolInt.simps(3) option.case_eq_if option.simps(3))
next
  case (Not x)
  then show ?case
    apply (simp add: maybe_double_negation)
    by (metis cval.simps(2) cval.simps(6) cval_double_negation false_not_true)
next
  case (And x1 x2)
  then show ?case
    apply safe
           apply simp+
         apply (case_tac "cval x2 ib")
          apply (metis option.case_eq_if option.distinct(1))
         apply simp
         apply (metis option.inject option.simps(5))
        apply simp+
       apply (case_tac "cval x1 ib")
        apply simp
        apply (metis option.distinct(1) option.simps(4))
       apply simp
       apply (metis (no_types, lifting) cval.simps(2) option.case_eq_if option.sel true_or_none_not_false)
      apply simp+
     apply (case_tac "cval x1 id")
      apply simp
      apply (metis option.case_eq_if option.simps(3))
     apply simp
     apply (case_tac "cval x2 id")
      apply simp
      apply (metis (no_types, lifting) option.case_eq_if option.simps(3))
     apply simp
     apply (smt is_none_code(2) option.simps(4) option.split_sel_asm true_or_none_not_false)
    by simp
qed

lemma maybe_not_values: "(maybe_not c \<noteq> Some False) = (maybe_not c = Some True \<or> maybe_not c = None)"
  by auto

lemma maybe_not_c: "(maybe_not c \<noteq> Some False) = (c = None \<or> c = Some False)"
  using maybe_not_values option.collapse by force

lemma cval_values: "(cval x i \<noteq> Some False) = (cval x i = Some True \<or> cval x i = None)"
  by auto

lemma remove_maybe_not: "(maybe_not (cval x6 i) \<noteq> Some False) = (cval x6 i \<noteq> Some True)"
  using cval_values maybe_not_c by auto

lemma x_nec_not_x: "x \<noteq> cexp.Not x"
  apply (induct_tac x)
  by auto

fun "and2" :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "and2 (Bc True) x = x" |
  "and2 x (Bc True) = x" |
  "and2 Undef Undef = Undef" |
  "and2 Undef c' = And Undef c'" |
  "and2 c Undef = And c Undef" |
  "and2 (Bc False) x = x" |
  "and2 x (Bc False) = x" |
  "and2 c c' = (if c = c' then c else And c c')"

lemma "cexp_equiv (and2 x y) (And x y)"
proof(induct x)
case Undef
  then show ?case
    apply (induct_tac y)
          apply simp
    unfolding cexp_equiv_def
next
  case (Bc x)
  then show ?case sorry
next
  case (Eq x)
then show ?case sorry
next
  case (Lt x)
  then show ?case sorry
next
  case (Gt x)
  then show ?case sorry
next
  case (Not x)
  then show ?case sorry
next
  case (And x1 x2)
  then show ?case sorry
qed

lemma "\<not>consistent (medial (\<lambda>x. cexp.Bc False) g)"
  apply (simp add: consistent_def)
  apply clarify
  apply (rule_tac x=x in exI)
  apply standard
  using context_equiv_false_medial context_equiv_reflexive context_equiv_undef apply blast
  

lemma "posterior (\<lambda>x. cexp.Bc False) aaa = (\<lambda>x. Bc False)"
  apply (simp add: posterior_def Let_def)

lemma "\<forall>s r. posterior_sequence (\<lambda>x. cexp.Bc False) e s r t = (\<lambda>x. Bc False)"
proof(induct t)
  case Nil
  then show ?case
    by simp
next
  case (Cons a t)
  then show ?case
    apply clarify
    apply simp
    apply (case_tac "step e s r (fst a) (snd a)")
     apply simp
    apply simp
    apply (case_tac aa)
    apply simp


qed

lemma "(anterior_context e t) (V(I i)) \<noteq> Bc True \<Longrightarrow> (anterior_context e t) (V(I i)) = Bc False"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: anterior_context_def)
next
  case (Cons a t)
  then show ?case
    apply (simp add: anterior_context_def)
    apply (case_tac "step e 0 Map.empty (fst a) (snd a)")
     apply simp
    apply simp
    apply (case_tac aa)
    apply clarify
    apply simp
    apply (case_tac "(posterior \<lbrakk>\<rbrakk> aaa) = (\<lambda>x. Bc False)")
     apply simp

qed

lemma "accepts_trace e t \<Longrightarrow> (anterior_context e t) (V(I i)) = Bc True"
proof(induct t)
case Nil
  then show ?case
    by (simp add: anterior_context_def)
next
  case (Cons a t)
  then show ?case
    apply (simp add: anterior_context_def)
    apply (case_tac "step e 0 Map.empty (fst a) (snd a)")
     apply simp
    apply simp
    apply (case_tac aa)
    apply clarify
    apply simp

qed

end