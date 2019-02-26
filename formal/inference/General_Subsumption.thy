theory General_Subsumption
imports "../Contexts" Trace_Matches
begin

declare One_nat_def [simp del]

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

lemma inconsistent_c_aux: "gval (cexp2gexp r (c r)) sa \<noteq> true \<Longrightarrow>
       (r = V (I i) \<longrightarrow> gval (cexp2gexp (V (I i)) (and (cexp.Eq s) (c (V (I i))))) sa \<noteq> true) \<and>
             (r \<noteq> V (I i) \<longrightarrow> gval (cexp2gexp r (c r)) sa \<noteq> true)"
proof-
  assume premise: "gval (cexp2gexp r (c r)) sa \<noteq> true"
  show ?thesis
    apply (simp only: gval_and)
    apply standard
    using gval_gAnd_True premise apply blast
    by (simp add: premise)
qed

lemma not_undef_gval: "\<forall>r. c r = Undef \<or> gval (cexp2gexp r (c r)) s = true \<Longrightarrow>
         c (V (I i)) \<noteq> Undef \<Longrightarrow> gval (cexp2gexp (V (I i)) (c (V (I i)))) s = true"
  by auto

lemma ctx_simp2: "and (if r = i then snd (i, g) else cexp.Bc True) (c r) = 
       (if r = i then and g (c r) else c r)"
  by auto

lemma gval_and_eq: "gval (cexp2gexp r (c r)) s \<noteq> true \<Longrightarrow> gval (cexp2gexp r (if r = i then and (cexp.Eq v) (c r) else c r)) s \<noteq> true"
  apply simp
  apply (simp only: gval_and gval_gAnd maybe_and_not_true)
  by auto

lemma test5: "gval (cexp2gexp r (if r = VIi then and c1 (c r) else c r)) s = true \<Longrightarrow>
           gval (cexp2gexp r (c r)) s = true"
  apply (case_tac "r = VIi")
   apply simp
   apply (simp only: gval_and gval_gAnd)
  using maybe_and_not_true apply blast
  by simp

lemma "gval (cexp2gexp uu (and a b)) s = maybe_and (gval (cexp2gexp uu a) s) (gval (cexp2gexp uu b) s)"
  by (simp add: gval_and gval_gAnd)

lemma gval_if_split: "(\<forall>r. gval (cexp2gexp r (if r = vIi then and c1 (c r) else c r)) s = true) =
((gval (cexp2gexp (vIi) (and c1 (c (vIi)))) s = true) \<and>
(\<forall>r. gval (cexp2gexp r (c r)) s = true))"
  apply safe
    apply (metis (full_types))
  using test5 apply blast
  by simp

lemma finite_enumerate_inputs_Guard: "finite (\<Union> set (map enumerate_gexp_inputs G))"
  by (simp add: finite_enumerate_gexp_inputs)

lemma finite_enumerate_inputs_Outputs: "finite (\<Union> set (map enumerate_aexp_inputs P))"
  by (simp add: finite_enumerate_aexp_inputs)

lemma finite_enumerate_inputs_Updates: "finite (\<Union> set (map (\<lambda>(_, u). enumerate_aexp_inputs u) U))"
proof(induct U)
  case Nil
  then show ?case by simp
next
  case (Cons a U)
  then show ?case
    by (simp add: finite_enumerate_aexp_inputs split_def)
qed

lemma finite_get_biggest_t_input: "finite ((\<Union> set (map enumerate_gexp_inputs G)) \<union>
                                           (\<Union> set (map enumerate_aexp_inputs (P))) \<union>
                                           (\<Union> set (map (\<lambda>(_, u). enumerate_aexp_inputs u) U)))"
  using finite_enumerate_inputs_Guard finite_enumerate_inputs_Outputs finite_enumerate_inputs_Updates by force

lemma "a \<noteq> {} \<Longrightarrow> b \<noteq> {} \<Longrightarrow> finite a \<Longrightarrow> finite b \<Longrightarrow> Max (a \<union> b) = max (Max a) (Max b)"
  by (simp add: Max.union)

lemma remove_guard_add_update_keeps_elements: "\<Union>set (map enumerate_gexp_inputs (Guard t)) \<union> \<Union>set (map enumerate_aexp_inputs (Outputs t)) \<union>
    \<Union>set (map (\<lambda>(uu, y). enumerate_aexp_inputs y) (Updates t)) \<noteq>
    {} \<Longrightarrow> \<Union>set (map enumerate_gexp_inputs (Guard (remove_guard_add_update t i r))) \<union>
           \<Union>set (map enumerate_aexp_inputs (Outputs (remove_guard_add_update t i r))) \<union>
           \<Union>set (map (\<lambda>(uu, y). enumerate_aexp_inputs y) (Updates (remove_guard_add_update t i r))) \<noteq> {}"
  by (simp add: remove_guard_add_update_def)

lemma finite_regs: "finite (\<Union>x\<in>set (Updates t). case x of (r, uu_) \<Rightarrow> enumerate_aexp_regs (V r))"
  using finite_enumerate_aexp_regs
  by auto

lemma remove_guard_add_update:  "\<lparr>Label=l, Arity=a, Guard=[], Outputs=[], Updates=[(R r, (V (I i)))]\<rparr> = remove_guard_add_update \<lparr>Label=l, Arity=a, Guard=[GExp.Eq (V (I i)) (L s)], Outputs=[], Updates=[]\<rparr> i r"
  by (simp add: remove_guard_add_update_def)

lemma filter_not_f_a: " \<not> f a \<Longrightarrow> filter f g = filter f (a#g)"
  by simp

lemma cval_not: "cval (not x) r s = maybe_not (cval x r s)"
proof(induct x)
case Undef
  then show ?case
    by (simp add: cval_Not)
next
  case (Bc x)
  then show ?case
    apply (case_tac x)
    by (simp add: cval_false cval_true)+
next
  case (Eq x)
  then show ?case
    by (simp add: cval_Not)
next
  case (Lt x)
  then show ?case
    by (simp add: cval_Not)
next
  case (Gt x)
  then show ?case
    by (simp add: cval_Not)
next
  case (Not x)
  then show ?case
    apply (simp add: cval_not cval_Not)
    by (simp add: maybe_double_negation)
next
  case (And x1 x2)
  then show ?case
    by (simp add: cval_Not)
qed

lemma "medial c G ra |\<subseteq>| medial c (filter f G) ra"
proof(induct G)
  case Nil
  then show ?case by simp
next
  case (Cons a G)
  then show ?case
    apply simp
    apply (case_tac "f a")
     apply simp
     apply (simp add: medial_def)
qed

lemma "t' = remove_guard_add_update t i r \<Longrightarrow>
       cval (Contexts.conjoin (medial c (Guard t) ra)) ra ia = true \<Longrightarrow>
       cval (Contexts.conjoin (medial c (Guard (remove_guard_add_update t i r)) ra)) ra ia = true"
  apply (simp add: remove_guard_add_update_def)

lemma "is_generalisation_of t' t e \<Longrightarrow> subsumes c t' t"
  apply (simp add: is_generalisation_of_def subsumes_def)
  apply clarify
  apply safe
          apply (simp add: remove_guard_add_update_preserves_label)
         apply (simp add: remove_guard_add_update_preserves_arity)
        apply (simp add: remove_guard_add_update_preserves_outputs)
       prefer 2
       apply (simp add: remove_guard_add_update_preserves_outputs)
      prefer 2
      apply (simp add: remove_guard_add_update_preserves_outputs)






lemma cval_make_gt_1: "cval (make_gt (and cp cp)) a s = true \<Longrightarrow>
                     cval (make_gt (and (and cp (cexp.Lt x)) (and cp (cexp.Lt x)))) a s = true"
proof(induct cp)
case Undef
  then show ?case
    by simp
next
  case (Bc x)
  then show ?case
    apply (case_tac x)
     apply simp
    by simp
next
  case (Eq x)
  then show ?case
    by simp
next
  case (Lt x)
  then show ?case
    by simp
next
  case (Gt x)
  then show ?case
    apply (case_tac x)
    by auto
next
  case (Not cp)
  then show ?case
    apply (simp del: make_gt.simps)
    apply (simp only: make_gt.simps cval_and cval_true)
    by simp
next
  case (And cp1 cp2)
  then show ?case
    apply (simp del: make_gt.simps)
    apply (simp only: make_gt.simps cval_and cval_true)
    by simp
qed

lemma cval_make_gt_2: "cval (make_gt (c (V v))) a s = true \<Longrightarrow>
       cval (make_gt (and (c (V v)) (cexp.Lt x))) a s = true"
  using and_self cval_make_gt_1 by auto

lemma and_gives_And: "c \<noteq> cexp.Bc True \<Longrightarrow> c' \<noteq> cexp.Bc True \<Longrightarrow> c' \<noteq> c \<Longrightarrow> (and c c') = And c c'"
  apply (induct c c' rule: and.induct)
  by auto

lemma cval_make_gt_and: "cval (make_gt (and c c')) a s = maybe_and (cval (make_gt c) a s) (cval (make_gt c') a s)"
  apply (induct c c' rule: and.induct)
                      apply (simp_all only: and.simps make_gt.simps cval_true maybe_and_zero cval_false)
                      apply (simp_all only: maybe_and_commutative maybe_and_zero)
                      apply simp
                      apply (simp_all only: cexp.distinct bool_simps cval_true if_True if_False cval_and cval_false maybe_and_one make_gt.simps)
                      apply (simp_all only: maybe_and_commutative maybe_and_zero)
       apply (case_tac "cexp.Eq v = cexp.Eq va")
        apply (simp only: bool_simps if_True make_gt.simps)
  using maybe_and_one apply auto[1]
       apply (simp only: bool_simps if_False make_gt.simps)
  using cval_and apply blast
      apply simp
     apply (case_tac "cexp.Lt v = cexp.Lt va")
        apply (simp only: bool_simps if_True make_gt.simps cval_true)
     apply (simp only: bool_simps if_False make_gt.simps cval_and cval_true)
     apply simp
    apply (case_tac "cexp.Gt v = cexp.Gt va")
     apply (simp only: bool_simps if_True make_gt.simps maybe_and_one)
    apply (simp only: bool_simps if_False make_gt.simps cval_and cval_true)
   apply (case_tac "cexp.Not v = cexp.Not va")
    apply (simp only: bool_simps if_True make_gt.simps maybe_and_one cval_not)
  using maybe_and_one apply auto[1]
   apply (simp only: bool_simps if_False make_gt.simps cval_and cval_true)
  apply (case_tac "And v va = And vb vc")
   apply (simp only: bool_simps if_True make_gt.simps maybe_and_one cval_not)
  using cval_and maybe_and_one apply auto[1]
  by (simp only: bool_simps if_False make_gt.simps cval_and cval_true)

lemma cval_make_gt_not: "cval (make_gt (not x)) r s = maybe_not (cval (make_gt x) r s)"
proof(induct x)
case Undef
  then show ?case
    by (simp add: cval_Not)
next
  case (Bc x)
  then show ?case
    apply simp
    by (metis cval_not not.simps(1))
next
  case (Eq x)
  then show ?case
    by (simp add: cval_Not)
next
  case (Lt x)
  then show ?case
    by (simp add: cval_Not cval_false cval_true)
next
  case (Gt x)
  then show ?case
    by (simp add: cval_Not)
next
  case (Not x)
  then show ?case
    by (simp add: cval_Not maybe_double_negation)
next
  case (And x1 x2)
  then show ?case
    apply simp
    by (simp only: cval_And cval_Not cval_and)
qed

lemma get_simp: "V x \<noteq> a2 \<Longrightarrow>
       (Contexts.get (\<lambda>a. if a = V x then and (c a) (make_gt (Contexts.get c a2)) else pairs2context [(a2, make_lt (c (V x)))] c a) a2) =
       (Contexts.get (\<lambda>a. pairs2context [(a2, make_lt (c (V x)))] c a) a2)"
  apply (case_tac a2)
  by auto

lemma and_undef_false: "and Undef (cexp.Bc False) = And Undef (Bc False)"
  by simp

lemma maybe_not_true: "maybe_not c = true = (c = Some False)"
  apply (case_tac c)
  by auto

lemma "(cval (apply_update (medial (medial c g) g) (Contexts.apply_updates (medial (medial c g) g) (medial c g) u) (aa, b1) (V aa)) (V aa) i =
     true \<Longrightarrow>
     Plus b1 b2 = b1 \<Longrightarrow> cval (apply_update (medial c g) (Contexts.apply_updates (medial c g) c u) (aa, b1) (V aa)) (V aa) i = true) \<Longrightarrow>
    (cval (apply_update (medial (medial c g) g) (Contexts.apply_updates (medial (medial c g) g) (medial c g) u) (aa, b2) (V aa)) (V aa) i =
     true \<Longrightarrow>
     Plus b1 b2 = b2 \<Longrightarrow> cval (apply_update (medial c g) (Contexts.apply_updates (medial c g) c u) (aa, b2) (V aa)) (V aa) i = true) \<Longrightarrow>
    (cval (Contexts.apply_updates (medial (medial c g) g) (medial c g) u (V aa)) (V aa) i = true \<Longrightarrow>
     cval (Contexts.apply_updates (medial c g) c u (V aa)) (V aa) i = true) \<Longrightarrow>
    cval (compose_plus (Contexts.get (medial (medial c g) g) b1) (Contexts.get (medial (medial c g) g) b2)) (V aa) i = true \<Longrightarrow>
    cval (compose_plus (Contexts.get (medial c g) b1) (Contexts.get (medial c g) b2)) (V aa) i = true"

lemma "(cval (Contexts.apply_updates (medial (medial c g) g) (medial c g) u r) r i = true \<Longrightarrow>
        cval (Contexts.apply_updates (medial c g) c u r) r i = true) \<Longrightarrow>
       cval (apply_update (medial (medial c g) g) (Contexts.apply_updates (medial (medial c g) g) (medial c g) u) (aa, b) r) r i =
       true \<Longrightarrow>
       a = (aa, b) \<Longrightarrow> cval (apply_update (medial c g) (Contexts.apply_updates (medial c g) c u) (aa, b) r) r i = true"
proof(induct b)
case (L x)
  then show ?case
    by auto
next
  case (V x)
  then show ?case
    apply simp
    using cval_medial_var_update by auto
next
  case (Plus b1 b2)
  then show ?case
    apply simp
    apply (case_tac " r = V aa")
     apply simp
     defer
     apply simp

   
next
  case (Minus b1 b2)
  then show ?case sorry
qed

lemma last: "cval (Contexts.apply_updates (medial (medial c g) g) (medial c g) u r) r i = true \<Longrightarrow>
             cval (Contexts.apply_updates (medial c g) c u r) r i = true"
proof(induct u)
  case Nil
  then show ?case
    by (simp add: cval_medial_true_requires_cval_anterior_true)
next
  case (Cons a u)
  then show ?case
    apply simp
    apply (case_tac a)
    apply simp
    sorry
qed

lemma "subsumes c t t"
  apply (simp add: subsumes_def)
  apply safe
  apply (simp add: posterior_def Let_def)
  apply (case_tac "consistent (medial (medial c G) G)")
   apply (simp add: consistent_medial_requires_consistent_anterior remove_input_constraints_alt)
  apply (case_tac "constrains_an_input r")
    apply simp
   apply simp
   defer
  using CExp.satisfiable_def unsatisfiable_false apply auto[1]
  by (simp add: last)
end