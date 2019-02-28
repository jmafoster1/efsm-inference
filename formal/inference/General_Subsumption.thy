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

lemma and_gives_And: "c \<noteq> cexp.Bc True \<Longrightarrow> c' \<noteq> cexp.Bc True \<Longrightarrow> c' \<noteq> c \<Longrightarrow> (and c c') = And c c'"
  apply (induct c c' rule: and.induct)
  by auto

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

lemma medial_filter: "medial c (filter f G) ra |\<subseteq>| medial c G ra"
proof(induct G)
  case Nil
  then show ?case by simp
next
  have aux1: "\<forall>a f G ra c. medial c (a # filter f G) ra = medial c [a] ra |\<union>| medial c (filter f G) ra"
    using medial_cons by blast
  case (Cons a G)
  then show ?case
    apply simp
    apply (case_tac "f a")
     apply simp
     defer
    apply simp
    using medial_cons_subset apply blast
    apply (simp only: aux1)
  proof -
    assume "medial c (filter f G) ra |\<subseteq>| medial c G ra"
    then have "medial c (a # G) ra = medial c [a] ra |\<union>| (medial c G ra |\<union>| medial c (filter f G) ra |\<union>| medial c (filter f G) ra)"
      using medial_cons by blast
    then show "medial c [a] ra |\<union>| medial c (filter f G) ra |\<subseteq>| medial c (a # G) ra"
      by blast
  qed
qed

lemma medial_general_subset: "medial c (Guard (remove_guard_add_update t i r)) ra |\<subseteq>| medial c (Guard t) ra"
  by (simp add: remove_guard_add_update_def medial_filter)

lemma consistent_medial_generalisation: "consistent (medial c (Guard t)) \<Longrightarrow> consistent (medial c (Guard (remove_guard_add_update t i r)))"
  apply (simp add: consistent_def)
  using medial_general_subset
  by blast

lemma "fBall (medial (medial c G) (filter f G) r) (\<lambda>c. cval c r s = true) \<Longrightarrow> fBall (medial c G r) (\<lambda>c. cval c r s = true)"
  using anterior_subset_medial by blast

lemma get_medial_filter: "Contexts.get (medial c (filter f G)) x31 |\<subseteq>| Contexts.get (medial c G) x31"
  apply (case_tac x31)
     apply simp
    apply (simp add: medial_filter)
   apply (simp add: le_supI2 medial_filter sup.coboundedI1)
  by (simp add: medial_filter)

lemma fprod_get_medial_filter: "(a, b) |\<in>| Contexts.get (medial c (filter f G)) r |\<times>| Contexts.get (medial c (filter f G)) x32 \<Longrightarrow>
                                (a, b) |\<in>| Contexts.get (medial c G) r |\<times>| Contexts.get (medial c G) x32"
  using get_medial_filter
  by (meson fin_mono fprod_subset)

lemma apply_updates_filter: "Contexts.apply_updates (medial c (filter f G)) c U ra |\<subseteq>| Contexts.apply_updates (medial c G) c U ra"
proof(induct U)
  case Nil
  then show ?case
    by simp
next
  case (Cons a U)
  then show ?case
    apply (cases a)
    apply (case_tac b)
       apply simp
      apply (simp add: medial_filter)
     apply simp
     apply clarify
     apply simp
    using fprod_get_medial_filter fimage_fprod apply metis
     apply simp
     apply clarify
     apply simp
    using fprod_get_medial_filter fimage_fprod by metis
qed

lemma "fBall (if constrains_an_input ra then {|cexp.Bc True|} else Contexts.apply_updates (medial c (Guard t)) c (Updates t) ra)
             (\<lambda>c. cval c ra s = true) \<Longrightarrow>
    (ra = V (R r) \<longrightarrow>
              fBall (medial c (filter (\<lambda>g. \<forall>a. g \<noteq> gexp.Eq (V (I i)) a \<and> g \<noteq> gexp.Eq a (V (I i))) (Guard t)) (V (I i)))
               (\<lambda>c. cval c (V (R r)) s = true)) \<and>
             (ra \<noteq> V (R r) \<longrightarrow>
              (constrains_an_input ra \<longrightarrow> cval (cexp.Bc True) ra s = true) \<and>
              (\<not> constrains_an_input ra \<longrightarrow>
               fBall
                (Contexts.apply_updates (medial c (filter (\<lambda>g. \<forall>a. g \<noteq> gexp.Eq (V (I i)) a \<and> g \<noteq> gexp.Eq a (V (I i))) (Guard t))) c
                  (Updates t) ra)
                (\<lambda>c. cval c ra s = true)))"
  apply (case_tac "ra = V (R r)")
   apply simp
   defer
   apply simp
   apply (case_tac "constrains_an_input ra")
    apply simp
   apply simp
  using apply_updates_filter apply blast
  oops

lemma "consistent (posterior c t) \<Longrightarrow> consistent (posterior c (remove_guard_add_update t i r))"
  apply (simp add: posterior_def Let_def)
  apply (case_tac "consistent (medial c (Guard t))")
   defer
   apply (simp add: inconsistent_false)
  apply (simp add: consistent_medial_generalisation)
  apply (simp add: remove_input_constraints_alt remove_guard_add_update_def)
  apply (simp add: consistent_def)
  oops
(*Stick the consistent part in here and carry it on up to all of the oops-ed lemmas*)


lemma "c (V (I i)) = {|Bc True|} \<Longrightarrow> c (V (R r)) = {|Undef|} \<Longrightarrow> subsumes c (remove_guard_add_update t i r) t"
  unfolding subsumes_def
  apply (simp add: remove_guard_add_update_preserves)
  apply standard
  using medial_general_subset apply blast
  apply standard
    apply (simp add: posterior_def Let_def)
    apply (case_tac "consistent (medial (medial c (Guard t)) (Guard (remove_guard_add_update t i r)))")
     apply (simp add: consistent_medial_gives_consistent_anterior remove_input_constraints_alt)
     apply (case_tac "constrains_an_input ra")
      apply simp
     apply simp
     apply (simp add: remove_guard_add_update_def)
     apply (case_tac "ra = V (R r)")
      apply simp
      apply clarify
      apply simp
end