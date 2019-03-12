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

lemma fBall_medial_filter: "fBall (medial c G r) (\<lambda>c. cval c r sa = true) \<Longrightarrow>
       fBall (medial c (filter f G) r) (\<lambda>c. cval c r sa = true)"
  using medial_filter by fastforce

lemma map_snd_filter: "map snd (filter (\<lambda>(a, uu). a = v) (map (\<lambda>(x, y). (x, not |`| y)) l)) =
       map (\<lambda>(x, y). (not |`| y)) (filter (\<lambda>(a, uu). a = v) l)"
proof(induct l)
case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case
    by auto
qed

lemma guard2pairs_no_constraints_on_v: "\<not> gexp_constrains g1 (V v) \<Longrightarrow> list_all (\<lambda>(a, c). a \<noteq> V v) (guard2pairs c g1)"
proof(induct g1)
case (Bc x)
  then show ?case
    apply (case_tac x)
    by auto
next
  case (Eq a1 a2)
  then show ?case
  proof(induct a1)
    case (L x)
    then show ?case
      apply (induct a2)
      by auto
  next
    case (V x)
    then show ?case
      apply (induct a2)
      by auto
  next
    case (Plus a11 a12)
    then show ?case
      apply (induct a2)
      by auto
  next
    case (Minus a11 a12)
    then show ?case
      apply (induct a2)
      by auto
  qed
next
  case (Gt a1 a2)
  then show ?case
  proof(induct a1)
    case (L x)
    then show ?case
      by auto
  next
    case (V x)
    then show ?case
      apply (induct a2)
      by auto
  next
    case (Plus a11 a12)
    then show ?case
      apply (induct a2)
      by auto
  next
    case (Minus a11 a12)
    then show ?case
      apply (induct a2)
      by auto
  qed
next
  case (Null x)
  then show ?case
    by auto
next
case (Nor g11 g12)
  then show ?case
    apply simp
    by (metis (mono_tags, lifting) Ball_set list.pred_map o_apply prod.sel(1) split_def)
qed

lemma pairs2context_no_constraints_on_v: "list_all (\<lambda>(a, c). a \<noteq> V v) l \<Longrightarrow> pairs2context l (V v) = {||}"
proof-
  assume premise: "list_all (\<lambda>(a, c). a \<noteq> V v) l"
  have list_all_empty: "filter (\<lambda>(a, uu). a = V v) l = []"
    using premise
    by (simp add: Ball_set split_def)
  show ?thesis
    by (simp add: pairs2context_def list_all_empty)
qed

lemma pairs2context_no_constraints_on_v_2: "\<not> gexp_constrains g1 (V v) \<Longrightarrow> pairs2context (map (\<lambda>(x, y). (x, not |`| y)) (guard2pairs c g1)) (V v) = {||}"
  using guard2pairs_no_constraints_on_v pairs2context_no_constraints_on_v
  by (metis funion_absorb gexp_constrains.simps(5) guard2pairs.simps(30) map_append pairs2context_append)

lemma updates_remove_guard_add_update: "Updates (remove_guard_add_update t i r) = (R r, V (I i)) # Updates t"
  by (simp add: remove_guard_add_update_def)

lemma generalisation_of_preserves: "is_generalisation_of t' t e i r \<Longrightarrow>
    Label t = Label t' \<and>
    Arity t = Arity t' \<and>
    (Outputs t) = (Outputs t')"
  apply (simp add: is_generalisation_of_def)
  using remove_guard_add_update_preserves by auto

lemma generalisation_medial_subset: "is_generalisation_of t' t e i r \<Longrightarrow> medial c (Guard t') a |\<subseteq>| medial c (Guard t) a"
  apply (simp add: is_generalisation_of_def)
  using medial_general_subset by blast

lemma generalisation_medial_equiv: "is_generalisation_of t' t e i r \<Longrightarrow> medial c (Guard t @ Guard t') = medial c (Guard t)"
  apply (rule ext)
  apply (simp add: is_generalisation_of_def medial_append)
  using medial_general_subset by blast

lemma apply_updates_same: "\<forall>i. c (V (I i)) = {|Bc True|} \<Longrightarrow>
       \<forall>i. \<forall>u\<in>set U. fst u \<noteq> v \<and> fst u \<noteq> I i \<Longrightarrow>
       consistent (medial c (Guard t)) \<Longrightarrow>
       remove_obsolete_constraints (Contexts.apply_updates (medial c (Guard t)) c U) (fst |`| fset_of_list U) (V v) = c (V v)"
proof(induct U)
  case Nil
  then show ?case
    apply (simp add: remove_obsolete_constraints_def)
    by auto
next
  case (Cons u us)
  then show ?case
    apply (cases u)
    apply (simp add: remove_obsolete_constraints_def)
    apply (case_tac v)
     apply simp
    apply simp
    apply clarify
    apply standard
     apply (metis (no_types, lifting) empty_variable_constraints)
    apply (case_tac b)
       apply simp
       apply (smt fBexE)
      apply simp
      apply (smt fBexE)
     apply simp
     apply (smt fBexE)
    apply simp
    by (smt fBexE)
qed

lemma posterior_same: "\<forall>i. c (V (I i)) = {|Bc True|} \<Longrightarrow>
       \<forall>i. \<forall>u\<in>set (Updates t). fst u \<noteq> v \<and> fst u \<noteq> I i \<Longrightarrow>
       consistent (medial c (Guard t)) \<Longrightarrow>
       posterior c t (V v) = c (V v)"
  by (simp add: posterior_def posterior_separate_def apply_updates_same)

lemma is_generalisation_of_consistent_medial: "is_generalisation_of t' t e i r \<Longrightarrow>
    consistent (medial c (Guard t)) \<Longrightarrow> 
    consistent (medial c (Guard t'))"
  by (simp add: is_generalisation_of_def consistent_medial_generalisation)

lemma is_generalisation_of_posterior_subset: "is_generalisation_of t' t e i r \<Longrightarrow> a \<noteq> V (R r) \<Longrightarrow>
       consistent (medial c (Guard t)) \<Longrightarrow>
       posterior c t' a |\<subseteq>| posterior c t a"
  apply (simp add: posterior_def posterior_separate_def)
  apply (simp add: Let_def generalisation_medial_equiv)
   apply (simp add: is_generalisation_of_consistent_medial)
   apply (simp add: is_generalisation_of_def remove_guard_add_update_def)
   apply (simp add: remove_obsolete_constraints_def)
   apply standard
    apply auto[1]
  by (simp add: apply_updates_filter)

lemma aux1: "\<forall>i. \<forall>u\<in>set U. fst u \<noteq> R r \<Longrightarrow> \<not>fBex (fset_of_list U) (\<lambda>x. fst x = R r \<and> R r \<noteq> fst x)"
  by simp

lemma is_generalisation_of_updates_r: "is_generalisation_of t' t e i r \<Longrightarrow>
                     \<not>fBex (fset_of_list (Updates t')) (\<lambda>x. fst x = R r \<and> R r \<noteq> fst x)"
  by (simp add: is_generalisation_of_def)

lemma posterior_Rr_undef: "\<forall>i. c (V (I i)) = {|Bc True|} \<Longrightarrow>
       c (V (R r)) = {|Undef|} \<Longrightarrow>
       \<forall>i. \<forall>u\<in>set (Updates t). fst u \<noteq> R r \<and> fst u \<noteq> I i \<Longrightarrow>
       consistent (medial c (Guard t)) \<Longrightarrow>
       posterior c t (V (R r)) = {|Undef|}"
  by (simp add: posterior_same)

lemma aux2: "is_generalisation_of t' t e i r \<Longrightarrow>
       c (V (R r)) = {|Undef|} \<Longrightarrow>
       \<forall>i. c (V (I i)) = {|Bc True|} \<Longrightarrow>
       \<forall>i. \<forall>u\<in>set (Updates t). fst u \<noteq> R r \<and> fst u \<noteq> I i \<Longrightarrow>
       fBall (Contexts.apply_updates (medial c (Guard t)) c (Updates t') ra) (\<lambda>c. cval c ra ia = true) \<Longrightarrow>
       Contexts.apply_updates (medial c (Guard t)) c (Updates t) ra \<noteq> {|Undef|} \<Longrightarrow>
       x |\<in>| Contexts.apply_updates (medial c (Guard t)) c (Updates t) ra \<Longrightarrow>
       consistent (medial c (Guard t)) \<Longrightarrow> ra \<noteq> V (R r) \<Longrightarrow> \<forall>n. \<not> aexp_constrains ra (V (I n)) \<Longrightarrow> cval x ra ia = true"
proof(induct "Updates t")
case Nil
  then show ?case
    apply (simp add: is_generalisation_of_def remove_guard_add_update_def)
    by auto
next
  case (Cons u us)
  then show ?case
    apply (simp add: is_generalisation_of_def remove_guard_add_update_def)
    by auto
qed

lemma generalised_updates:  "is_generalisation_of t' t e i r \<Longrightarrow> Updates t' = (R r, (V (I i)))#(Updates t)"
  by (simp add: is_generalisation_of_def remove_guard_add_update_def)

lemma aux3: "\<not> gexp_constrains a (V v) \<Longrightarrow> pairs2context (guard2pairs c a) (V v) |\<subseteq>| c (V v)"
proof(induct a)
case (Bc x)
  then show ?case
    apply (case_tac x)
     apply (simp add: pairs2context_def)
    by(simp add: pairs2context_def)
next
  case (Eq a1 a2)
  then show ?case
  proof(induct a1)
    case (L x)
    then show ?case
      apply (induct a2)
      using pairs2context_def
      by auto
  next
    case (V x)
    then show ?case
      apply (induct a2)
      using pairs2context_def
      by auto
  next
    case (Plus a11 a12)
    then show ?case
      apply (induct a2)
      using pairs2context_def
      by auto
  next
    case (Minus a11 a12)
    then show ?case
      apply (induct a2)
      using pairs2context_def
      by auto
  qed
next
  case (Gt a1 a2)
  then show ?case
  proof(induct a1)
    case (L x)
    then show ?case
      apply (induct a2)
      using pairs2context_def
      by auto
  next
    case (V x)
    then show ?case
      apply (induct a2)
      using pairs2context_def
      by auto
  next
    case (Plus a11 a12)
    then show ?case 
      apply (induct a2)
      using pairs2context_def
      by auto
  next
    case (Minus a11 a12)
    then show ?case 
      apply (induct a2)
      using pairs2context_def
      by auto
  qed
next
  case (Nor a1 a2)
  then show ?case
    apply (simp add: pairs2context_append)
    apply standard
     apply (simp add: pairs2context_no_constraints_on_v_2)
    by (simp add: pairs2context_no_constraints_on_v_2)
next
  case (Null x)
  then show ?case
    apply (simp add: pairs2context_def)
    by auto
qed

lemma medial_filter_constraints: "medial c (filter (\<lambda>g. \<not> gexp_constrains g (V (I i))) G) (V (I i)) = c (V (I i))"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: medial_def pairs2context_def List.maps_def)
next
  case (Cons a G)
  then show ?case
    apply (simp add: medial_def List.maps_simps pairs2context_append)
    apply standard
    apply standard
     prefer 2
     apply blast
    apply simp
    apply standard
    defer
     apply auto[1]
    by (simp add: aux3)
qed

lemma generealisation_medial: "is_generalisation_of t' t e i r \<Longrightarrow>
       medial c (Guard t') (V (I i)) = c (V (I i))"
  apply (simp add: is_generalisation_of_def remove_guard_add_update_def)
  apply clarify
  by (simp add: medial_filter_constraints)

lemma generalisation_posterior_consistent: "is_generalisation_of t' t e i r \<Longrightarrow>
       c (V (R r)) = {|Undef|} \<Longrightarrow>
       \<forall>i. c (V (I i)) = {|Bc True|} \<Longrightarrow>
       \<forall>i. \<forall>u\<in>set (Updates t). fst u \<noteq> R r \<and> fst u \<noteq> I i \<Longrightarrow>
       consistent (medial c (Guard t)) \<Longrightarrow>
       fBall (posterior c t a) (\<lambda>c. cval c a s = true) \<Longrightarrow>
       fBall (posterior c t' a) (\<lambda>c. cval c a s = true)"
  apply (case_tac "a \<noteq> V (R r)")
  using is_generalisation_of_posterior_subset apply blast
  apply (simp add: posterior_def posterior_separate_def Let_def is_generalisation_of_consistent_medial)
  apply (simp add: generalised_updates remove_obsolete_constraints_def)
  apply (case_tac "fBex (fset_of_list (Updates t)) (\<lambda>x. fst x = R r \<and> R r \<noteq> fst x)")
   apply auto[1]
  apply simp
  apply standard
   apply auto[1]
  apply clarify
  by (simp add: generealisation_medial cval_true)


lemma is_generalisation_of_subsumes_original: "is_generalisation_of t' t e i r \<Longrightarrow>
       c (V (R r)) = {|Undef|} \<Longrightarrow>
       \<forall>i. c (V (I i)) = {|Bc True|} \<Longrightarrow>
       \<forall>u \<in> set (Updates t). fst u \<noteq> (R r) \<Longrightarrow>
       \<forall>i. \<forall>u \<in> set (Updates t). fst u \<noteq> (R r) \<and> fst u \<noteq> (I i) \<Longrightarrow>
       t' \<^sub>c\<sqsupseteq> t"
  apply (simp add: subsumes_def generalisation_of_preserves)
  apply standard
  using generalisation_medial_subset apply blast
  apply standard
   apply clarify
   apply (case_tac "consistent (medial c (Guard t))")
    prefer 2
    apply (simp add: posterior_def posterior_separate_def Let_def generalisation_medial_equiv)

   apply (case_tac "ra = V (R r)")
    apply clarify
    apply (simp add: posterior_Rr_undef)
   apply (simp add: posterior_separate_def posterior_def Let_def generalisation_medial_equiv)
   apply (simp add: remove_obsolete_constraints_def)
   apply (case_tac "(\<exists>n. aexp_constrains ra (V (I n)))")
    apply auto[1]
   apply (case_tac "fBex (fset_of_list (Updates t')) (\<lambda>x. V (fst x) = ra \<and> ra \<noteq> V (fst x))")
    apply auto[1]
   apply (case_tac "fBex (fset_of_list (Updates t)) (\<lambda>x. V (fst x) = ra \<and> ra \<noteq> V (fst x))")
    apply auto[1]
   apply simp
  using aux2

   apply simp
  apply (simp only: consistent_def)
  apply clarify
  apply (rule_tac x=s in exI)

  apply (case_tac "consistent (medial c (Guard t))")
  apply (simp add: generalisation_posterior_consistent)

  apply (simp add: posterior_def posterior_separate_def Let_def)
  apply clarify
  by (simp add: cval_false)

lemma restrict_value_of_register: "c (V (R r)) = {|cexp.Eq v|} \<Longrightarrow>
       consistent (\<lambda>x. datastate2context ra x |\<union>| c x) \<Longrightarrow>
       ra (R r) = Some v"
proof-
  assume premise1: "c (V (R r)) = {|cexp.Eq v|}"
  assume premise2: "consistent (\<lambda>x. datastate2context ra x |\<union>| c x)"
  have contra: "\<And>c r v ra. c (V (R r)) = {|cexp.Eq v|} \<Longrightarrow>
       ra (R r) \<noteq> Some v \<Longrightarrow>
       \<not> consistent (\<lambda>x. datastate2context ra x |\<union>| c x)"
  apply (simp add: datastate2context_def consistent_def)
  apply clarify
  apply (rule_tac x="V (R r)" in exI)
  apply simp
  apply (simp add: cval_def gval.simps ValueEq_def)
  apply (case_tac "ra (R r)")
   apply (simp add: gval.simps ValueEq_def)
    by (simp add: gval.simps ValueEq_def)
  show ?thesis
    using contra premise1 premise2
    by auto
qed

lemma length_apply_generalised_outputs: "length (apply_outputs (Outputs t)                         (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. ra (R n)))) =
                                         length (apply_outputs (Outputs (generalise_output t p r)) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. ra (R n))))"
  by (simp add: apply_outputs_alt generalise_output_preserves_output_length)

lemma apply_outputs_equiv: "i < length (Outputs t) \<Longrightarrow>
       i \<noteq> r \<Longrightarrow>
       (apply_outputs (Outputs t) s) ! i = (apply_outputs (Outputs (generalise_output t p r)) s) ! i"
  apply (simp add: generalise_output_def)
  by (simp add: apply_outputs_alt)

lemma generalise_output_subsumes_original: "nth (Outputs t) r = L v \<Longrightarrow>
       c (V (R p)) = {|Eq v|} \<Longrightarrow>
       (generalise_output t p r) \<^sub>c\<sqsupseteq> t"
  apply (simp add: subsumes_def generalise_output_preserves)
  apply standard
   apply (simp add: satisfies_context_def)
   apply clarify
   apply (simp add: list_eq_iff_nth_eq length_apply_generalised_outputs )
   apply clarify
   apply (simp only: apply_outputs_preserves_length)
   apply (case_tac "ia = r")
    prefer 2
    apply (simp add: apply_outputs_equiv)
   apply (simp add: apply_outputs_alt generalise_output_def)
   apply (simp add: restrict_value_of_register)
  apply standard
   apply (simp add: list_eq_iff_nth_eq length_apply_generalised_outputs apply_outputs_alt generalise_output_def)
   apply (rule_tac x=i in exI)
   apply (rule_tac x="<R p := v>" in exI)
   apply (rule allI)
   apply (case_tac "ia = r")
    apply simp
   apply simp
  apply standard
  apply (rule allI)+
   apply (simp add: posterior_separate_append_self posterior_def generalise_output_preserves)
  by (simp add: posterior_def posterior_separate_def  generalise_output_preserves)

end