theory General_Subsumption
imports "../Contexts" Trace_Matches
begin

declare gval.simps [simp del]

lemma gval_True: "gval (cexp2gexp a (cexp.Bc True)) x = Some True"
  by (simp add: gval.simps)

lemma maybe_and_None: "maybe_and None x = None"
  by simp


lemma maybe_and_is_true: "(maybe_and x y = Some True) = (x = Some True \<and> y = Some True)"
  apply simp
  apply (case_tac x)
   apply simp+
  apply (case_tac y)
  by auto

lemma maybe_and_commutative: "maybe_and x y = maybe_and y x"
  apply simp
  apply (case_tac x)
   apply simp
   apply (case_tac y)
    apply simp+
  apply (case_tac y)
  by auto

lemma maybe_and_true: "maybe_and (Some True) x = x"
  apply (case_tac x)
  by auto

lemma maybe_and_one: "maybe_and x x = x"
  apply (case_tac x)
  by auto

lemma gval_and: "gval (cexp2gexp a (and c1 c2)) = gval (gAnd (cexp2gexp a c1) (cexp2gexp a c2))"
  apply (rule ext)
  apply (case_tac "c1 = Bc True")
   apply (simp only: and.simps gval_gAnd gval_True maybe_and_true)
  apply (case_tac "c2 = Bc True")
   apply (simp only: and.simps gval_gAnd gval_True maybe_and_true maybe_and_commutative)
   apply simp
  apply (case_tac "c1 = c2")
   apply (simp only: and.simps gval_gAnd maybe_and_one)
   apply (metis and_is_And and_true cexp_equiv_def cexp_equiv_redundant_and cval_def)
  by (metis and_is_And cval_def gval_And)

lemma maybe_and_not_true: "(maybe_and x y \<noteq> Some True) = (x \<noteq> Some True \<or> y \<noteq> Some True)"
  apply simp
  apply (case_tac x)
   apply simp+
  apply (case_tac y)
  by auto

lemma gval_and_cexp: "gval (cexp2gexp i c1) s \<noteq> Some True \<Longrightarrow>  gval (cexp2gexp i (and c2 c1)) s \<noteq> Some True"
  apply (simp only: gval_and gval_gAnd maybe_and_not_true)
  by simp

lemma remove_guard_same_labels_arities: "t' = remove_guard_add_update t i ri \<Longrightarrow> Label t = Label t' \<and>
       Arity t = Arity t' \<and>
       length (Outputs t) = length (Outputs t')"
  by (simp add: remove_guard_add_update_def)

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
  show ?thesis
    apply (simp only: gval_and)
    apply standard
    using gval_gAnd_True premise apply blast
    by (simp add: premise)
qed

lemma inconsistent_c: "\<not>consistent c \<Longrightarrow> \<not>consistent (\<lambda>r. and (if r = V (I i) then snd (V (I i), cexp.Eq s) else cexp.Bc True) (c r))"
proof-
  assume premise: "\<not> consistent c"
  show ?thesis
    using premise
    apply (simp add: consistent_def)
    unfolding cval_def
    apply (simp only: gval_And gval_gAnd maybe_and_is_true)
    by metis
qed

lemma not_undef_gval: "\<forall>r. c r = Undef \<or> gval (cexp2gexp r (c r)) s = Some True \<Longrightarrow>
         c (V (I i)) \<noteq> Undef \<Longrightarrow> gval (cexp2gexp (V (I i)) (c (V (I i)))) s = Some True"
  by auto

lemma ctx_simp2: "and (if r = i then snd (i, g) else cexp.Bc True) (c r) = 
       (if r = i then and g (c r) else c r)"
  by auto

lemma test2: "consistent (\<lambda>r. and (if r = V (I i) then snd (V (I i), cexp.Eq s) else cexp.Bc True) (c r)) \<Longrightarrow> consistent c"
  using inconsistent_c
  by auto

lemma gval_conjoin: "gval (cexp2gexp r (c r)) s \<noteq> Some True \<Longrightarrow> gval (cexp2gexp r (if r = i then and (cexp.Eq v) (c r) else c r)) s \<noteq> Some True"
  apply simp
  apply (simp only: gval_and gval_gAnd maybe_and_not_true)
  by auto

lemma test5: "gval (cexp2gexp r (if r = VIi then and c1 (c r) else c r)) s = Some True \<Longrightarrow>
           gval (cexp2gexp r (c r)) s = Some True"
  apply (case_tac "r = VIi")
   apply simp
   apply (simp only: gval_and gval_gAnd)
  using maybe_and_not_true apply blast
  by simp

lemma constrains_an_input_true: "constrains_an_input r \<Longrightarrow> gval (cexp2gexp r (\<lbrakk>\<rbrakk> r)) ia = Some True"
proof(induct r)
  case (L x)
  then show ?case by simp
next
  case (V x)
  then show ?case
    apply (case_tac x)
    using gval.simps
    by auto
next
  case (Plus r1 r2)
  then show ?case
    using gval.simps
    by simp
next
  case (Minus r1 r2)
  then show ?case
    using gval.simps
    by simp
qed

lemma "gval (cexp2gexp uu (and a b)) s = maybe_and (gval (cexp2gexp uu a) s) (gval (cexp2gexp uu b) s)"
  by (simp add: gval_and)

lemma gval_and_false: "gval (cexp2gexp uu (and x (cexp.Bc False))) s \<noteq> Some True"
  apply (simp only: gval_and gval_gAnd)
  by (metis and.simps(17) gval_and_false maybe_and_not_true)

lemma consistent_i_and: "consistent (\<lambda>r. if r = i then and x (c r) else c r) \<Longrightarrow> consistent c"
proof-
  assume premise: "consistent (\<lambda>r. if r = i then and x (c r) else c r)"
  have aux: "\<And>r i c s x. gval (cexp2gexp r (if r = i then and x (c r) else c r)) s = Some True \<Longrightarrow> gval (cexp2gexp r (c r)) s = Some True"
    apply (case_tac "r \<noteq> i")
     apply simp+
    apply (simp only: gval_and gval_gAnd)
    using maybe_and_not_true by blast
  show ?thesis
    using premise
    apply (simp add: consistent_def cval_def)
    apply clarify
    apply (rule_tac x=s in exI)
    apply clarify
    using aux
    by blast
qed

lemma gval_if_split: "(\<forall>r. gval (cexp2gexp r (if r = vIi then and c1 (c r) else c r)) s = Some True) =
((gval (cexp2gexp (vIi) (and c1 (c (vIi)))) s = Some True) \<and>
(\<forall>r. gval (cexp2gexp r (c r)) s = Some True))"
  apply safe
    apply (metis (full_types))
  using test5 apply blast
  by simp

lemma inconsistent_anterior_gives_inconsistent_medial: "\<not>consistent c \<Longrightarrow> \<not>consistent (medial c g)"
proof(induct g)
  case Nil
  then show ?case by simp
next
  case (Cons a g)
  then show ?case
    apply (simp add: consistent_def)
    apply clarify
    unfolding cval_def
    apply (simp only: gval_and gval_gAnd maybe_and_is_true gval_And)
    by auto
qed

lemma consistent_medial_requires_consistent_anterior: "consistent (medial c g) \<Longrightarrow> consistent c"
  using inconsistent_anterior_gives_inconsistent_medial
  by auto

lemma consistent_posterior_requires_consistent_antrior: "consistent (posterior c t) \<Longrightarrow> consistent c"
  apply (simp add: posterior_def Let_def)
  apply (case_tac "consistent (medial c (Guard t))")
   apply simp
   apply (simp add: consistent_medial_requires_consistent_anterior)
  by (simp add: inconsistent_false)

lemma consistent_posterior_gives_consistent_medial: "consistent (posterior c x) \<Longrightarrow> consistent (medial c (Guard x))"
  apply (simp add: posterior_def Let_def)
  apply (case_tac "consistent (medial c (Guard x))")
   apply simp
  by (simp add: inconsistent_false)

lemma inconsistent_c_inconsistent_and: "\<not> consistent c \<Longrightarrow> \<not>consistent (\<lambda>r. if r = a then and c1 (c r) else c r)"
  apply (simp add: consistent_def cval_def)
  apply clarify
  apply (simp only: gval_and gval_gAnd)
  using maybe_and_is_true by fastforce
    
lemma generalise_subsumption: "c (V (R ri)) = Undef \<Longrightarrow> 
                               c (V (I i)) = Bc True \<Longrightarrow> 
                               subsumes c (remove_guard_add_update \<lparr>Label=l, Arity=a, Guard=[GExp.Eq (V (I i)) (L v)], Outputs=[], Updates=[]\<rparr> i ri)
                                                                   \<lparr>Label=l, Arity=a, Guard=[GExp.Eq (V (I i)) (L v)], Outputs=[], Updates=[]\<rparr>"
  apply (simp add: subsumes_def remove_guard_add_update_def ctx_simp2)
  apply safe
    apply (simp add: cval_def gval.simps)
   apply (simp add: posterior_def Let_def remove_input_constraints_def ctx_simp2)
   apply (case_tac "consistent (\<lambda>r. if r = V (I i) then and (cexp.Eq v) (c r) else c r)")
    apply (simp add: cval_empty_inputs)
    apply clarify
    apply (simp add: remove_input_constraints_def)
    apply (simp add: consistent_def)
    apply clarify
    apply (case_tac "r = V (R ri)")
     apply simp
    apply simp
    apply (case_tac "r = V (I i)")
     apply simp
    apply simp
   apply simp
  apply (simp add: posterior_def Let_def)
  apply (case_tac "consistent (\<lambda>r. and (if r = V (I i) then snd (V (I i), cexp.Eq v) else cexp.Bc True) (c r))")
   apply (simp add: test2)
   apply (simp add: remove_input_constraints_alt ctx_simp2)
   apply (case_tac "consistent c")
    apply (simp add: consistent_def)
    apply clarify
    apply (rule_tac x=s in exI)
    apply clarify
    apply (simp add: gval.simps cval_def)
  using gval_conjoin apply blast
   apply (simp add: inconsistent_c_inconsistent_and)
  by (simp add: inconsistent_false)

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

lemma cval_medial_true_requires_cval_anterior_true: "cval (medial c g r) r i = Some True \<Longrightarrow> cval (c r) r i = Some True"
proof(induct g)
  case Nil
  then show ?case by simp
next
  case (Cons a g)
  then show ?case
    apply simp
    unfolding cval_def
    by (simp only: gval_And gval_gAnd maybe_and_is_true)
qed

lemma cval_medial_var_update: "cval (medial m g x) y i = Some True \<Longrightarrow>
             cval (m x) y i = Some True"
  using cval_medial_true_requires_cval_anterior_true
proof(induct g)
  case Nil
  then show ?case by simp
next
  case (Cons a g)
  then show ?case
    apply simp
    unfolding cval_def
    by (simp only: gval_And gval_gAnd maybe_and_is_true)
qed

lemma satisfiable_undef: "satisfiable Undef"
  apply (simp add: satisfiable_def)
  apply (rule_tac x="V (R 1)" in exI)
  apply (rule_tac x="<>" in exI)
  by (simp add: cval_def gval.simps)

lemma invalid_false: "\<not>valid (cexp.Bc False)"
  by (simp add: valid_def cval_def gval.simps)

lemma get_false_aux_1: "c g (V x2) = cexp.Bc False \<Longrightarrow> x32 = V x2 \<Longrightarrow> \<forall>a s. cval (medial (c g) g (V x2)) a s \<noteq> Some True"
proof(induct g)
  case Nil
  then show ?case
    by (simp add: cval_def gval.simps)
next
  case (Cons a g)
  then show ?case
    apply simp
    unfolding cval_def
    apply (simp only: gval_And gval_gAnd maybe_and_is_true)
    apply simp
    apply clarify
    by (metis CExp.satisfiable_def Cons.prems(1) cval_def cval_medial_var_update unsatisfiable_false)
qed

lemma get_false_aux_2: "c g (Minus x41 x42) = cexp.Bc False \<Longrightarrow>
cval (medial (c g) g (Minus x41 x42)) a s \<noteq> Some True"
proof(induct g)
  case Nil
  then show ?case
    by (simp add: cval_def gval.simps)
next
  case (Cons a g)
  then show ?case
    apply simp
    unfolding cval_def
    apply (simp only: gval_And gval_gAnd maybe_and_is_true)
    apply simp
    apply clarify
    by (metis CExp.satisfiable_def Cons.prems(1) cval_def cval_medial_var_update unsatisfiable_false)
qed

lemma get_false: "Contexts.get (medial c g) x32 = cexp.Bc False \<Longrightarrow> \<not>CExp.satisfiable (Contexts.get (medial (medial c g) g) x32)"
  apply (simp add: CExp.satisfiable_def)
  apply (case_tac x32)
     apply simp+
    apply (simp add: get_false_aux_1)
   apply simp
  apply simp
  apply clarify
  by (simp add: get_false_aux_2)

lemma satisfiable_dont_get_false: "CExp.satisfiable (Contexts.get (medial (medial c g) g) x31) \<and> CExp.satisfiable (Contexts.get (medial (medial c g) g) x32) \<Longrightarrow>
       Contexts.get (medial c g) x32 \<noteq> cexp.Bc False"
  using get_false
  by auto

lemma last: "cval (Contexts.apply_updates (medial (medial c g) g) (medial c g) u r) r i = Some True \<Longrightarrow>
       cval (Contexts.apply_updates (medial c g) c u r) r i = Some True"
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
    apply (case_tac b)
       apply simp
       apply clarify
       apply simp
       apply (case_tac "r = V aa")
        apply simp+
       apply (case_tac "r = V aa")
       apply simp
       apply clarify
       apply (simp add: cval_medial_var_update)
      apply simp
     apply (simp del: compose_plus.simps)
     apply (case_tac "r = V aa")
     apply (simp del: compose_plus.simps)
      prefer 2
      apply simp
     apply clarify
     apply simp
     apply (case_tac "CExp.satisfiable (Contexts.get (medial (medial c g) g) x31) \<and> CExp.satisfiable (Contexts.get (medial (medial c g) g) x32)")
      apply simp
      apply (case_tac "valid (Contexts.get (medial (medial c g) g) x31) \<or> valid (Contexts.get (medial (medial c g) g) x32)")
       apply simp
       apply (case_tac "Contexts.get (medial c g) x31")
                   apply (simp add: satisfiable_undef)
             apply (case_tac "Contexts.get (medial c g) x32")
                   apply (simp add: satisfiable_undef)
                  apply (case_tac x2)
                   apply simp
                  apply (simp add: invalid_false)
                  apply (simp add: cval_def gval.simps)
    using satisfiable_dont_get_false apply auto[1]
    sorry
qed

lemma "subsumes c t t"
  apply (simp add: subsumes_def)
  apply safe
  apply (simp add: posterior_def Let_def)
  apply (case_tac "consistent (medial (medial c (Guard t)) (Guard t))")
   apply (simp add: consistent_medial_requires_consistent_anterior remove_input_constraints_alt)
  apply (case_tac "constrains_an_input r")
    apply simp
   apply simp
   defer
  using CExp.satisfiable_def unsatisfiable_false apply auto[1]
  by (simp add: last)
end