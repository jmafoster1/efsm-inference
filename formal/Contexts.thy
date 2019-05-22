subsection \<open>Contexts\<close>
text\<open>
This theory defines contexts as a way of relating possible constraints on register values to
observable output. We then use contexts to extend the idea of transition subsumption to EFSM
transitions with register update functions.
\<close>

theory Contexts
  imports
    EFSM GExp CExp
begin

type_synonym "context" = "aexp \<Rightarrow> cexp fset"

(*Decided to keep this as Bc True in order to oversimplify relatiy - strictly this should be
"Not Undef" for "has a value but we don't know what it is but this doesn't allow for
oversimplification*)
abbreviation empty :: "context" ("\<lbrakk>\<rbrakk>") where
  "empty \<equiv> (\<lambda>x. case x of
    (V v) \<Rightarrow> (case v of R n \<Rightarrow> {|Undef|} | I n \<Rightarrow> {|Bc True|}) |
    _ \<Rightarrow> {|Bc True|}
  )"
syntax
  "_updbind" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind" ("(2_ \<mapsto>/ _)")
  "_Context" :: "updbinds \<Rightarrow> 'a"      ("\<lbrakk>_\<rbrakk>")
translations
  "_Update f (_updbinds b bs)" \<rightleftharpoons> "_Update (_Update f b) bs"
  "_Context ms" == "_Update \<lbrakk>\<rbrakk> ms"
  "_Context (_updbinds b bs)" \<rightleftharpoons> "_Update (_Context b) bs"

lemma empty_register: "\<lbrakk>\<rbrakk> (V (R r)) = {|Undef|}"
  by (simp)

lemma empty_input: "\<lbrakk>\<rbrakk> (V (I i)) = {|Bc True|}"
  by (simp)

lemma consistent_empty_fball: "fBall (\<lbrakk>\<rbrakk> r) (\<lambda>c. cval c r Map.empty = true)"
  apply (cases r)
     apply (simp add: cval_true)
    apply (case_tac x2)
     apply (simp add: cval_true)
    apply (simp add: cval_def gval.simps ValueEq_def)
  using cval_true by auto

lemma empty_not_false[simp]: "{|Bc False|} \<noteq> \<lbrakk>\<rbrakk> i"
proof (induct i)
case (L x)
then show ?case by simp
next
  case (V x)
  then show ?case
    apply (case_tac x)
    by simp_all
next
  case (Plus i1 i2)
  then show ?case
    by simp
next
  case (Minus i1 i2)
  then show ?case
    by simp
qed

lemma empty_variable_constraints: "\<lbrakk>\<rbrakk> (V (R ri)) = {|Undef|} \<and> \<lbrakk>\<rbrakk> (V (I i)) = {|Bc True|}"
  by simp

fun get :: "context \<Rightarrow> aexp \<Rightarrow> cexp fset" where
  "get c (L n) = {|Eq n|}" |
  "get c (V v) = c (V v)" |
  "get c (Plus v va) = (c (Plus v va)) |\<union>| (c (Plus va v))" |
  "get c (Minus v va) = (c (Minus v va))"

fun update :: "context \<Rightarrow> aexp \<Rightarrow> cexp fset \<Rightarrow> context" where
  "update c (L n) _ = c" |
  "update c k v = (\<lambda>r. if r=k then v else c r)"

definition conjoin :: "cexp fset \<Rightarrow> cexp" where
  "conjoin f = foldr And (sorted_list_of_fset f) (Bc True)"

definition consistent :: "context \<Rightarrow> bool" where (* Is there a variable evaluation which can satisfy all of the context? *)
  "consistent c \<equiv> \<exists>s. \<forall>r. fBall (c r) (\<lambda>c. (cval c r s = true))"

lemma subset_consistency: "\<forall>r. c' r |\<subseteq>| c r \<Longrightarrow> consistent c \<Longrightarrow> consistent c'"
  apply (simp add: consistent_def)
  apply clarify
  apply (rule_tac x=s in exI)
  by auto

lemma possible_false_not_consistent: "\<exists>r. c r = {|Bc False|} \<Longrightarrow> \<not> consistent c"
  apply (simp add: consistent_def conjoin_def)
  apply clarify
  apply (rule_tac x=r in exI)
  by (simp add: sorted_list_of_fset_def cval_And cval_false cval_true)

lemma inconsistent_false: "\<not>consistent (\<lambda>i. {|Bc False|})"
  using possible_false_not_consistent
  by simp

lemma consistent_empty_1: "empty r = {|Undef|} \<or> empty r = {|Bc True|}"
  apply (cases r)
  prefer 2
    apply (case_tac x2)
  by simp_all

theorem consistent_empty_2: "(\<forall>r. c r = {|Bc True|}) \<longrightarrow> consistent c"
  apply (simp add: consistent_def conjoin_def sorted_list_of_fset_def)
  by (simp add: cval_And cval_true)

lemma consistent_empty_4: "\<lbrakk>\<rbrakk> r = {|Undef|} \<or> gval (cexp2gexp r (conjoin (\<lbrakk>\<rbrakk> r))) c = true"
  apply (case_tac r)
     apply (simp add: consistent_def conjoin_def sorted_list_of_fset_def maybe_double_negation)
     apply (simp add: gval_gAnd gval.simps(1))
    apply (case_tac x2)
     apply (simp add: conjoin_def sorted_list_of_fset_def gval_gAnd gval.simps(1))
    apply (simp add: conjoin_def)
   apply (simp add: conjoin_def sorted_list_of_fset_def gval_gAnd gval.simps(1))
  by (simp add: conjoin_def sorted_list_of_fset_def gval_gAnd gval.simps(1))

lemma consistent_empty [simp]: "consistent empty"
  apply (simp add: consistent_def cval_def)
  apply (rule_tac x="<>" in exI)
  apply clarify
  apply (case_tac r)
     apply (simp add: conjoin_def sorted_list_of_fset_def gval_gAnd gval.simps(1))
    apply (case_tac x2)
  by (simp_all add: conjoin_def sorted_list_of_fset_def gval_gAnd gval.simps ValueEq_def)

lemma cexp2gexp_double_neg: "gexp_equiv (cexp2gexp r (Not (Not x))) (cexp2gexp r x)"
  apply (simp add: gexp_equiv_def gval_gAnd)
  by (simp add: maybe_and_idempotent)

lemma gval_cexp2gexp_double_neg: "gval (cexp2gexp r (Not (Not x))) s = gval (cexp2gexp r x) s"
  using cexp2gexp_double_neg gexp_equiv_def by blast

fun make_gt :: "cexp \<Rightarrow> cexp" where
  "make_gt (Bc b) = Bc b" |
  "make_gt Undef = Undef" |
  "make_gt (Eq v) = Gt v" |
  "make_gt (Lt v) = Bc True" |
  "make_gt (Gt s) = Gt s" |
  "make_gt (Not v) = Not (make_gt v)" |
  "make_gt (And v va) = And (make_gt v) (make_gt va)"

lemma make_gt_twice: "make_gt (make_gt x) = make_gt x"
  apply (induct x)
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

fun make_lt :: "cexp \<Rightarrow> cexp" where
  "make_lt (Bc b) = Bc b" |
  "make_lt Undef = Undef" |
  "make_lt (Eq v) = Lt v" |
  "make_lt (Lt v) = Lt v" |
  "make_lt (Gt v) = Bc True" |
  "make_lt (Not v) = Not (make_lt v)" |
  "make_lt (And v va) = And (make_lt v) (make_lt va)"

lemma make_lt_twice: "make_lt (make_lt x) = make_lt x"
  apply(induct x)
  by auto

fun guard2pairs :: "context \<Rightarrow> guard \<Rightarrow> (aexp \<times> cexp fset) list" where
  "guard2pairs a (gexp.Bc True) = []" |
  "guard2pairs a (gexp.Bc False) = [(L (Num 0), {|Bc False|})]" |

  "guard2pairs a (gexp.Null v) = [(v, {|Undef|})]" |

  "guard2pairs a (gexp.Eq v (L n)) = [(v, {|Eq n|})]" |
  "guard2pairs a (gexp.Eq (L n) v) = [(v, {|Eq n|})]" |
  "guard2pairs a (gexp.Eq (Plus a1 a2) (Plus a4 a3)) = [((Plus a1 a2), (get a (Plus a2 a1)) |\<union>| (get a (Plus a3 a4))),
                                                        ((Plus a2 a1), (get a (Plus a1 a2)) |\<union>| (get a (Plus a3 a4))),
                                                        ((Plus a3 a4), (get a (Plus a4 a3)) |\<union>| (get a (Plus a1 a2))),
                                                        ((Plus a4 a3), (get a (Plus a3 a4)) |\<union>| (get a (Plus a1 a2)))]" |
  "guard2pairs a (gexp.Eq (Plus a1 a2) v) = [((Plus a1 a2), (get a v) |\<union>| (get a (Plus a1 a2))),
                                             ((Plus a2 a1), (get a v) |\<union>| (get a (Plus a2 a1))),
                                             (v, get a (Plus a1 a2))]" |
  "guard2pairs a (gexp.Eq v (Plus a1 a2)) = [((Plus a1 a2), (get a v) |\<union>| (get a (Plus a1 a2))),
                                             ((Plus a2 a1), (get a v) |\<union>| (get a (Plus a2 a1))),
                                             (v, get a (Plus a1 a2))]" |
  "guard2pairs a (gexp.Eq v va) = [(v, get a va), (va, get a v)]" |

  "guard2pairs a (gexp.Gt (L v) va) = (if L v = va then [(L (Num 0), {|Bc False|})] else [(va, {|Lt v|})])" |
  "guard2pairs a (gexp.Gt va (L v)) = (if L v = va then [(L (Num 0), {|Bc False|})] else [(va, {|Gt v|})])" |
  "guard2pairs a (gexp.Gt v vb) = (if v = vb then
                                     [(L (Num 0), {|Bc False|})]
                                   else
                                     [(v, fimage make_gt (get a vb))]
                                  )" |

  "guard2pairs a (Nor v va) = (map (\<lambda>(x, y). (x, fimage not y)) ((guard2pairs a v) @ (guard2pairs a va)))"

definition pairs2context :: "(aexp \<times> cexp fset) list \<Rightarrow> context" where
  "pairs2context l = (\<lambda>r. fold funion (map snd (filter (\<lambda>(a, _). a = r) l)) {||})"

lemma pairs2context_empty: "pairs2context [] x = {||}"
  by (simp add: pairs2context_def)

lemma pairs2context_append: "pairs2context (x @ y) ra = pairs2context x ra |\<union>| pairs2context y ra"
  apply (simp only: pairs2context_def)
  by (metis ffUnion_funion_distrib filter_append fold_union_ffUnion fset_of_list_append map_append map_eq_map_tailrec)

lemma pairs2context_cons: "pairs2context (x # y) ra = pairs2context [x] ra |\<union>| pairs2context y ra"
  by (metis append_Cons append_self_conv2 pairs2context_append)

definition medial :: "context \<Rightarrow> guard list \<Rightarrow> context" where
 "medial c G = (\<lambda>r. (c r) |\<union>| pairs2context (List.maps (guard2pairs c) G) r)"

lemma medial_cons: "medial c (a # G) ra = medial c [a] ra |\<union>| medial c G ra"
  apply (simp only: medial_def)
  by (simp add: inf_sup_aci(5) inf_sup_aci(7) maps_simps(1) maps_simps(2) pairs2context_append)

lemma List_maps_append:  "List.maps f (a@g) = (List.maps f a)@(List.maps f g)"
  by (simp add: List.maps_def)

lemma medial_append: "medial c (a @ G) ra = medial c a ra |\<union>| medial c G ra"
  apply (simp only: medial_def List_maps_append pairs2context_append)
  by auto

lemma medial_self_append: "medial c (g @ g) = medial c g"
  apply (rule ext)
  by (simp add: medial_append)

lemma medial_cons_subset: "medial c G ra |\<subseteq>| medial c (a # G) ra"
  apply (simp add: medial_def)
  apply (simp only: maps_simps(1))
  apply (simp only: pairs2context_append)
  by auto

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

lemma medial_empty: "medial c [] = c"
  by (simp add: medial_def pairs2context_def List.maps_def)

lemma anterior_subset_medial: "c r |\<subseteq>| (medial c G r)"
    by (simp add: medial_def pairs2context_def)

fun apply_update :: "context \<Rightarrow> context \<Rightarrow> update_function \<Rightarrow> context" where
  "apply_update l c (v, (L n)) = update c (V v) {|(Eq n)|}" |
  "apply_update l c (v, V vb) = update c (V v) (l (V vb))" |
  "apply_update l c (v, Plus vb vc) = update c (V v) (fimage (\<lambda>(a, b). compose_plus a b) ((get l vb) |\<times>| (get l vc)))" |
  "apply_update l c (v, Minus vb vc) = update c (V v) (fimage (\<lambda>(a, b). compose_minus a b) ((get l vb) |\<times>| (get l vc)))"

primrec apply_updates :: "context \<Rightarrow> context \<Rightarrow> update_function list \<Rightarrow> context" where
  "apply_updates _ c [] = c" |
  "apply_updates l c (h#t) = (apply_update l (apply_updates l c t) h)"

definition can_take :: "transition \<Rightarrow> context \<Rightarrow> bool" where
  "can_take t c \<equiv> consistent (medial c (Guard t))"

lemma can_take_no_guards: "\<forall> c. (Contexts.consistent c \<and> (Guard t) = []) \<longrightarrow> Contexts.can_take t c"
  by (simp add: consistent_def Contexts.can_take_def medial_def pairs2context_def List.maps_def)

fun constrains_an_input :: "aexp \<Rightarrow> bool" where
  "constrains_an_input (L v) = False" |
  "constrains_an_input (V (R x)) = False" |
  "constrains_an_input (V (I x)) = True" |
  "constrains_an_input (Plus v va) = (constrains_an_input v \<or> constrains_an_input va)" |
  "constrains_an_input (Minus v va) = (constrains_an_input v \<or> constrains_an_input va)"

definition remove_obsolete_constraints :: "context \<Rightarrow> vname fset \<Rightarrow> context" where
  "remove_obsolete_constraints c vs = (\<lambda>a. if \<exists>n. aexp_constrains a (V (I n)) \<or> fBex vs (\<lambda>x. aexp_constrains (V x) a \<and> a \<noteq> (V x)) then \<lbrakk>\<rbrakk> a else c a)"

lemma consistent_c_consistent_remove_obsolete_constraints: "consistent c \<Longrightarrow> consistent (remove_obsolete_constraints c Any)"
  apply (simp add: remove_obsolete_constraints_def consistent_def)
  apply clarify
  apply (rule_tac x=s in exI)
  apply clarify
  apply (case_tac r)
     apply simp
  apply (case_tac x2)
  using cval_true by auto

lemma empty_inputs_are_true: "constrains_an_input x \<Longrightarrow> \<lbrakk>\<rbrakk> x = {|Bc True|}"
  apply (case_tac x)
     apply simp
    apply (case_tac x2)
  by auto

lemma cval_empty_inputs: "constrains_an_input r \<longrightarrow> cval (conjoin (\<lbrakk>\<rbrakk> r)) r ia = true"
proof(induct r)
case (L x)
  then show ?case by simp
next
  case (V x)
  then show ?case
    apply (cases x)
     apply (simp add: conjoin_def sorted_list_of_fset_def)
     apply (simp only: cval_And maybe_and_true cval_true)
    by simp
next
  case (Plus r1 r2)
  then show ?case
    apply (simp add: conjoin_def sorted_list_of_fset_def)
    apply (simp only: cval_And maybe_and_true cval_true)
    by simp
next
  case (Minus r1 r2)
  then show ?case
    apply (simp add: conjoin_def sorted_list_of_fset_def)
    apply (simp only: cval_And maybe_and_true cval_true)
    by simp
qed

lemma remove_input_constraints_empty[simp]: "remove_obsolete_constraints \<lbrakk>\<rbrakk> s = \<lbrakk>\<rbrakk>"
  by (simp add: remove_obsolete_constraints_def)

definition posterior_separate :: "context \<Rightarrow> guard list \<Rightarrow> update_function list \<Rightarrow> context" where (* Corresponds to Algorithm 1 in Foster et. al. *)
  "posterior_separate c g u = (let c' = (medial c g) in (if consistent c' then remove_obsolete_constraints (apply_updates c' c u) (fset_of_list (map fst u)) else (\<lambda>i. {|Bc False|})))"

lemma posterior_separate_append_self: "posterior_separate c (g @ g) = posterior_separate c g"
  apply (rule ext)
  by (simp add: posterior_separate_def Let_def medial_self_append)

definition posterior :: "context \<Rightarrow> transition \<Rightarrow> context" where
  "posterior c t = posterior_separate c (Guard t) (Updates t)"

lemma posterior_consistent_medial: "medial c (Guard t) = c' \<Longrightarrow> consistent c' \<Longrightarrow> remove_obsolete_constraints (apply_updates c' c (Updates t)) (fst |`| fset_of_list (Updates t)) = p \<Longrightarrow> posterior c t = p"
  by (simp add: posterior_def posterior_separate_def)

primrec posterior_n :: "nat \<Rightarrow> transition \<Rightarrow> context \<Rightarrow> context" where (* Apply a given transition to a given context n times - good for reflexive transitions*)
  "posterior_n 0 _ c = c " |
  "posterior_n (Suc m) t c = posterior_n m t (posterior c t)"

primrec posterior_sequence :: "context \<Rightarrow> transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> context" where
  "posterior_sequence c _ _ _ [] = c" |
  "posterior_sequence c e s r (h#t) =
    (case (step e s r (fst h) (snd h)) of
      (Some (transition, s', outputs, r')) \<Rightarrow> (posterior_sequence (posterior c transition) e s' r' t) |
      _ \<Rightarrow> c
    )"

definition datastate2context :: "datastate \<Rightarrow> context" where
  "datastate2context d = (\<lambda>x. case x of V r \<Rightarrow> (case d r of None \<Rightarrow> {|Undef|} | Some v \<Rightarrow> {|Eq v|}) | _ \<Rightarrow> \<lbrakk>\<rbrakk> x)"

definition satisfies_context :: "datastate \<Rightarrow> context \<Rightarrow> bool" where
  "satisfies_context d c = consistent (\<lambda>x. (datastate2context d x) |\<union>| c x)"

lemma satisfactory_registers: "c (V (R r)) = {|cexp.Eq v|} \<Longrightarrow>
       satisfies_context ra c \<Longrightarrow>
       ra (R r) = Some v"
proof-
  assume premise1: "c (V (R r)) = {|cexp.Eq v|}"
  assume premise2: "satisfies_context ra c"
  have contra: "c (V (R r)) = {|cexp.Eq v|} \<Longrightarrow>
                ra (R r) \<noteq> Some v \<Longrightarrow>
                \<not>satisfies_context ra c"
    apply (simp add: satisfies_context_def datastate2context_def consistent_def)
    apply clarify
    apply (rule_tac x="V (R r)" in exI)
    apply (simp add: cval_def)
    apply (case_tac "ra (R r)")
    using gval.simps ValueEq_def
    by auto
  show ?thesis
    using premise1 premise2 contra by auto
qed

lemma cval_undef_empty: "cval Undef (V x) <> = true"
  by (simp add: cval_def gval.simps ValueEq_def)

lemma satisfies_context_empty: "satisfies_context <> \<lbrakk>\<rbrakk> \<and> satisfies_context Map.empty \<lbrakk>\<rbrakk>"
  apply (simp add: satisfies_context_def datastate2context_def consistent_def)
  apply (rule_tac x="<>" in exI)
  apply clarify
  apply (case_tac r)
     apply (simp add: cval_true)
    apply (case_tac x2)
     apply (case_tac "x=Bc True")
  by (simp_all add: cval_true cval_def gval.simps ValueEq_def)

(* Does t2 subsume t1? *)
definition subsumes :: "transition \<Rightarrow> context \<Rightarrow> transition \<Rightarrow> bool" ("_\<^sub>_\<sqsupseteq>_" 60) where (* Corresponds to Algorithm 2 in Foster et. al. *)
  "subsumes t2 c t1 \<equiv> Label t1 = Label t2 \<and> Arity t1 = Arity t2 \<and> length (Outputs t1) = length (Outputs t2) \<and>
                      (\<forall>r i. fBall (medial c (Guard t1) r) (\<lambda>c. cval c r i = true) \<longrightarrow> fBall (medial c (Guard t2) r) (\<lambda>c. cval c r i = true)) \<and>
                      (\<forall> i r. satisfies_context r c \<longrightarrow> apply_guards (Guard t1) (join_ir i r) \<longrightarrow> apply_outputs (Outputs t1) (join_ir i r) = apply_outputs (Outputs t2) (join_ir i r)) \<and>
                      (\<exists> i r. apply_outputs (Outputs t1) (join_ir i r) = apply_outputs (Outputs t2) (join_ir i r)) \<and>
                      (\<forall>r i. fBall (posterior_separate c (Guard t1@Guard t2) (Updates t2) r) (\<lambda>c. cval c r i = true) \<longrightarrow> fBall (posterior c t1 r) (\<lambda>c. cval c r i = true) \<or> (posterior c t1 r) = {|Undef|}) \<and>
                      (consistent (posterior c t1) \<longrightarrow> consistent (posterior c t2))"

lemma output_subsumption_violation: "\<not> (\<forall> i r. satisfies_context r c \<longrightarrow> apply_guards (Guard t1) (join_ir i r) \<longrightarrow> apply_outputs (Outputs t1) (join_ir i r) = apply_outputs (Outputs t2) (join_ir i r)) \<Longrightarrow>
      \<not> subsumes t2 c t1"
  by (simp add: subsumes_def)

lemma medial_subsumption_violation: "\<not> (\<forall>r i. fBall (medial c (Guard t1) r) (\<lambda>c. cval c r i = true) \<longrightarrow> fBall (medial c (Guard t2) r) (\<lambda>c. cval c r i = true)) \<Longrightarrow>
\<not> subsumes t2 c t1"
  by (simp add: subsumes_def)

lemma update_subsumption_violation: "\<not> (\<forall>r i. fBall (posterior_separate c (Guard t1@Guard t2) (Updates t2) r) (\<lambda>c. cval c r i = true) \<longrightarrow> fBall (posterior c t1 r) (\<lambda>c. cval c r i = true) \<or> (posterior c t1 r) = {|Undef|}) \<Longrightarrow>
      \<not> subsumes t2 c t1"
  by (simp add: subsumes_def)

lemma outputs_never_equal: "\<not>(\<exists> i r. apply_outputs (Outputs t1) (join_ir i r) = apply_outputs (Outputs t2) (join_ir i r)) \<Longrightarrow>
\<not> subsumes t2 c t1"
  by (simp add: subsumes_def)

lemma subsumption: "Label t1 = Label t2 \<and>
                    Arity t1 = Arity t2 \<and>
                    length (Outputs t1) = length (Outputs t2) \<Longrightarrow>
                    (\<forall>r i. fBall (medial c (Guard t1) r) (\<lambda>c. cval c r i = true) \<longrightarrow> fBall (medial c (Guard t2) r) (\<lambda>c. cval c r i = true)) \<Longrightarrow>
                    (\<forall> i r. satisfies_context r c \<longrightarrow> apply_guards (Guard t1) (join_ir i r) \<longrightarrow> apply_outputs (Outputs t1) (join_ir i r) = apply_outputs (Outputs t2) (join_ir i r)) \<Longrightarrow>
                    (\<exists> i r. apply_outputs (Outputs t1) (join_ir i r) = apply_outputs (Outputs t2) (join_ir i r)) \<Longrightarrow>
                    (\<forall>r i. fBall (posterior_separate c (Guard t1@Guard t2) (Updates t2) r) (\<lambda>c. cval c r i = true) \<longrightarrow> fBall (posterior c t1 r) (\<lambda>c. cval c r i = true) \<or> (posterior c t1 r) = {|Undef|}) \<Longrightarrow>
                    (consistent (posterior c t1) \<longrightarrow> consistent (posterior c t2)) \<Longrightarrow>
                    subsumes t2 c t1"
  by (simp add: subsumes_def)

definition anterior_context :: "transition_matrix \<Rightarrow> trace \<Rightarrow> context" where
 "anterior_context e t = posterior_sequence \<lbrakk>\<rbrakk> e 0 <> t"

lemma gexp_equiv_cexp_not_true:  "gexp_equiv (cexp2gexp a (Not (Bc True))) (gexp.Bc False)"
  by (simp add: gexp_equiv_def gval.simps)

lemma gexp_equiv_cexp_not_false:  "gexp_equiv (cexp2gexp a (Not (Bc False))) (gexp.Bc True)"
  by (simp add: gexp_equiv_def gval.simps)

lemma geq_to_ge: "Geq x = c r \<Longrightarrow> (cexp2gexp r (c r)) = Ge r (L x)"
  by (metis cexp2gexp.simps(3) cexp2gexp.simps(6))

lemma leq_to_le: "Leq x = c r \<Longrightarrow> (cexp2gexp r (c r)) = Le r (L x)"
  by (metis cexp2gexp.simps(4) cexp2gexp.simps(6))

lemma lt_to_lt: "Lt x = c r \<Longrightarrow> (cexp2gexp r (c r)) = gexp.Gt (L x) r"
  by (metis cexp2gexp.simps(3))

lemma gt_to_gt: "Gt x = c r \<Longrightarrow> (cexp2gexp r (c r)) = gexp.Gt r (L x)"
  by (metis cexp2gexp.simps(4))

lemma satisfiable_double_neg: "satisfiable (cexp.Not (cexp.Not x)) = satisfiable x"
  by (simp add: satisfiable_def cval_double_negation)

lemma gval_empty_r_neq_none[simp]: "gval (cexp2gexp r (conjoin (\<lbrakk>\<rbrakk> r))) s \<noteq> invalid"
  apply (case_tac r)
     apply (simp add: conjoin_def sorted_list_of_fset_def maybe_double_negation gval.simps)
    apply (case_tac x2)
  by (simp_all add: conjoin_def sorted_list_of_fset_def gval_gAnd gval.simps ValueEq_def)

lemma constrains_an_input_true: "constrains_an_input r \<Longrightarrow> cval (conjoin (\<lbrakk>\<rbrakk> r)) r ia = true"
proof(induct r)
  case (L x)
  then show ?case by simp
next
  case (V x)
  then show ?case
    apply (case_tac x)
    by (simp_all add: conjoin_def cval_And cval_true sorted_list_of_fset_def gval.simps)
next
  case (Plus r1 r2)
  then show ?case
    by (simp add: conjoin_def sorted_list_of_fset_def cval_And cval_true)
next
  case (Minus r1 r2)
  then show ?case
    by (simp add: conjoin_def sorted_list_of_fset_def cval_And cval_true)
qed

lemma consistent_posterior_gives_consistent_medial: "consistent (posterior c x) \<Longrightarrow> consistent (medial c (Guard x))"
  apply (simp add: posterior_def Let_def posterior_separate_def)
  apply (case_tac "consistent (medial c (Guard x))")
   apply simp
  by (simp add: inconsistent_false)

lemma consistent_medial_gives_consistent_anterior: "consistent (medial c G) \<Longrightarrow> consistent c"
  apply (simp add: consistent_def)
  by (metis (full_types) fBall_funion medial_def)

lemma medial_equivalent: "medial c (Guard t @ Guard t) = medial c (Guard t)"
  apply (rule ext)
  by (simp add: medial_append)

lemma transition_subsumes_self: "t \<^sub>c\<sqsupseteq> t"
  apply (simp add: subsumes_def)
  apply (simp only: posterior_separate_def Let_def posterior_def medial_equivalent)
  apply (case_tac "consistent (medial c (Guard t))")
   apply simp
  by simp

lemma medial_preserves_existing_elements: "x |\<in>| c r \<Longrightarrow> x |\<in>| medial c G r "
  using anterior_subset_medial by blast

lemma remove_obsolete_constraints_input: "remove_obsolete_constraints c s (V (I i)) = {|Bc True|}"
  by (simp add: remove_obsolete_constraints_def)

lemma filter_simp: "I i |\<notin>| fst |`| fset_of_list as \<Longrightarrow>
(\<exists>n. aexp_constrains a (V (I n))) \<or> V aa = a \<or> fBex (fset_of_list as) (\<lambda>x. V (fst x) = a) =
(\<exists>n. aexp_constrains a (V (I n))) \<or> fBex (fset_of_list as) (\<lambda>x. V (fst x) = a)"
  by auto

end
