subsection \<open>Contexts\<close>
text\<open>
This theory defines contexts as a way of relating possible constraints on register values to
observable output. We then use contexts to extend the idea of transition subsumption to EFSM
transitions with register update functions.
\<close>

theory Contexts
  imports
    EFSM "efsm-exp.GExp" "efsm-exp.CExp"
begin

type_synonym "context" = "aexp \<Rightarrow> cexp"

abbreviation empty ("\<lbrakk>\<rbrakk>") where
  "empty \<equiv> (\<lambda>x. case x of
    (V v) \<Rightarrow> (case v of R n \<Rightarrow> Undef | I n \<Rightarrow> Bc True) |
    _ \<Rightarrow> Bc True
  )"
syntax
  "_updbind" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind" ("(2_ \<mapsto>/ _)")
  "_Context" :: "updbinds \<Rightarrow> 'a"      ("\<lbrakk>_\<rbrakk>")
translations
  "_Update f (_updbinds b bs)" \<rightleftharpoons> "_Update (_Update f b) bs"
  "_Context ms" == "_Update \<lbrakk>\<rbrakk> ms"
  "_Context (_updbinds b bs)" \<rightleftharpoons> "_Update (_Context b) bs"

lemma empty_not_false[simp]: "cexp.Bc False \<noteq> \<lbrakk>\<rbrakk> i"
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

lemma empty_variable_constraints: "\<lbrakk>\<rbrakk> (V (R ri)) = Undef \<and> \<lbrakk>\<rbrakk> (V (I i)) = Bc True"
  by simp

fun get :: "context \<Rightarrow> aexp \<Rightarrow> cexp" where
  "get c (L n) = Eq n" |
  "get c (V v) = c (V v)" |
  "get c (Plus v va) = (And (c (Plus v va)) (c (Plus va v)))" |
  "get c (Minus v va) = (c (Minus v va))"

fun update :: "context \<Rightarrow> aexp \<Rightarrow> cexp \<Rightarrow> context" where
  "update c (L n) _ = c" |
  "update c k v = (\<lambda>r. if r=k then v else c r)"

fun conjoin :: "context \<Rightarrow> context \<Rightarrow> context" where
  "conjoin c c' = (\<lambda>r. (and (c r) (c' r)))"

fun negate :: "context \<Rightarrow> context" where
  "negate c = (\<lambda>r. not (c r))"

definition context_equiv :: "context \<Rightarrow> context \<Rightarrow> bool" where
  "context_equiv c c' \<equiv> (\<forall>r. cexp_equiv (c r) (c' r))"

lemma context_equiv_reflexive: "context_equiv x x"
  apply (simp add: context_equiv_def)
  apply (rule allI)
  by (simp add: cexp_equiv_def gexp_equiv_def)

lemma context_equiv_symmetric: "context_equiv x y \<Longrightarrow> context_equiv y x"
  apply (simp add: context_equiv_def)
  apply (rule allI)
  by (simp add: cexp_equiv_def gexp_equiv_def)

lemma context_equiv_transitive: "context_equiv x y \<and> context_equiv y z \<Longrightarrow> context_equiv x z"
  apply (simp add: context_equiv_def)
  apply (rule allI)
  by (simp add: cexp_equiv_def gexp_equiv_def)

definition consistent :: "context \<Rightarrow> bool" where (* Is there a variable evaluation which can satisfy all of the context? *)
  "consistent c \<equiv> \<exists>s. \<forall>r. (cval (c r) r s = Some True)"

lemma possible_false_not_consistent: "\<exists>r. c r = Bc False \<Longrightarrow> \<not> consistent c"
  unfolding consistent_def
  apply (simp add: cval_def)
  apply (rule allI)
  apply clarify
  apply (rule_tac x=r in exI)
  by (simp add: gval.simps)

lemma inconsistent_false: "\<not>consistent (\<lambda>i. cexp.Bc False)"
  by (simp add: consistent_def cval_def gval.simps)

definition valid_context :: "context \<Rightarrow> bool" where (* Is the context satisfied in all variable evaluations? *)
  "valid_context c \<equiv> \<forall>s. \<forall>r. (c r) = Undef \<or> (gval (cexp2gexp r (c r)) s = Some True)"

theorem consistent_empty_1: "empty r = Undef \<or> empty r = Bc True"
  apply (cases r)
  prefer 2
    apply (case_tac x2)
  by simp_all

theorem consistent_empty_2: "(\<forall>r. c r = Bc True) \<longrightarrow> consistent c"
  by (simp add: consistent_def cval_def gval.simps)

lemma consistent_empty_4: "\<lbrakk>\<rbrakk> r = Undef \<or> gval (cexp2gexp r (\<lbrakk>\<rbrakk> r)) c = Some True"
  using consistent_empty_1 gval_True by fastforce

lemma consistent_empty [simp]: "consistent empty"
  apply (simp add: consistent_def cval_def)
  apply (rule_tac x="<>" in exI)
  apply clarify
  apply (case_tac r)
     apply (simp add: gval.simps)
    apply (case_tac x2)
  by (simp_all add: gval.simps)

lemma cexp2gexp_double_neg: "gexp_equiv (cexp2gexp r (Not (Not x))) (cexp2gexp r x)"
  apply (simp add: gexp_equiv_def)
  apply (rule allI)
  apply (case_tac "gval (cexp2gexp r x) s")
   apply (simp)
  by (simp)

lemma gval_cexp2gexp_double_neg: "gval (cexp2gexp r (Not (Not x))) s = gval (cexp2gexp r x) s"
  using cexp2gexp_double_neg gexp_equiv_def by blast

primrec and_insert :: "(aexp \<times> cexp) list \<Rightarrow> (aexp \<times> cexp) \<Rightarrow> (aexp \<times> cexp) list" where
  "and_insert [] c = [c]" |
  "and_insert (h#t) c = (if fst h = fst c then ((fst h, and (snd h) (snd c))#t) else (h#(and_insert t c)))"

primrec pair_and :: "(aexp \<times> cexp) list \<Rightarrow> (aexp \<times> cexp) list \<Rightarrow> (aexp \<times> cexp) list" where
  "pair_and [] c = c" |
  "pair_and (h#t) c = pair_and t (and_insert c h)"

fun guard2pairs :: "context \<Rightarrow> guard \<Rightarrow> (aexp \<times> cexp) list" where
  "guard2pairs a (gexp.Bc True) = []" |
  "guard2pairs a (gexp.Bc False) = [(L (Num 0), Bc False)]" |

  "guard2pairs a (gexp.Null v) = [(v, Undef)]" |

  "guard2pairs a (gexp.Eq (L n) (L n')) =  (if n = n' then [] else [(L (Num 0), Bc False)])" |
  "guard2pairs a (gexp.Gt (L (Num n)) (L (Num n'))) = (if n > n' then [] else [(L (Num 0), Bc False)])" |

  "guard2pairs a (gexp.Eq v (L n)) = [(v, Eq n)]" |
  "guard2pairs a (gexp.Eq (L n) v) = [(v, Eq n)]" |
  "guard2pairs a (gexp.Eq v vb) = [(v, get a vb), (vb, get a v)]" |

  "guard2pairs a (gexp.Gt v (L n)) = [(v, (Gt n))]" |
  "guard2pairs a (gexp.Gt (L n) v) = [(v, (Lt n))]" |
  "guard2pairs a (gexp.Gt v vb) = (let (cv, cvb) = apply_gt (get a v) (get a vb) in [(v, cv), (vb, cvb)])" |

  "guard2pairs a (Nor v va) = (pair_and (map (\<lambda>x. ((fst x), not (snd x))) (guard2pairs a v)) (map (\<lambda>x. ((fst x), not (snd x))) (guard2pairs a va)))"

fun pairs2context :: "(aexp \<times> cexp) list \<Rightarrow> context" where
  "pairs2context [] = (\<lambda>i. Bc True)" |
  "pairs2context ((_, Bc False)#t) = (\<lambda>r. Bc False)" |
  "pairs2context (h#t) = conjoin (pairs2context t) (\<lambda>r. if r = (fst h) then (snd h) else Bc True)"

fun apply_guard :: "context \<Rightarrow> guard \<Rightarrow> context" where
  "apply_guard a g = conjoin (pairs2context (guard2pairs a g)) a"

primrec medial :: "context \<Rightarrow> guard list \<Rightarrow> context" where
 "medial c [] = c" |
 "medial c (h#t) = conjoin (pairs2context (guard2pairs c h)) (medial c t)"

fun apply_update :: "context \<Rightarrow> context \<Rightarrow> update_function \<Rightarrow> context" where
  "apply_update l c (v, (L n)) = update c (V v) (Eq n)" |
  "apply_update l c (v, V vb) = update c (V v) (l (V vb))" |
  "apply_update l c (v, Plus vb vc) = update c (V v) (compose_plus (get l vb) (get l vc))" |
  "apply_update l c (v, Minus vb vc) = update c (V v) (compose_minus (get l vb) (get l vc))"

primrec apply_updates :: "context \<Rightarrow> context \<Rightarrow> update_function list \<Rightarrow> context" where
  "apply_updates _ c [] = c" |
  "apply_updates l c (h#t) = (apply_update l (apply_updates l c t) h)"

definition can_take :: "transition \<Rightarrow> context \<Rightarrow> bool" where
  "can_take t c \<equiv> consistent (medial c (Guard t))"

lemma can_take_no_guards: "\<forall> c. (Contexts.consistent c \<and> (Guard t) = []) \<longrightarrow> Contexts.can_take t c"
  by (simp add: consistent_def Contexts.can_take_def)

fun constrains_an_input :: "aexp \<Rightarrow> bool" where
  "constrains_an_input (L v) = False" |
  "constrains_an_input (V (R x)) = False" |
  "constrains_an_input (V (I x)) = True" |
  "constrains_an_input (Plus v va) = (constrains_an_input v \<and> constrains_an_input va)" |
  "constrains_an_input (Minus v va) = (constrains_an_input v \<and> constrains_an_input va)"

definition remove_input_constraints :: "context \<Rightarrow> context" where
  "remove_input_constraints c = (\<lambda>x. if constrains_an_input x then \<lbrakk>\<rbrakk> x else c x)"

lemma empty_inputs_are_true: "constrains_an_input x \<Longrightarrow> \<lbrakk>\<rbrakk> x = Bc True"
  apply (case_tac x)
     apply simp
    apply (case_tac x2)
  by auto

lemma cval_empty_inputs: "constrains_an_input r \<longrightarrow> cval (\<lbrakk>\<rbrakk> r) r ia = Some True"
  by (simp add: empty_inputs_are_true cval_def gval.simps)

lemma remove_input_constraints_alt:  "remove_input_constraints c = (\<lambda>x. if constrains_an_input x then Bc True else c x)"
  apply (rule ext)
  by (simp add: remove_input_constraints_def empty_inputs_are_true)

lemma remove_input_constraints_empty[simp]: "remove_input_constraints \<lbrakk>\<rbrakk> = \<lbrakk>\<rbrakk>"
  by (simp add: remove_input_constraints_def)

lemma consistent_remove_input_constraints[simp]: "consistent c \<Longrightarrow> consistent (remove_input_constraints c)"
proof-
  assume premise: "consistent c"
  show ?thesis
    using premise
    apply (simp add: remove_input_constraints_def consistent_def cval_def)
    apply clarify
    apply (rule_tac x=s in exI)
    apply (rule allI)
    apply (case_tac "constrains_an_input r")
     apply simp
     apply (case_tac r)
        apply (simp add: gval.simps)
       apply (case_tac x2)
    by (simp_all add: gval.simps)
qed

definition posterior :: "context \<Rightarrow> transition \<Rightarrow> context" where (* Corresponds to Algorithm 1 in Foster et. al. *)
  "posterior c t = (let c' = (medial c (Guard t)) in (if consistent c' then remove_input_constraints (apply_updates c' c (Updates t)) else (\<lambda>i. Bc False)))"

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
  "datastate2context d = (\<lambda>x. case x of V r \<Rightarrow> (case d r of None \<Rightarrow> Undef | Some v \<Rightarrow> Eq v) | _ \<Rightarrow> \<lbrakk>\<rbrakk> x)"

definition satisfies_context :: "datastate \<Rightarrow> context \<Rightarrow> bool" where
  "satisfies_context d c = consistent (conjoin (datastate2context d) c)"

lemma satisfies_context_empty: "satisfies_context <> \<lbrakk>\<rbrakk> \<and> satisfies_context Map.empty \<lbrakk>\<rbrakk>"
  apply (simp add: satisfies_context_def consistent_def datastate2context_def cval_def)
  apply (rule_tac x="<>" in exI)
  apply clarify
  apply (case_tac r)
        apply (simp add: gval.simps)
    apply (case_tac x2)
  by (simp_all add: gval.simps)

(* Does t2 subsume t1? *)
definition subsumes :: "context \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> bool" where (* Corresponds to Algorithm 2 in Foster et. al. *)
  "subsumes c t2 t1 \<equiv> Label t1 = Label t2 \<and> Arity t1 = Arity t2 \<and> length (Outputs t1) = length (Outputs t2) \<and>
                      (\<forall>r i. (cval (medial c (Guard t1) r) r i = Some True) \<longrightarrow> (cval (medial c (Guard t2) r) r i) = Some True) \<and>
                      (\<forall> i r. satisfies_context r c \<longrightarrow> apply_guards (Guard t1) (join_ir i r) \<longrightarrow> apply_outputs (Outputs t1) (join_ir i r) = apply_outputs (Outputs t2) (join_ir i r)) \<and>
                      (\<exists> i r. apply_outputs (Outputs t1) (join_ir i r) = apply_outputs (Outputs t2) (join_ir i r)) \<and>
                      (\<forall>r i. cval (posterior (medial c (Guard t1)) t2 r) r i = Some True \<longrightarrow> (cval (posterior c t1 r) r i = Some True) \<or> (posterior c t1 r) = Undef) \<and>
                      (consistent (posterior c t1) \<longrightarrow> consistent (posterior c t2))"

definition anterior_context :: "transition_matrix \<Rightarrow> trace \<Rightarrow> context" where
 "anterior_context e t = posterior_sequence \<lbrakk>\<rbrakk> e 0 <> t"

(* Does t1 subsume t2 in all possible anterior contexts? *)
(* For every path which gets us to the problem state, does t1 subsume t2 in the resulting context *)
definition directly_subsumes :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> bool" where
  "directly_subsumes e1 e2 s t1 t2 \<equiv> (\<forall>p. accepts_trace e1 p \<and> gets_us_to s e1 0 <>  p \<longrightarrow> subsumes (anterior_context e2 p) t1 t2) \<and>
                                     (\<exists>c. subsumes c t1 t2)"

lemma cant_directly_subsume: "\<forall>c. \<not> subsumes c t t' \<Longrightarrow> \<not> directly_subsumes m m' s t t'"
  by (simp add: directly_subsumes_def)

primrec pairs2guard :: "(aexp \<times> cexp) list \<Rightarrow> guard" where
  "pairs2guard [] = gexp.Bc True" |
  "pairs2guard (h#t) = gAnd (cexp2gexp (fst h) (snd h)) (pairs2guard t)"

lemma context_equiv_same_undef: "c i = Undef \<Longrightarrow> c' i = cexp.Bc True \<Longrightarrow> \<not> context_equiv c c'"
  apply (simp add: context_equiv_def cexp_equiv_def gexp_equiv_def)
  apply (rule_tac x=i in exI)
  apply (simp add: cval_def gval.simps)
  using aval.simps(1) by blast

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

lemma gval_empty_r_neq_none[simp]: "gval (cexp2gexp r (\<lbrakk>\<rbrakk> r)) s \<noteq> None"
  apply (case_tac r)
     apply (simp add: gval.simps)
    apply (case_tac x2)
  by (simp_all add: gval.simps)

lemma inconsistant_conjoin_false: "\<not>consistent (conjoin (\<lambda>r. cexp.Bc False) c)"
  apply (simp add: consistent_def cval_def)
  apply clarify
  apply (rule_tac x=r in exI)
  apply (case_tac "c r")
        apply (simp add: gval.simps)
       apply (case_tac x2)
        apply (simp add: gval.simps)+
     apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval r s)")
      apply (simp add: gval.simps)+
    apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x5)")
     apply (simp add: gval.simps)+
   apply (case_tac "gval (cexp2gexp r x6) s")
    apply (simp add: gval.simps)+
  apply (case_tac "gval (cexp2gexp r x71) s")
   apply (simp add: gval.simps)+
  apply (case_tac "gval (cexp2gexp r x72) s")
  by auto

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
    apply (simp only: gval_and gval_gAnd maybe_and_true gval_And)
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

lemma unsatisfiable_cexp_gives_unsatisfiable_medial: "\<not>satisfiable (Contexts.get c x) \<Longrightarrow> \<not>satisfiable (Contexts.get (medial c g) x)"
proof(induct g)
  case Nil
  then show ?case
    by (simp add: unsatisfiable_lt)
next
  case (Cons a g)
  then show ?case
    apply (simp add: satisfiable_def)
    apply (case_tac x)
       apply simp
      apply simp
      apply (simp only: cval_def gval_And gval_gAnd maybe_and_true)
      apply simp
     apply simp
     apply (simp only: cval_def gval_And gval_gAnd maybe_and_true gval_and)
     apply simp
     apply simp
     apply (simp only: cval_def gval_And gval_gAnd maybe_and_true gval_and)
    by simp
qed

lemma cexp_satisfiable_medial_medial: "satisfiable (Contexts.get (medial c g) b1) \<Longrightarrow> satisfiable (Contexts.get c b1)"
  using unsatisfiable_cexp_gives_unsatisfiable_medial by blast
end
