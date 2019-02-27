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
  "conjoin f = fold And (sorted_list_of_fset f) (Bc True)"

definition consistent :: "context \<Rightarrow> bool" where (* Is there a variable evaluation which can satisfy all of the context? *)
  "consistent c \<equiv> \<exists>s. \<forall>r. fBall (c r) (\<lambda>c. (cval c r s = true))"

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

fun make_lt :: "cexp \<Rightarrow> cexp" where
  "make_lt (Bc b) = Bc b" |
  "make_lt Undef = Undef" |
  "make_lt (Eq v) = Lt v" |
  "make_lt (Lt v) = Lt v" |
  "make_lt (Gt v) = Bc True" |
  "make_lt (Not v) = Not (make_lt v)" |
  "make_lt (And v va) = And (make_lt v) (make_lt va)"

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

  "guard2pairs a (gexp.Gt (L v) va) = (if L v = va then [(L (Num 0), {|Bc False|})] else [(va, {|Gt v|})])" |
  "guard2pairs a (gexp.Gt va (L v)) = (if L v = va then [(L (Num 0), {|Bc False|})] else [(va, {|Gt v|})])" |
  "guard2pairs a (gexp.Gt v vb) = (if v = vb then
                                     [(L (Num 0), {|Bc False|})]
                                   else
                                     [(v, fimage make_gt (get a vb))]
                                  )" |

  "guard2pairs a (Nor v va) = (map (\<lambda>(x, y). (x, fimage Not y)) ((guard2pairs a v) @ (guard2pairs a va)))"

fun pairs2context :: "(aexp \<times> cexp fset) list \<Rightarrow> context \<Rightarrow> context" where
  "pairs2context l c = (\<lambda>r. (c r) |\<union>| fold funion (map snd (filter (\<lambda>(a, _). a = r) l)) {||})"

fun apply_guard :: "context \<Rightarrow> guard \<Rightarrow> context" where
  "apply_guard a g = (pairs2context (guard2pairs a g) a)"

definition medial :: "context \<Rightarrow> guard list \<Rightarrow> context" where
 "medial c G = (apply_guard c (fold gAnd G (gexp.Bc True)))"

fun apply_update :: "context \<Rightarrow> context \<Rightarrow> update_function \<Rightarrow> context" where
  "apply_update l c (v, (L n)) = update c (V v) {|(Eq n)|}" |
  "apply_update l c (v, V vb) = update c (V v) (l (V vb))" |
  "apply_update l c (v, Plus vb vc) = update c (V v) {|(compose_plus (conjoin (get l vb)) (conjoin (get l vc)))|}" |
  "apply_update l c (v, Minus vb vc) = update c (V v) {|(compose_minus (conjoin (get l vb)) (conjoin (get l vc)))|}"

primrec apply_updates :: "context \<Rightarrow> context \<Rightarrow> update_function list \<Rightarrow> context" where
  "apply_updates _ c [] = c" |
  "apply_updates l c (h#t) = (apply_update l (apply_updates l c t) h)"

definition can_take :: "transition \<Rightarrow> context \<Rightarrow> bool" where
  "can_take t c \<equiv> consistent (medial c (Guard t))"

lemma can_take_no_guards: "\<forall> c. (Contexts.consistent c \<and> (Guard t) = []) \<longrightarrow> Contexts.can_take t c"
  by (simp add: consistent_def Contexts.can_take_def medial_def)

fun constrains_an_input :: "aexp \<Rightarrow> bool" where
  "constrains_an_input (L v) = False" |
  "constrains_an_input (V (R x)) = False" |
  "constrains_an_input (V (I x)) = True" |
  "constrains_an_input (Plus v va) = (constrains_an_input v \<and> constrains_an_input va)" |
  "constrains_an_input (Minus v va) = (constrains_an_input v \<and> constrains_an_input va)"

definition remove_input_constraints :: "context \<Rightarrow> context" where
  "remove_input_constraints c = (\<lambda>x. if constrains_an_input x then \<lbrakk>\<rbrakk> x else c x)"

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

lemma remove_input_constraints_alt:  "remove_input_constraints c = (\<lambda>x. if constrains_an_input x then {|Bc True|} else c x)"
  apply (rule ext)
  by (simp add: remove_input_constraints_def empty_inputs_are_true)

lemma remove_input_constraints_empty[simp]: "remove_input_constraints \<lbrakk>\<rbrakk> = \<lbrakk>\<rbrakk>"
  by (simp add: remove_input_constraints_def)

lemma consistent_remove_input_constraints[simp]: "consistent c \<Longrightarrow> consistent (remove_input_constraints c)"
proof-
  assume premise: "consistent c"
  show ?thesis
    using premise
    apply (simp add: consistent_def remove_input_constraints_def)
    apply clarify
    apply (rule_tac x=s in exI)
    apply clarify
    apply (case_tac r)
       apply simp
      apply (case_tac x2)
    by (simp_all add: cval_true)
qed

definition posterior :: "context \<Rightarrow> transition \<Rightarrow> context" where (* Corresponds to Algorithm 1 in Foster et. al. *)
  "posterior c t = (let c' = (medial c (Guard t)) in (if consistent c' then remove_input_constraints (apply_updates c' c (Updates t)) else (\<lambda>i. {|Bc False|})))"

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
definition subsumes :: "context \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> bool" where (* Corresponds to Algorithm 2 in Foster et. al. *)
  "subsumes c t2 t1 \<equiv> Label t1 = Label t2 \<and> Arity t1 = Arity t2 \<and> length (Outputs t1) = length (Outputs t2) \<and>
                      (\<forall>r i. (cval (conjoin (medial c (Guard t1) r)) r i = true) \<longrightarrow> (cval (conjoin (medial c (Guard t2) r)) r i) = true) \<and>
                      (\<forall> i r. satisfies_context r c \<longrightarrow> apply_guards (Guard t1) (join_ir i r) \<longrightarrow> apply_outputs (Outputs t1) (join_ir i r) = apply_outputs (Outputs t2) (join_ir i r)) \<and>
                      (\<exists> i r. apply_outputs (Outputs t1) (join_ir i r) = apply_outputs (Outputs t2) (join_ir i r)) \<and>
                      (\<forall>r i. fBall (posterior (medial c (Guard t1)) t2 r) (\<lambda>c. cval c r i = true) \<longrightarrow> fBall (posterior c t1 r) (\<lambda>c. cval c r i = true) \<or> (posterior c t1 r) = {|Undef|}) \<and>
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
  apply (simp add: posterior_def Let_def)
  apply (case_tac "consistent (medial c (Guard x))")
   apply simp
  by (simp add: inconsistent_false)

end