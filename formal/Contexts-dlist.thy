subsection \<open>Contexts\<close>
text\<open>
This theory defines contexts as a way of relating possible constraints on register values to
observable output. We then use contexts to extend the idea of transition subsumption to EFSM
transitions with register update functions.
\<close>

theory Contexts
  imports
    EFSM GExp "efsm-exp.CExp" "~~/src/HOL/Library/Dlist"
begin

context includes dlist.lifting begin
lift_definition dfold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a dlist \<Rightarrow> 'b \<Rightarrow> 'b" is fold.
lift_definition dappend :: "'a dlist \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist" (infix "|@|" 50) is "\<lambda>x y. remdups (x @ y)"
  by simp
end

type_synonym "context" = "aexp \<Rightarrow> cexp dlist"

abbreviation empty ("\<lbrakk>\<rbrakk>") where
  "empty \<equiv> (\<lambda>x. case x of
    (V v) \<Rightarrow> (case v of R n \<Rightarrow> Dlist [Undef] | I n \<Rightarrow> Dlist [Bc True]) |
    _ \<Rightarrow> Dlist [Bc True]
  )"
syntax
  "_updbind" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind" ("(2_ \<mapsto>/ _)")
  "_Context" :: "updbinds \<Rightarrow> 'a"      ("\<lbrakk>_\<rbrakk>")
translations
  "_Update f (_updbinds b bs)" \<rightleftharpoons> "_Update (_Update f b) bs"
  "_Context ms" == "_Update \<lbrakk>\<rbrakk> ms"
  "_Context (_updbinds b bs)" \<rightleftharpoons> "_Update (_Context b) bs"

lemma list_of_dlist_singleton[simp]: "list_of_dlist (Abs_dlist [a]) = [a]"
  by (simp add: Abs_dlist_inverse)

definition collapse :: "cexp dlist \<Rightarrow> cexp" where
  "collapse l = dfold (\<lambda>x y. and x y) l (Bc True)"

fun get :: "context \<Rightarrow> aexp \<Rightarrow> cexp" where
  "get c (L n) = Eq n" |
  "get c (V v) = collapse (c (V v))" |
  "get c (Plus v va) = collapse ((c (Plus v va)) |@|  (c (Plus va v)))" |
  "get c (Minus v va) = collapse (c (Minus v va))"

lemma empty_not_false[simp]: "cexp.Bc False \<noteq> get \<lbrakk>\<rbrakk> i"
proof (induct i)
case (L x)
then show ?case by simp
next
  case (V x)
  then show ?case
    apply (case_tac x)
    by (simp_all add: collapse_def dfold_def)
next
  case (Plus i1 i2)
  then show ?case
    by (simp add: collapse_def dfold_def dappend_def)
next
  case (Minus i1 i2)
  then show ?case
    by (simp add: collapse_def dfold_def)
qed

fun update :: "context \<Rightarrow> aexp \<Rightarrow> cexp dlist \<Rightarrow> context" where
  "update c (L n) _ = c" |
  "update c k v = (\<lambda>r. if r=k then v else c r)"

fun single_update :: "context \<Rightarrow> aexp \<Rightarrow> cexp \<Rightarrow> context" where
  "single_update c k v = update c k (Dlist [v])"

fun conjoin :: "context \<Rightarrow> context \<Rightarrow> context" where
  "conjoin c c' = (\<lambda>r. ((c r) |@| (c' r)))"

fun negate :: "context \<Rightarrow> context" where
  "negate c = (\<lambda>r. Dlist [not (get c r)])"

definition context_equiv :: "context \<Rightarrow> context \<Rightarrow> bool" where
  "context_equiv c c' \<equiv> (\<forall>r. cexp_equiv (get c r) (get c' r))"

lemma context_equiv_reflexive: "context_equiv x x"
  apply (simp add: context_equiv_def)
  apply (rule allI)
  by (simp add: cexp_equiv_def)

lemma context_equiv_symmetric: "context_equiv x y \<Longrightarrow> context_equiv y x"
  apply (simp add: context_equiv_def)
  apply (rule allI)
  by (simp add: cexp_equiv_def)

lemma context_equiv_transitive: "context_equiv x y \<and> context_equiv y z \<Longrightarrow> context_equiv x z"
  apply (simp add: context_equiv_def)
  apply (rule allI)
  by (simp add: cexp_equiv_def)

fun cexp2gexp :: "aexp \<Rightarrow> cexp \<Rightarrow> gexp" where
  "cexp2gexp _ (Bc b) = gexp.Bc b" |
  "cexp2gexp a Undef = gexp.Bc False" |
  "cexp2gexp a (Lt v) = gexp.Gt (L v) a" |
  "cexp2gexp a (Gt v) = gexp.Gt a (L v)" |
  "cexp2gexp a (Eq v) = gexp.Eq a (L v)" |
  "cexp2gexp a (Not v) = gNot (cexp2gexp a v)" |
  "cexp2gexp a (And v va) = gAnd (cexp2gexp a v) (cexp2gexp a va)"

definition consistent :: "context \<Rightarrow> bool" where (* Is there a variable evaluation which can satisfy all of the context? *)
  "consistent c \<equiv> \<exists>s. \<forall>r. (get c r) = Undef \<or> (gval (cexp2gexp r (get c r)) s = Some True)"

lemma possible_false_not_consistent: "\<exists>r. (get c r) = Bc False \<Longrightarrow> \<not> consistent c"
  unfolding consistent_def
  apply simp
  apply (rule allI)
  apply clarify
  apply (rule_tac x=r in exI)
  by simp

lemma inconsistent_false: "\<not>consistent (\<lambda>i. Dlist [Bc False])"
  apply (simp add: consistent_def collapse_def dfold_def)
  apply clarify
  apply (rule_tac x="V v" in exI)
  by (simp add: collapse_def dfold_def)

definition valid_context :: "context \<Rightarrow> bool" where (* Is the context satisfied in all variable evaluations? *)
  "valid_context c \<equiv> \<forall>s. \<forall>r. (get c r) = Undef \<or> (gval (cexp2gexp r (get c r)) s = Some True)"

theorem consistent_empty_1: "\<lbrakk>\<rbrakk> r = Dlist [Undef] \<or> \<lbrakk>\<rbrakk> r = Dlist [Bc True]"
  apply (cases r)
  prefer 2
    apply (case_tac x2)
  by simp_all

theorem consistent_empty_2: "(\<forall>r. get c r = Bc True \<or> get c r = Undef) \<longrightarrow> consistent c"
  apply (simp add: consistent_def)
  by force

lemma consistent_empty_3: "(\<forall>r. get \<lbrakk>\<rbrakk> r = Bc True \<or> get \<lbrakk>\<rbrakk> r = Undef) \<longrightarrow> consistent empty"
  apply (insert consistent_empty_2)
  by simp

lemma consistent_empty_4: "get \<lbrakk>\<rbrakk> r = Undef \<or> gval (cexp2gexp r (get \<lbrakk>\<rbrakk> r)) c = Some True"
  apply (cases r)
     apply simp+
    apply (case_tac x2)
     apply (simp add: collapse_def dfold_def)+
   apply (simp add: dappend_def)
  by (simp add: collapse_def dfold_def)

lemma consistent_empty [simp]: "consistent empty"
  by (simp add: consistent_def consistent_empty_4)

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

  "guard2pairs a (gexp.Null v) = [(V v, Undef)]" |

  "guard2pairs a (gexp.Eq (L n) (L n')) =  [(L n, Eq n')]" |
  "guard2pairs a (gexp.Gt (L n) (L n')) =  [(L n, Gt n')]" |

  "guard2pairs a (gexp.Eq v (L n)) = [(v, Eq n)]" |
  "guard2pairs a (gexp.Eq (L n) v) = [(v, Eq n)]" |
  "guard2pairs a (gexp.Eq v vb) = (if v = vb then [] else [(v, get a vb), (vb, get a v)])" |

  "guard2pairs a (gexp.Gt v (L n)) = [(v, (Gt n))]" |
  "guard2pairs a (gexp.Gt (L n) v) = [(v, (Lt n))]" |
  "guard2pairs a (gexp.Gt v vb) = (let (cv, cvb) = apply_gt (get a v) (get a vb) in [(v, cv), (vb, cvb)])" |

  "guard2pairs a (Nor v va) = (pair_and (map (\<lambda>x. ((fst x), not (snd x))) (guard2pairs a v)) (map (\<lambda>x. ((fst x), not (snd x))) (guard2pairs a va)))"

(*fun pairs2context :: "(aexp \<times> cexp) list \<Rightarrow> context" where
  "pairs2context [] = (\<lambda>i. Dlist [Bc True])" |
  "pairs2context ((_, Bc False)#t) = (\<lambda>r. Dlist [Bc False])" |
  "pairs2context ((a, c)#t) = conjoin (pairs2context t) (\<lambda>r. if r = a then Dlist [c] else Dlist [Bc True])"*)

primrec pairs2context2 :: "(aexp \<times> cexp) list \<Rightarrow> context \<Rightarrow> context" where
  "pairs2context2 [] c = c" |
  "pairs2context2 (h#t) c = pairs2context2 t (update c (fst h) (Dlist.insert (snd h) (c (fst h))))"

fun apply_guard :: "context \<Rightarrow> guard \<Rightarrow> context" where
  "apply_guard a g = (pairs2context2 (guard2pairs a g) a)"

definition medial :: "context \<Rightarrow> guard list \<Rightarrow> context" where
   "medial c G = (apply_guard c (fold gAnd G (gexp.Bc True)))"

fun apply_update :: "context \<Rightarrow> context \<Rightarrow> update_function \<Rightarrow> context" where
  "apply_update l c (v, (L n)) = single_update c (V v) (Eq n)" |
  "apply_update l c (v, V vb) = update c (V v) (l (V vb))" |
  "apply_update l c (v, Plus vb vc) = single_update c (V v) (compose_plus (get l vb) (get l vc))" |
  "apply_update l c (v, Minus vb vc) = single_update c (V v) (compose_minus (get l vb) (get l vc))"

primrec apply_updates :: "context \<Rightarrow> context \<Rightarrow> update_function list \<Rightarrow> context" where
  "apply_updates _ c [] = c" |
  "apply_updates l c (h#t) = apply_updates l (apply_update l c h) t"

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

lemma empty_inputs_are_true: "constrains_an_input x \<Longrightarrow> get \<lbrakk>\<rbrakk> x = Bc True"
  apply (case_tac x)
     apply simp
    apply (case_tac x2)
  by (simp_all add: collapse_def dfold_def dappend_def)

lemma remove_input_constraints_alt:  "remove_input_constraints c = (\<lambda>x. if constrains_an_input x then Dlist [Bc True] else c x)"
  apply (rule ext)
  apply (simp add: remove_input_constraints_def empty_inputs_are_true)
  apply (case_tac x)
     apply simp_all
  apply (case_tac x2)
  by auto

lemma remove_input_constraints_empty[simp]: "remove_input_constraints \<lbrakk>\<rbrakk> = \<lbrakk>\<rbrakk>"
  by (simp add: remove_input_constraints_def)

lemma consistent_remove_input_constraints[simp]: "consistent c \<Longrightarrow> consistent (remove_input_constraints c)"
proof-
  assume premise: "consistent c"
  have consistent_aux: "\<And>r s. get c r = Undef \<or> gval (cexp2gexp r (get c r)) s = Some True \<Longrightarrow>
           gval (cexp2gexp r (get (\<lambda>x. if constrains_an_input x then Dlist [cexp.Bc True] else c x) r)) s \<noteq> Some True \<Longrightarrow>
           get (\<lambda>x. if constrains_an_input x then Dlist [cexp.Bc True] else c x) r = Undef "
    apply (case_tac r)
       apply simp
      apply (case_tac x2)
       apply (simp add: collapse_def dfold_def)
      apply simp
     apply (simp add: dappend_def collapse_def dfold_def)
     apply auto[1]
     apply (simp add: dappend_def collapse_def dfold_def)
    by auto
  show ?thesis
    using premise
    apply (simp add: remove_input_constraints_alt)
    apply (simp add: consistent_def)
    apply clarify
    apply (rule_tac x=s in exI)
    apply clarify
    using consistent_aux
    by auto
qed

definition posterior :: "context \<Rightarrow> transition \<Rightarrow> context" where (* Corresponds to Algorithm 1 in Foster et. al. *)
  "posterior c t = (let c' = (medial c (Guard t)) in
                    (if consistent c' then
                       remove_input_constraints (apply_updates c' c (Updates t))
                     else
                       (\<lambda>i. Dlist [Bc False]))
                   )"

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
  "datastate2context d = (\<lambda>x. case x of V r \<Rightarrow> (case d r of None \<Rightarrow> Dlist [Undef] | Some v \<Rightarrow> Dlist [Eq v]) | _ \<Rightarrow> \<lbrakk>\<rbrakk> x)"

definition satisfies_context :: "datastate \<Rightarrow> context \<Rightarrow> bool" where
  "satisfies_context d c = consistent (conjoin (datastate2context d) c)"

lemma satisfies_context_empty: "satisfies_context <> \<lbrakk>\<rbrakk> \<and> satisfies_context Map.empty \<lbrakk>\<rbrakk>"
  apply (simp add: satisfies_context_def consistent_def datastate2context_def)
  apply (rule_tac x="<>" in exI)
  apply clarify
  apply (case_tac r)
     apply simp
    apply (case_tac x2)
  by (simp add: collapse_def dfold_def dappend_def Abs_dlist_inverse)+

(* Does t2 subsume t1? *)
definition subsumes :: "context \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> bool" where (* Corresponds to Algorithm 2 in Foster et. al. *)
  "subsumes c t2 t1 \<equiv> Label t1 = Label t2 \<and> Arity t1 = Arity t2 \<and> length (Outputs t1) = length (Outputs t2) \<and>
                      (\<forall>r i. (cval (get (medial c (Guard t1)) r) i = Some True) \<longrightarrow> (cval (get (medial c (Guard t2)) r) i) = Some True) \<and>
                      (\<forall> i r. satisfies_context r c \<longrightarrow> apply_guards (Guard t1) (join_ir i r) \<longrightarrow> apply_outputs (Outputs t1) (join_ir i r) = apply_outputs (Outputs t2) (join_ir i r)) \<and>
                      (\<exists> i r. apply_outputs (Outputs t1) (join_ir i r) = apply_outputs (Outputs t2) (join_ir i r)) \<and>
                      (\<forall>r i. cval (get (posterior (medial c (Guard t1)) t2) r) i = Some True \<longrightarrow> (cval (get (posterior c t1) r) i = Some True) \<or> (get (posterior c t1) r) = Undef) \<and>
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

lemma context_equiv_same_undef: "get c i = Undef \<Longrightarrow> get c' i = cexp.Bc True \<Longrightarrow> \<not> context_equiv c c'"
  apply (simp add: context_equiv_def cexp_equiv_def)
  by (metis CExp.satisfiable_def satisfiable_true unsatisfiable_undef)

(* lemma context_equiv_undef: "context_equiv c c' \<Longrightarrow> ((c i) = Undef) = ((c' i) = Undef)" *)
  (* apply (simp add: cexp_equiv_def context_equiv_def) *)

lemma gexp_equiv_cexp_not_true:  "gexp_equiv (cexp2gexp a (Not (Bc True))) (gexp.Bc False)"
  by (simp add: gexp_equiv_def)

lemma gexp_equiv_cexp_not_false:  "gexp_equiv (cexp2gexp a (Not (Bc False))) (gexp.Bc True)"
  by (simp add: gexp_equiv_def)

lemma geq_to_ge: "Geq x = c r \<Longrightarrow> (cexp2gexp r (c r)) = Ge r (L x)"
  by (metis cexp2gexp.simps(3) cexp2gexp.simps(6))

lemma leq_to_le: "Leq x = c r \<Longrightarrow> (cexp2gexp r (c r)) = Le r (L x)"
  by (metis cexp2gexp.simps(4) cexp2gexp.simps(6))

lemma lt_to_lt: "Lt x = c r \<Longrightarrow> (cexp2gexp r (c r)) = gexp.Gt (L x) r"
  by (metis cexp2gexp.simps(3))

lemma gt_to_gt: "Gt x = c r \<Longrightarrow> (cexp2gexp r (c r)) = gexp.Gt r (L x)"
  by (metis cexp2gexp.simps(4))

lemma not_satisfiable_def: "\<not> satisfiable c = (\<forall>i. cval c i = Some False \<or> cval c i = None)"
  apply (simp add: satisfiable_def)
  apply safe
   apply (rule_tac x=i in exI)
   apply auto[1]
  apply simp
   apply (rule_tac x=i in exI)
  by simp

lemma cexp_satisfiable_some_false: "CExp.satisfiable (cexp.Not c) \<Longrightarrow> \<exists>i. cval c i = Some False"
  apply (simp add: satisfiable_def)
  by (metis (full_types) cval.simps(6) cval_double_negation map_option_case option.simps(9))

lemma true_or_none_not_false: "(\<forall>i. cval c i = Some True \<or> cval c i = None) \<Longrightarrow> \<nexists>i. cval c i = Some False"
  by (metis CExp.satisfiable_def not_satisfiable_def option.distinct(1))

lemma not_satisfiable_neg: "\<not> CExp.satisfiable (cexp.Not c) = (\<forall>i. cval c i = Some True \<or> cval c i = None)"
  apply safe
   apply (simp add: satisfiable_def)
   apply (metis option.case_eq_if option.sel option.simps(3))
   apply (simp add: satisfiable_def)
  by (metis (full_types) map_option_case option.simps(9))

lemma satisfiable_double_neg: "satisfiable (cexp.Not (cexp.Not x)) = satisfiable x"
  apply (simp add: satisfiable_def)
  by (metis cval.simps(6) cval_double_negation)

lemma cval_empty_r_neq_none[simp]: "cval (get \<lbrakk>\<rbrakk> r) i \<noteq> None"
  apply (case_tac r)
     apply (simp)
    apply (simp)
    apply (case_tac x2)
     apply (simp add: collapse_def dfold_def)
     apply auto[1]
     apply (simp add: collapse_def dfold_def)
    apply auto[1]
   apply (simp add: collapse_def dfold_def dappend_def)
  by (simp add: collapse_def dfold_def)

lemma abs_dlist_remdups_inverse: "Abs_dlist (remdups (list_of_dlist d)) = d"
proof(induct d)
  case empty
  then show ?case
    by (metis Dlist.empty_def Dlist_def list_of_dlist_empty)
next
  case (insert x d)
  then show ?case
    apply simp
    by (metis list_of_dlist_insert list_of_dlist_inverse remdups_list_of_dlist)
qed

lemma compound_insert: "Dlist.insert e (Dlist.insert e l) = Dlist.insert e l"
    apply (simp add: Dlist.insert_def)
  by (simp add: distinct_remdups_id)

lemma "consistent (apply_guard (apply_guard c G) G) = consistent (apply_guard c G)"
proof(induct G)
  case (Bc x)
  then show ?case
    apply (cases x)
    by auto
next
  case (Eq a1 a2)
  then show ?case
    apply (simp only: consistent_def)
    apply standard
     apply clarify
     apply (rule_tac x=s in exI)
     apply clarify
     apply simp
     apply (case_tac r)
        apply simp
       apply (simp add: collapse_def dfold_def)
       apply clarify
       apply simp
    
next
  case (Gt x1a x2)
  then show ?case sorry
next
  case (Nor G1 G2)
  then show ?case sorry
next
  case (Null x)
  then show ?case sorry
qed


lemma "consistent (medial (medial c g) g) = consistent (medial c g)"
  unfolding medial_def


lemma "subsumes c t t"
  unfolding subsumes_def
  apply standard
   apply simp
  apply standard
   apply simp
  apply standard
   defer
   apply simp
  unfolding posterior_def Let_def
  oops

end
