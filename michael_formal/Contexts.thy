subsection \<open>Contexts\<close>
text\<open>
This theory defines contexts as a way of relating possible constraints on register values to
observable output. We then use contexts to extend the idea of transition subsumption to EFSM
transitions with register update functions.
\<close>

theory Contexts
  imports
    EFSM GExp "efsm-exp.CExp"
begin

type_synonym "context" = "vname \<Rightarrow> cexp"

abbreviation empty ("\<lbrakk>\<rbrakk>") where
  "empty \<equiv> (\<lambda>x. (case x of R n \<Rightarrow> Undef | _ \<Rightarrow> Bc True))"
syntax
  "_updbind" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind" ("(2_ \<mapsto>/ _)")
  "_Context" :: "updbinds \<Rightarrow> 'a"      ("\<lbrakk>_\<rbrakk>")
translations
  "_Update f (_updbinds b bs)" \<rightleftharpoons> "_Update (_Update f b) bs"
  "_Context ms" == "_Update \<lbrakk>\<rbrakk> ms"
  "_Context (_updbinds b bs)" \<rightleftharpoons> "_Update (_Context b) bs"

lemma empty_not_false[simp]: "cexp.Bc False \<noteq> \<lbrakk>\<rbrakk> i"
  apply (case_tac i)
  by simp_all

fun update :: "context \<Rightarrow> vname \<Rightarrow> cexp \<Rightarrow> context" where
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
  by (simp add: cexp_equiv_def)

lemma context_equiv_symmetric: "context_equiv x y \<Longrightarrow> context_equiv y x"
  apply (simp add: context_equiv_def)
  apply (rule allI)
  by (simp add: cexp_equiv_def)

lemma context_equiv_transitive: "context_equiv x y \<and> context_equiv y z \<Longrightarrow> context_equiv x z"
  apply (simp add: context_equiv_def)
  apply (rule allI)
  by (simp add: cexp_equiv_def)

fun cexp2gexp :: "vname \<Rightarrow> cexp \<Rightarrow> gexp" where
  "cexp2gexp _ (Bc b) = gexp.Bc b" |
  "cexp2gexp a Undef = gexp.Bc False" |
  "cexp2gexp a (Lt v) = gexp.Lt a (L v)" |
  "cexp2gexp a (Gt v) = gexp.Gt a (L v)" |
  "cexp2gexp a (Eq v) = gexp.Eq a (L v)" |
  "cexp2gexp a (Not v) = gNot (cexp2gexp a v)" |
  "cexp2gexp a (And v va) = gAnd (cexp2gexp a v) (cexp2gexp a va)"

definition consistent :: "context \<Rightarrow> bool" where (* Is there a variable evaluation which can satisfy all of the context? *)
  "consistent c \<equiv> \<exists>s. \<forall>r. (c r) = Undef \<or> (gval (cexp2gexp r (c r)) s = Some True)"

lemma possible_false_not_consistent: "\<exists>r. c r = Bc False \<Longrightarrow> \<not> consistent c"
  unfolding consistent_def
  apply simp
  apply (rule allI)
  apply clarify
  apply (rule_tac x=r in exI)
  by simp

definition valid_context :: "context \<Rightarrow> bool" where (* Is the context satisfied in all variable evaluations? *)
  "valid_context c \<equiv> \<forall>s. \<forall>r. (c r) = Undef \<or> (gval (cexp2gexp r (c r)) s = Some True)"

theorem consistent_empty_1: "empty r = Undef \<or> empty r = Bc True"
  apply (cases r)
  prefer 2
    apply (case_tac x2)
  by simp_all

theorem consistent_empty_2: "(\<forall>r. c r = Bc True \<or> c r = Undef) \<longrightarrow> consistent c"
  apply (simp add: consistent_def)
  by force

lemma consistent_empty_3: "(\<forall>r. empty r = Bc True \<or> empty r = Undef) \<longrightarrow> consistent empty"
  apply (insert consistent_empty_2)
  by simp

lemma consistent_empty_4: "\<lbrakk>\<rbrakk> r = Undef \<or> gval (cexp2gexp r (\<lbrakk>\<rbrakk> r)) c = Some True"
  using consistent_empty_1 by force

lemma consistent_empty [simp]: "consistent empty"
  apply (insert consistent_empty_1 consistent_empty_3)
  by auto

lemma cexp2gexp_double_neg: "gexp_equiv (cexp2gexp r (Not (Not x))) (cexp2gexp r x)"
  apply (simp add: gexp_equiv_def)
  apply (rule allI)
  apply (case_tac "gval (cexp2gexp r x) s")
   apply (simp)
  by (simp)

lemma gval_cexp2gexp_double_neg: "gval (cexp2gexp r (Not (Not x))) s = gval (cexp2gexp r x) s"
  using cexp2gexp_double_neg gexp_equiv_def by blast

primrec and_insert :: "(vname \<times> cexp) list \<Rightarrow> (vname \<times> cexp) \<Rightarrow> (vname \<times> cexp) list" where
  "and_insert [] c = [c]" |
  "and_insert (h#t) c = (if fst h = fst c then ((fst h, and (snd h) (snd c))#t) else (h#(and_insert t c)))"

primrec pair_and :: "(vname \<times> cexp) list \<Rightarrow> (vname \<times> cexp) list \<Rightarrow> (vname \<times> cexp) list" where
  "pair_and [] c = c" |
  "pair_and (h#t) c = pair_and t (and_insert c h)"

fun context_eval :: "aexp \<Rightarrow> context \<Rightarrow> cexp" where
  "context_eval (L n) _ = Eq n" |
  "context_eval (V v) c = c v" |
  "context_eval (Plus x y) c = compose_plus (context_eval x c) (context_eval y c)" |
  "context_eval (Minus x y) c = compose_minus (context_eval x c) (context_eval y c)"

fun make_gt :: "cexp \<Rightarrow> cexp" where
  "make_gt Undef = Undef" |
  "make_gt (Not Undef) = Bc True" |
  "make_gt (Bc b) = Bc b" |
  "make_gt (Not (Bc b)) = Bc (\<not> b)" |
  "make_gt (Eq v) = Gt v" |
  "make_gt (Neq v) = Bc True" |
  "make_gt (Geq v) = Gt v" |
  "make_gt (Gt v) = Gt v" |
  "make_gt (Lt v) = Bc True" |
  "make_gt (Leq v) = Bc True" |
  "make_gt (Not (Not v)) = make_gt v" |
  "make_gt (And v1 v2) = and (make_gt v1) (make_gt v2)" |
  "make_gt (Not (And v1 v2)) = Or (make_gt (Not v1)) (make_gt (Not v2))"

fun make_lt :: "cexp \<Rightarrow> cexp" where
  "make_lt Undef = Undef" |
  "make_lt (Not Undef) = Bc True" |
  "make_lt (Bc b) = Bc b" |
  "make_lt (Not (Bc b)) = Bc (\<not> b)" |
  "make_lt (Eq v) = Lt v" |
  "make_lt (Neq v) = Bc True" |
  "make_lt (Geq v) = Bc True" |
  "make_lt (Gt v) = Bc True" |
  "make_lt (Lt v) = Lt v" |
  "make_lt (Leq v) = Lt v" |
  "make_lt (Not (Not v)) = make_gt v" |
  "make_lt (And v1 v2) = and (make_gt v1) (make_gt v2)" |
  "make_lt (Not (And v1 v2)) = Or (make_gt (Not v1)) (make_gt (Not v2))"

fun guard2pairs :: "context \<Rightarrow> guard \<Rightarrow> (vname \<times> cexp) list" where
  "guard2pairs a (gexp.Bc True) = []" |
  "guard2pairs a (gexp.Bc False) = [(I 0, Bc False)]" |
  "guard2pairs a (gexp.Null v) = [(v, Undef)]" |
  "guard2pairs a (gexp.Eq v vb) = [(v, context_eval vb a)]" |
  "guard2pairs a (gexp.Gt v vb) = [(v, make_gt (context_eval vb a))]" |
  "guard2pairs a (gexp.Lt v vb) = [(v, make_lt (context_eval vb a))]" |
  "guard2pairs a (Nor v va) = (pair_and (map (\<lambda>x. ((fst x), not (snd x))) (guard2pairs a v))
                                        (map (\<lambda>x. ((fst x), not (snd x))) (guard2pairs a va)))"

fun pairs2context :: "(vname \<times> cexp) list \<Rightarrow> context \<Rightarrow> context" where
  "pairs2context [] c = c" |
  \<comment>\<open>This deals with literal guard (Bc False) which doesn't go through guard2pairs well\<close>
  "pairs2context ((_, Bc False)#t) c = (\<lambda>r. Bc False)" |
  "pairs2context (h#t) c = (let c' = (pairs2context t c) in (\<lambda>r. if r = (fst h) then and (c' r) (snd h) else c' r))"

fun context_nor :: "cexp option \<Rightarrow> cexp option \<Rightarrow> cexp option" where
  "context_nor None None = None" |
  "context_nor None (Some c) = Some (not c)" |
  "context_nor (Some c) None = Some (not c)" |
  "context_nor (Some c1) (Some c2) = Some (not (Or c1 c2))"

fun guard2context :: "guard \<Rightarrow> context \<Rightarrow> (vname \<Rightarrow> cexp option)" where
  "guard2context (gexp.Bc True) c = (\<lambda>x. None)" |
  "guard2context (gexp.Bc False) c = (\<lambda>x. Some (Bc False))" |
  "guard2context (gexp.Eq v a) c = (\<lambda>x. if x = v then Some (context_eval a c) else None)" |
  "guard2context (gexp.Gt v a) c = (\<lambda>x. if x = v then Some (make_gt (context_eval a c)) else None)" |
  "guard2context (gexp.Lt v a) c = (\<lambda>x. if x = v then Some (make_lt (context_eval a c)) else None)" |
  "guard2context (Nor g1 g2) c = (\<lambda>x. context_nor (guard2context g1 c x) (guard2context g2 c x))" |
  "guard2context (Null v) c = (\<lambda>x. if x = v then Some Undef else None)"

(*fun medial :: "context \<Rightarrow> guard list \<Rightarrow> context" where
  "medial c [] = c" |
  "medial c ((gexp.Bc True)#t) = medial c t"|
  "medial c ((gexp.Bc False)#t) = (\<lambda>r. Bc False)"|
  "medial c l = pairs2context (concat (map (\<lambda>g. guard2pairs c g) l)) c"*)

fun medial :: "context \<Rightarrow> guard list \<Rightarrow> context" where
  "medial c [] = c" |
  "medial c (h#t) = conjoin (\<lambda>x. case guard2context h c x of None \<Rightarrow> \<lbrakk>\<rbrakk> x | Some y \<Rightarrow> y) (medial c t)"

primrec apply_updates :: "context \<Rightarrow> context \<Rightarrow> update_function list \<Rightarrow> context" where
  "apply_updates _ c [] = c" |
  "apply_updates l c (h#t) = apply_updates l (update l (fst h) (context_eval (snd h) l)) t"

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

definition posterior :: "context \<Rightarrow> transition \<Rightarrow> context" where (* Corresponds to Algorithm 1 in Foster et. al. *)
  "posterior c t = (let c' = (medial c (Guard t)) in (if consistent c' then (apply_updates c' c (Updates t)) else (\<lambda>i. Bc False)))"

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

(* Does t2 subsume t1? *)
definition subsumes :: "context \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> bool" where (* Corresponds to Algorithm 2 in Foster et. al. *)
  "subsumes c t2 t1 \<equiv> (\<forall>r i. (cval (medial c (Guard t1) r) i = Some True) \<longrightarrow> (cval (medial c (Guard t2) r) i) = Some True) \<and>
                      (\<forall> i r. apply_guards (Guard t1) (join_ir i r) \<longrightarrow> apply_outputs (Outputs t1) (join_ir i r) = apply_outputs (Outputs t2) (join_ir i r)) \<and>
                      (\<forall>r i. cval (posterior (medial c (Guard t1)) t2 r) i = Some True \<longrightarrow> (cval (posterior c t1 r) i = Some True) \<or> (posterior c t1 r) = Undef) \<and>
                      (consistent (posterior c t1) \<longrightarrow> consistent (posterior c t2))"

definition anterior_context :: "transition_matrix \<Rightarrow> trace \<Rightarrow> context" where
 "anterior_context e t = posterior_sequence \<lbrakk>\<rbrakk> e 0 <> t"

(* Does t1 subsume t2 in all possible anterior contexts? *)
(* For every path which gets us to the problem state, does t1 subsume t2 in the resulting context *)
definition directly_subsumes :: "transition_matrix \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> bool" where
  "directly_subsumes e s t1 t2 = (\<forall>p. (gets_us_to s e 0 <>  p) \<longrightarrow> subsumes (anterior_context e p) t1 t2)"

lemma context_equiv_same_undef: "c i = Undef \<Longrightarrow> c' i = cexp.Bc True \<Longrightarrow> \<not> context_equiv c c'"
  apply (simp add: context_equiv_def cexp_equiv_def)
  by force

lemma context_equiv_undef: "context_equiv c c' \<Longrightarrow> ((c i) = Undef) = ((c' i) = Undef)"
  by (simp add: cexp_equiv_def context_equiv_def)

lemma gexp_equiv_cexp_not_true:  "gexp_equiv (cexp2gexp a (Not (Bc True))) (gexp.Bc False)"
  by (simp add: gexp_equiv_def)

lemma gexp_equiv_cexp_not_false:  "gexp_equiv (cexp2gexp a (Not (Bc False))) (gexp.Bc True)"
  by (simp add: gexp_equiv_def)

lemma geq_to_ge: "Geq x = c r \<Longrightarrow> (cexp2gexp r (c r)) = Ge r (L x)"
  by (metis cexp2gexp.simps(3) cexp2gexp.simps(6))

lemma leq_to_le: "Leq x = c r \<Longrightarrow> (cexp2gexp r (c r)) = Le r (L x)"
  by (metis cexp2gexp.simps(4) cexp2gexp.simps(6))

lemma lt_to_lt: "Lt x = c r \<Longrightarrow> (cexp2gexp r (c r)) = gexp.Lt r (L x)"
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

lemma cval_empty_r_neq_none[simp]: "cval (\<lbrakk>\<rbrakk> r) i \<noteq> None"
  apply (cases r)
  by auto

lemma gand_gAnd_equiv: "a \<noteq> gexp.Bc True \<Longrightarrow> a \<noteq> gexp.Bc False \<Longrightarrow> gand (gexp.Bc False) a = gAnd (gexp.Bc False) a"
  apply (case_tac a)
  by auto

lemma "consistent (medial c g) \<Longrightarrow> consistent (medial (medial c g) g)"
proof (induct g)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    apply simp
    sorry
    

    

qed



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
