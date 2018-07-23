theory Contexts
imports EFSM CExp

begin

type_synonym "context" = "aexp \<Rightarrow> cexp"

abbreviation empty ("\<lbrakk>\<rbrakk>") where
  "empty \<equiv> (\<lambda>x. case x of
    (V v) \<Rightarrow> (case v of R n \<Rightarrow> Undef | I n \<Rightarrow> Bc True) |
    _ \<Rightarrow> Bc True
  )"
syntax 
  "_updbind" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind"             ("(2_ \<mapsto>/ _)")
  "_Context" :: "updbinds \<Rightarrow> 'a" ("\<lbrakk>_\<rbrakk>")
translations
  "_Update f (_updbinds b bs)" \<rightleftharpoons> "_Update (_Update f b) bs"
  "_Context ms" == "_Update \<lbrakk>\<rbrakk> ms"
  "_Context (_updbinds b bs)" <= "_Update (_Context b) bs"

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

definition context_equiv :: "context \<Rightarrow> context \<Rightarrow> bool" where
  "context_equiv c c' \<equiv> (\<forall>r. cexp_equiv (get c r) (get c' r))"

fun cexp2gexp :: "aexp \<Rightarrow> cexp \<Rightarrow> gexp" where
  "cexp2gexp _ (Bc b) = gexp.Bc b" |
  "cexp2gexp a Undef = gexp.Bc False" |
  "cexp2gexp a (Lt (Str va)) = gexp.Bc False" |
  "cexp2gexp a (Gt (Str va)) = gexp.Bc False" |
  "cexp2gexp a (Eq v) = gexp.Eq a (L v)" |
  "cexp2gexp a (Lt (Num v)) = gexp.Lt a (L (Num v))" |
  "cexp2gexp a (Gt (Num v)) = gexp.Gt a (L (Num v))" |
  "cexp2gexp a (Not v) = gNot (cexp2gexp a v)" |
  "cexp2gexp a (And v va) = gAnd (cexp2gexp a v) (cexp2gexp a va)"
  
(* Is there a variable evaluation which can satisfy all of the context? *)
definition consistent :: "context \<Rightarrow> bool" where
  "consistent c \<equiv> \<exists>s. \<forall>r. (c r) = Undef \<or> (gval (cexp2gexp r (c r)) s = Some True)"

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

definition valid_context :: "context \<Rightarrow> bool" where
  "valid_context c \<equiv> \<forall>s. \<forall>r. (c r) = Undef \<or> (gval (cexp2gexp r (c r)) s = Some True)"

primrec and_insert :: "(aexp \<times> cexp) list \<Rightarrow> (aexp \<times> cexp) \<Rightarrow> (aexp \<times> cexp) list" where
  "and_insert [] c = [c]" |
  "and_insert (h#t) c = (if fst h = fst c then ((fst h, and (snd h) (snd c))#t) else (h#(and_insert t c)))"

primrec pair_and :: "(aexp \<times> cexp) list \<Rightarrow> (aexp \<times> cexp) list \<Rightarrow> (aexp \<times> cexp) list" where
  "pair_and [] c = c" |
  "pair_and (h#t) c = pair_and t (and_insert c h)"

fun guard2context :: "context \<Rightarrow> guard \<Rightarrow> (aexp \<times> cexp) list" where
  "guard2context a (gexp.Bc v) = [(L (Num 0), Bc v)]" |
  "guard2context a (gexp.Null v) = [(V v, Undef)]" |
  
  "guard2context a (gexp.Eq (L n) (L n')) =  [(L n, Eq n')]" |
  "guard2context a (gexp.Gt (L n) (L n')) =  [(L n, Gt n')]" |
  "guard2context a (gexp.Lt (L n) (L n')) =  [(L n, Lt n')]" |

  "guard2context a (gexp.Eq v (L n)) = [(v, Eq n)]" |
  "guard2context a (gexp.Eq (L n) v) = [(v, Eq n)]" |
  "guard2context a (gexp.Eq v vb) = [(v, get a vb), (vb, get a v)]" |
  
  "guard2context a (gexp.Gt v (L n)) = [(v, (Gt n))]" |
  "guard2context a (gexp.Gt (L n) v) = [(v, (Lt n))]" |
  "guard2context a (gexp.Gt v vb) = (let (cv, cvb) = apply_gt (get a v) (get a vb) in [(v, cv), (vb, cvb)])" |

  "guard2context a (gexp.Lt v (L n)) = [(v, (Lt n))]" |
  "guard2context a (gexp.Lt (L n) v) = [(v, (Gt n))]" |
  "guard2context a (gexp.Lt v vb) = (let (cv, cvb) = apply_lt (get a v) (get a vb) in [(v, cv), (vb, cvb)])" |
  "guard2context a (Nor v va) = (pair_and (map (\<lambda>x. ((fst x), not (snd x))) (guard2context a v)) (map (\<lambda>x. ((fst x), not (snd x))) (guard2context a va)))"

primrec pairs2context :: "(aexp \<times> cexp) list \<Rightarrow> context" where
  "pairs2context [] = (\<lambda>i. Bc True)" |
  "pairs2context (h#t) = conjoin (pairs2context t) (\<lambda>r. if r = (fst h) then (snd h) else Bc True)"

fun apply_guard :: "context \<Rightarrow> guard \<Rightarrow> context" where
  "apply_guard a g = conjoin a (pairs2context (guard2context a g))"

fun apply_update :: "context \<Rightarrow> context \<Rightarrow> update_function \<Rightarrow> context" where
  "apply_update l c (v, (L n)) = update c (V v) (Eq n)" |
  "apply_update l c (v, V vb) = update c (V v) (l (V vb))" |
  "apply_update l c (v, Plus vb vc) = update c (V v) (compose_plus (get l vb) (get l vc))" |
  "apply_update l c (v, Minus vb vc) = update c (V v) (compose_minus (get l vb) (get l vc))"

primrec medial :: "context \<Rightarrow> guard list \<Rightarrow> context" where
  "medial c [] = c" |
  "medial c (h#t) = (medial (apply_guard c h) t)"

primrec apply_updates :: "context \<Rightarrow> context \<Rightarrow> update_function list \<Rightarrow> context" where
  "apply_updates _ c [] = c" |
  "apply_updates l c (h#t) = apply_updates l (apply_update l c h) t"

definition posterior :: "context \<Rightarrow> transition \<Rightarrow> context" where
  "posterior c t = (let c' = (medial c (Guard t)) in (if consistent c' then (apply_updates c' \<lbrakk>\<rbrakk> (Updates t)) else (\<lambda>i. Bc False)))"

definition can_take :: "transition \<Rightarrow> context \<Rightarrow> bool" where
  "can_take t c \<equiv> consistent (medial c (Guard t))"

primrec posterior_n :: "nat \<Rightarrow> transition \<Rightarrow> context \<Rightarrow> context" where
  "posterior_n 0 _ c = c " |
  "posterior_n (Suc m) t c = posterior_n m t (posterior c t)"

primrec posterior_sequence :: "transition list \<Rightarrow> context \<Rightarrow> context" where
  "posterior_sequence [] c = c" |
  "posterior_sequence (h#t) c = posterior_sequence t (posterior c h)"

lemma medial_empty: "medial empty [] = empty"
  by simp

(* Widening the precondition and reducing nondeterminism *)
(* t2 subsumes t1 *)
definition subsumes :: "context \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> bool" where
  "subsumes c t2 t1 \<equiv> (\<forall>r i. ceval (medial c (Guard t1) r) i \<longrightarrow> ceval (medial c (Guard t2) r) i) \<and>
                      (\<forall> i r. apply_guards (Guard t1) (join_ir i r) \<longrightarrow> apply_outputs (Outputs t1) (join_ir i r) = apply_outputs (Outputs t2) (join_ir i r)) \<and>
                      (\<forall>r i. ceval (posterior (medial c (Guard t1)) t2 r) i \<longrightarrow> (ceval (posterior c t1 r) i) \<or> (posterior c t1 r) = Undef) \<and>
                      (consistent (posterior c t1) \<longrightarrow> consistent (posterior c t2))"
end