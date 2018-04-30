theory Constraints
imports Types CExp

begin

type_synonym constraints = "vname \<Rightarrow> cexp"

abbreviation no_regs :: constraints where
  "no_regs \<equiv> (\<lambda>x. if hd x = CHR ''r'' then Undef else Bc True)"

abbreviation empty :: constraints where
  "empty \<equiv> \<lambda>x. Bc True"

fun update :: "constraints \<Rightarrow> vname \<Rightarrow> cexp \<Rightarrow> constraints" where
  "update c k v = (\<lambda>r. if r=k then v else c r)"

fun conjoin :: "constraints \<Rightarrow> constraints \<Rightarrow> constraints" where
  "conjoin c c' = (\<lambda>r. (and (c r) (c' r)))"

abbreviation constraints_equiv :: "constraints \<Rightarrow> constraints \<Rightarrow> bool" where
  "constraints_equiv c c' \<equiv> (\<forall>r. cexp_equiv (c r) (c' r))"

abbreviation consistent :: "constraints \<Rightarrow> bool" where
  "consistent c \<equiv> (\<forall>r. satisfiable (c r) \<or> (c r) = Undef)"

abbreviation valid_constraints :: "constraints \<Rightarrow> bool" where
  "valid_constraints c \<equiv> (\<forall>r. valid (c r) \<or> (c r) = Undef)"

definition nonempty :: "constraints \<Rightarrow> bool" where
  "nonempty c = (\<not> (\<forall>r. cexp_equiv (c r) (Bc True)))"

definition constraints_simulates :: "constraints \<Rightarrow> constraints \<Rightarrow> bool" where
  "constraints_simulates c c' = (\<forall>r. cexp_simulates (c r) (c' r))"

function apply_plus :: "constraints \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> cexp" where
  "apply_plus _ (N n) (N n') = Eq (n+n')" |
  "apply_plus c (V v) (N n) = compose_plus (c v) (Eq n)" |
  "apply_plus c (N n) (V v) = compose_plus (c v) (Eq n)" |
  "apply_plus c (V v) (V va) = compose_plus (c v) (c va)" |
  "apply_plus c (N n) (Plus va vb) = compose_plus (Eq n) (apply_plus c va vb)" |
  "apply_plus c (V v) (Plus va vb) = compose_plus (c v) (apply_plus c va vb)" |
  "apply_plus c (Plus v va) (N vb) = compose_plus (apply_plus c v va) (Eq vb)" |
  "apply_plus c (Plus v va) (V vb) = compose_plus (apply_plus c v va) (c vb)" |
  "apply_plus c (Plus vb vc) (Plus v va) = compose_plus (apply_plus c vb vc) (apply_plus c v va)"
    apply pat_completeness
  by simp_all

termination apply_plus
  apply (relation "measure (\<lambda>(c, x, y). (size x) + (size y))")
  by simp_all

primrec and_insert :: "(vname \<times> cexp) list \<Rightarrow> (vname \<times> cexp) \<Rightarrow> (vname \<times> cexp) list" where
  "and_insert [] c = [c]" |
  "and_insert (h#t) c = (if fst h = fst c then ((fst h, and (snd h) (snd c))#t) else (h#(and_insert t c)))"

primrec pair_and :: "(vname \<times> cexp) list \<Rightarrow> (vname \<times> cexp) list \<Rightarrow> (vname \<times> cexp) list" where
  "pair_and [] c = c" |
  "pair_and (h#t) c = pair_and t (and_insert c h)"

fun guard2constraints :: "constraints \<Rightarrow> guard \<Rightarrow> (vname \<times> cexp) list" where
  "guard2constraints a (gexp.Not g) = map (\<lambda>x. ((fst x), not (snd x))) (guard2constraints a g)" |
  "guard2constraints a (gexp.And g g') = pair_and (guard2constraints a g) (guard2constraints a g')" |
  "guard2constraints a (gexp.Eq v (N n)) = [(v, (Eq n))]" |
  "guard2constraints a (gexp.Eq v (V vb)) = [(v, and (a vb) (a v)), (vb, and (a vb) (a v))]" |
  "guard2constraints a (gexp.Eq v (Plus (N n) (N n'))) = [(v, (Eq (n+n')))]" |
  "guard2constraints a (gexp.Eq v (Plus (V va) (N n))) = [(v, compose_plus (a va) (Eq n)), (va, compose_minus (a v) (Eq n))]" |
  "guard2constraints a (gexp.Eq v (Plus (N n) (V va))) = [(v, compose_plus (a va) (Eq n)), (va, compose_minus (a v) (Eq n))]" |
  "guard2constraints a (gexp.Eq v (Plus (V va) (V vb))) =  (case (a vb, a v, a va) of
    (Bc True, Bc True, _) \<Rightarrow> [] |
    (_, Bc True, Bc True) \<Rightarrow> [] |
    (Bc True, _, Bc True) \<Rightarrow> [] |
    (avb, Bc True, ava) \<Rightarrow> [(vb, and avb ava), (v, and avb ava), (va, and avb ava)] |
    (avb, av, Bc True) \<Rightarrow> [(vb, and avb av), (v, and avb av), (va, and avb av)]|
    (_, av, ava) \<Rightarrow> [(vb, and ava av), (v, and ava av), (va, and ava av)]
  )" |
  "guard2constraints a (gexp.Eq _ _) = []" |

  "guard2constraints a (gexp.Gt v (N n)) = [(v, Gt n)]" |
  "guard2constraints a (gexp.Gt v (V va)) = (let (cv, cva) = apply_gt (a v) (a va) in [(v, cv), (va, cva)])" |
  "guard2constraints a (gexp.Gt v (Plus (N n) (N n'))) = [(v, Gt (n+n'))]" |
  "guard2constraints a (gexp.Gt v (Plus (N n) (V va))) = (let (cv, cplus) = apply_gt (a v) (compose_plus (a va) (Eq n)) in [(v, cv), (va, compose_minus cplus (Eq n))])" |
  "guard2constraints a (gexp.Gt v (Plus (V va) (N n))) = (let (cv, cplus) = apply_gt (a v) (compose_plus (a va) (Eq n)) in [(v, cv), (va, compose_minus cplus (Eq n))])" |
  "guard2constraints a (gexp.Gt v (Plus (V va) (V vb))) =  (case (a vb, a v, a va) of
    (Bc True, Bc True, _) \<Rightarrow> [] |
    (_, Bc True, Bc True) \<Rightarrow> [] |
    (Bc True, _, Bc True) \<Rightarrow> [] |
    (avb, Bc True, ava) \<Rightarrow> (let (cv, _) = apply_gt (Bc True) (compose_minus avb ava);
                                (cvb, _) = apply_gt avb (compose_plus cv ava);
                                (cva, _) = apply_gt ava (compose_minus cvb cv) in
                                [(v, cv), (vb, cvb), (va, cva)]
                           ) |
    (avb, av, Bc True) \<Rightarrow> (let (cva, _) = apply_gt (a va) (compose_minus (a vb) (a v));
                               (cvb, _) = apply_gt avb (compose_plus av cva);
                               (cv, _) = apply_gt av (compose_minus cvb cva) in
                               [(v, cv), (vb, cvb), (va, cva)]
                          ) |
    (_, av, ava) \<Rightarrow> (let (cvb, _) = apply_gt (a vb) (compose_plus av ava);
                         (cv, _) = apply_gt av (compose_minus cvb ava);
                         (cva, _) = apply_gt ava (compose_minus cvb cv) in
                         [(v, cv), (vb, cvb), (va, cva)]
                    )
  )" |
  "guard2constraints a (gexp.Gt _ _) = []" |
  
  "guard2constraints a (gexp.Lt v (N n)) = [(v, Lt n)]" |
  "guard2constraints a (gexp.Lt v (V va)) = (let (cv, cva) = apply_lt (a v) (a va) in [(v, cv), (va, cva)])" |
  "guard2constraints a (gexp.Lt v (Plus (N n) (N n'))) = [(v, Lt (n+n'))]" |
  "guard2constraints a (gexp.Lt v (Plus (N n) (V va))) = (let (cv, cplus) = apply_lt (a v) (compose_plus (a va) (Eq n)) in [(v, cv), (va, compose_minus cplus (Eq n))])" |
  "guard2constraints a (gexp.Lt v (Plus (V va) (N n))) = (let (cv, cplus) = apply_lt (a v) (compose_plus (a va) (Eq n)) in [(v, cv), (va, compose_minus cplus (Eq n))])" |
  "guard2constraints a (gexp.Lt v (Plus (V va) (V vb))) =  (case (a vb, a v, a va) of
    (Bc True, Bc True, _) \<Rightarrow> [] |
    (_, Bc True, Bc True) \<Rightarrow> [] |
    (Bc True, _, Bc True) \<Rightarrow> [] |
    (avb, Bc True, ava) \<Rightarrow> (let (cv, _) = apply_lt (Bc True) (compose_minus avb ava);
                                (cvb, _) = apply_lt avb (compose_plus cv ava);
                                (cva, _) = apply_lt ava (compose_minus cvb cv) in
                                [(v, cv), (vb, cvb), (va, cva)]
                           ) |
    (avb, av, Bc True) \<Rightarrow> (let (cva, _) = apply_lt (a va) (compose_minus (a vb) (a v));
                               (cvb, _) = apply_lt avb (compose_plus av cva);
                               (cv, _) = apply_lt av (compose_minus cvb cva) in
                               [(v, cv), (vb, cvb), (va, cva)]
                          ) |
    (_, av, ava) \<Rightarrow> (let (cvb, _) = apply_lt (a vb) (compose_plus av ava);
                         (cv, _) = apply_lt av (compose_minus cvb ava);
                         (cva, _) = apply_lt ava (compose_minus cvb cv) in
                         [(v, cv), (vb, cvb), (va, cva)]
                    )
  )" |
  "guard2constraints a (gexp.Lt _ _) = []"

primrec pairs2constraints :: "(vname \<times> cexp) list \<Rightarrow> constraints" where
  "pairs2constraints [] = empty" |
  "pairs2constraints (h#t) = conjoin (pairs2constraints t) (\<lambda>r. if r = (fst h) then (snd h) else Bc True)"

fun apply_guard :: "constraints \<Rightarrow> guard \<Rightarrow> constraints" where
  "apply_guard a g = conjoin a (pairs2constraints (guard2constraints a g))"

fun apply_update :: "constraints \<Rightarrow> constraints \<Rightarrow> update_function \<Rightarrow> constraints" where
  "apply_update l c (v, (N n)) = update c v (Eq n)" |
  "apply_update l c (v, V vb) = update c v (l vb)" |
  "apply_update l c (v, Plus vb vc) = update c v (apply_plus l vb vc)"

primrec apply_guards :: "constraints \<Rightarrow> guard list \<Rightarrow> constraints" where
  "apply_guards c [] = c" |
  "apply_guards c (h#t) = (apply_guards (apply_guard c h) t)"

primrec apply_updates :: "constraints \<Rightarrow> constraints \<Rightarrow> update_function list \<Rightarrow> constraints" where
  "apply_updates _ c [] = c" |
  "apply_updates l c (h#t) = apply_updates l (apply_update l c h) t"

definition posterior :: "constraints \<Rightarrow> transition \<Rightarrow> constraints" where
  "posterior c t = (let c' = (apply_guards c (Guard t)) in (if consistent c' then (apply_updates c' no_regs (Updates t)) else (\<lambda>i. Bc False)))"

abbreviation can_take :: "transition \<Rightarrow> constraints \<Rightarrow> bool" where
  "can_take t c \<equiv> consistent (apply_guards c (Guard t))"

primrec posterior_n :: "nat \<Rightarrow> transition \<Rightarrow> constraints \<Rightarrow> constraints" where
  "posterior_n 0 _ c = c " |
  "posterior_n (Suc m) t c = posterior_n m t (posterior c t)"

primrec posterior_sequence :: "transition list \<Rightarrow> constraints \<Rightarrow> constraints" where
  "posterior_sequence [] c = c" |
  "posterior_sequence (h#t) c = posterior_sequence t (posterior c h)"

lemma "apply_guards empty [] = empty"
  by simp

lemma "constraints_equiv (apply_guards empty [(gexp.Eq ''i1'' (N 0))]) (\<lambda>x. if x = ''i1'' then Eq 0 else Bc True)"
  by simp

lemma constraints_simulates_symetry: "constraints_simulates c c"
  by (simp add: constraints_simulates_def)

abbreviation subsumes :: "constraints \<Rightarrow> constraints \<Rightarrow> bool" where
  "subsumes c c' \<equiv> (\<forall> r i. (ceval (c' r) i \<longrightarrow> ceval (c r) i) \<or> ((c r) = Undef))"

lemma "subsumes (\<lambda>x. Bc True) (\<lambda>x. Bc False)"
  by simp

lemma subsumes_reflexivity:  "subsumes x x"
  by simp

(* Widening the precondition and reducing nondeterminism *)
(* Guards of A imply guards of B and if the precondition of A is satisfied and we do a B then the
   posterior state of B is consistent with those of A *)
abbreviation is_generalisation :: "constraints \<Rightarrow> transition \<Rightarrow> constraints \<Rightarrow> transition \<Rightarrow> bool" where
  "is_generalisation cb b ca a \<equiv> (subsumes (apply_guards cb (Guard b)) (apply_guards ca (Guard a))) \<and> (subsumes (posterior ca a) (posterior (apply_guards cb (Guard a)) b))"

end