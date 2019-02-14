section\<open>Subsumption and Generalisation\<close>
text\<open>
We now define a language of constraint expressions to express restrictions on the known values of
registers which can be grouped into \emph{contexts} which are used to extend the idea of transition
subsumption \cite{lorenzoli2008} to transitions with update functions. This forms the
underpinning of an EFSM inference technique based on transition merging.
\<close>
subsection \<open>Constraint Expressions\<close>
text\<open>
This theory defines a language to express constraints on register values. Base restrictions are
undefined, unrestricted, inconsistent, equal to a value, less than a value, greater than a value.
Expressions may be combined using either negation or conjunction to form compound expressions. We
also define syntax hacks for the relations less than or equal to, greater than or equal to, and
not equal to as well as the expression of logical ``or'' in terms of negation and conjunction.
\<close>

theory CExp
  imports AExp Option_Logic GExp
begin

datatype cexp = Undef | Bc bool | Eq "value" | Lt "value" | Gt "value" | Not cexp | And cexp cexp

fun "and" :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "and (Bc True) x = x" |
  "and x (Bc True) = x" |
  "and c c' = (if c = c' then c else And c c')"

fun "not" :: "cexp \<Rightarrow> cexp" where
  "not c = (case c of
    Bc True \<Rightarrow> Bc False |
    Bc False \<Rightarrow> Bc True |
    Not x \<Rightarrow> x |
    c \<Rightarrow> Not c
  )"

abbreviation Leq :: "value \<Rightarrow> cexp" where
  "Leq v \<equiv> Not (Gt v)"

abbreviation Geq :: "value \<Rightarrow> cexp" where
  "Geq v \<equiv> Not (Lt v)"

abbreviation Neq :: "value \<Rightarrow> cexp" where
  "Neq v \<equiv> Not (Eq v)"

abbreviation Or :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "Or v va \<equiv> not (and (not v) (not va))"

text \<open>
This function takes two cexps and tries to apply restrictions such that the first argument is
greater than the second. The return value is a pair of the first and second inputs with their
respective increased restrictions.
\<close>
fun apply_gt :: "cexp \<Rightarrow> cexp \<Rightarrow> (cexp \<times> cexp)" where (* This takes a LONG time to prove *)
  "apply_gt Undef v = (Bc False, v)" |
  "apply_gt v Undef = (v, Bc False)" |
  "apply_gt (Bc False) v = (Bc False, v)" |
  "apply_gt v (Bc False) = (v, Bc False)" |
  "apply_gt v (Not (Bc True)) = (v, Bc False)" |
  "apply_gt (Not (Bc True)) v = (Bc False, v)" |
  "apply_gt v (Not (Bc False)) = apply_gt v (Bc True)" |
  "apply_gt (Not (Bc False)) v = apply_gt (Bc True) v" |
  "apply_gt v (Not (Not vb)) = apply_gt v vb" |
  "apply_gt (Not (Not vb)) v = apply_gt vb v" |

  "apply_gt v (And va vb) = (and (fst (apply_gt v va)) (fst (apply_gt v vb)), and (snd (apply_gt v va)) (snd (apply_gt v vb)))" |
  "apply_gt (And va vb) v = (and (fst (apply_gt va v)) (fst (apply_gt vb v)), and (snd (apply_gt va v)) (snd (apply_gt vb v)))" |
  "apply_gt v (Not (And va vb)) = (not (and (fst (apply_gt v va)) (fst (apply_gt v vb))), not (and (snd (apply_gt v va)) (snd (apply_gt v vb))))" |
  "apply_gt (Not (And va vb)) v = (not (and (fst (apply_gt va v)) (fst (apply_gt vb v))), not (and (snd (apply_gt va v)) (snd (apply_gt vb v))))" |

  "apply_gt (Bc True) (Bc True) = (Bc True, Bc True)" |
  "apply_gt (Eq v) (Bc True)   = (Eq v, Lt v)" |
  "apply_gt (Lt v) (Bc True)   = (Lt v, Lt v)" |
  "apply_gt (Leq va) (Bc True) = (Leq va, Lt va)" |

  "apply_gt (Bc True) (Eq v) = (Gt v, Eq v)" |
  "apply_gt (Bc True) (Geq v) = (Gt v, Geq v)" |
  "apply_gt (Bc True) (Gt v) = (Gt v, Gt v)" |
  "apply_gt (Bc True) v = (Bc True, v)" |

  "apply_gt (Lt v) (Gt va) = (and (Lt v)  (Gt va), and (Gt va) (Lt v))" |
  "apply_gt v (Leq vb) = (and v (Gt vb), Leq vb)" |
  "apply_gt v (Gt va) =  (and v (Gt va), Gt va)" |
  "apply_gt v (Lt va) = (and v (Geq va), Lt va)" |
  "apply_gt (Lt v)  (Neq vb) = (Lt v,  and (Neq vb) (Lt v))" |
  "apply_gt (Leq v) (Neq vb) = (Leq v, and (Neq vb) (Lt v))" |

  "apply_gt (Eq v) va = (Eq v, and va (Lt v))" |
  "apply_gt v (Eq va) = (and v (Gt va), Eq va)" |

  "apply_gt (Lt v) (Geq va) = (and (Lt v) (Gt va), and (Geq va) (Lt v))" |
  "apply_gt v      (Geq vb) = (and v (Gt vb), Geq vb)" |
  "apply_gt v va = (v, va)"

fun apply_lt :: "cexp \<Rightarrow> cexp \<Rightarrow> (cexp \<times> cexp)" where
  "apply_lt a b = (let (ca, cb) = (apply_gt b a) in (cb, ca))"

fun cexp2gexp :: "aexp \<Rightarrow> cexp \<Rightarrow>  gexp" where
  "cexp2gexp _ (Bc b) = gexp.Bc b" |
  "cexp2gexp a Undef = Null a" |
  "cexp2gexp a (Lt v) = gexp.Gt (L v) a" |
  "cexp2gexp a (Gt v) = gexp.Gt a (L v)" |
  "cexp2gexp a (Eq v) = gexp.Eq a (L v)" |
  "cexp2gexp a (Not v) = gNot (cexp2gexp a v)" |
  "cexp2gexp a (And v va) = gAnd (cexp2gexp a v) (cexp2gexp a va)"

definition cval :: "cexp \<Rightarrow> aexp \<Rightarrow> (datastate \<Rightarrow> bool option)" where
  "cval c a = gval (cexp2gexp a c)"

definition valid :: "cexp \<Rightarrow> bool" where (* Is cexp "c" satisfied under all "i" values? *)
  "valid c \<equiv> (\<forall> a s. cval c a s = Some True)"

definition satisfiable :: "cexp \<Rightarrow> bool" where (* Is there some value of "i" which satisfies "c"? *)
  "satisfiable c \<equiv> (\<exists> a s. cval c a s = Some True)"

fun compose_plus :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "compose_plus x y = (if satisfiable x \<and> satisfiable y then (if valid x \<or> valid y then Bc True else (case (x, y) of
  ((Eq v), (Eq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Eq c') |
  ((Eq v), (Lt va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Lt c') |
  ((Eq v), (Gt va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Gt c') |
  ((Eq v), (Leq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Leq c') |
  ((Eq v), (Geq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Geq c') |
  ((Lt v), (Eq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Lt c') |
  ((Lt v), (Lt va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Lt c') |
  ((Lt v), (Leq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Lt c') |
  ((Gt v), (Eq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Gt c') |
  ((Gt v), (Gt va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Gt c') |
  ((Gt v), (Geq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Gt c') |
  ((Leq v), (Eq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Leq c') |
  ((Leq v), (Lt va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow>Lt c') |
  ((Leq v), (Leq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Leq c') |
  ((Geq v), (Eq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Geq c') |
  ((Geq v), (Gt va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Gt c') |
  ((Geq v), (Geq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Geq c') |
  ((Neq _), _) \<Rightarrow> Bc True |
  (_, (Neq _)) \<Rightarrow> Bc True |
  ((Not (Not v)), va) \<Rightarrow> compose_plus v va |
  (v, (Not (Not va))) \<Rightarrow> compose_plus v va |
  ((And v va), vb) \<Rightarrow> and (compose_plus v vb) (compose_plus va vb) |
  (v, (And va vb)) \<Rightarrow> and (compose_plus v va) (compose_plus v vb) |
  ((Not (And v va)), vb) \<Rightarrow> not (and (compose_plus v vb) (compose_plus va vb)) |
  (v, (Not (And va vb))) \<Rightarrow> not (and (compose_plus v va) (compose_plus v vb)) |
  _ \<Rightarrow> Bc True
  )) else Bc False)"

fun compose_minus :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "compose_minus x y = (if satisfiable x \<and> satisfiable y then (if valid x \<or> valid y then Bc True else (case (x, y) of
  ((Eq v), (Eq va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Eq c') |
  ((Eq v), (Lt va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Lt c') |
  ((Eq v), (Gt va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Gt c') |
  ((Eq v), (Leq va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Leq c') |
  ((Eq v), (Geq va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Geq c') |
  ((Lt v), (Eq va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Lt c') |
  ((Lt v), (Lt va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Lt c') |
  ((Lt v), (Leq va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Lt c') |
  ((Gt v), (Eq va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Gt c') |
  ((Gt v), (Gt va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Gt c') |
  ((Gt v), (Geq va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Gt c') |
  ((Leq v), (Eq va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Leq c') |
  ((Leq v), (Lt va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Lt c') |
  ((Leq v), (Leq va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Leq c') |
  ((Geq v), (Eq va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Geq c') |
  ((Geq v), (Gt va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Gt c') |
  ((Geq v), (Geq va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Geq c') |
  ((Neq _), _) \<Rightarrow> Bc True |
  (_, (Neq _)) \<Rightarrow> Bc True |
  ((Not (Not v)), va) \<Rightarrow> compose_minus v va |
  (v, (Not (Not va))) \<Rightarrow> compose_minus v va |
  ((And v va), vb) \<Rightarrow> and (compose_minus v vb) (compose_minus va vb) |
  (v, (And va vb)) \<Rightarrow> and (compose_minus v va) (compose_minus v vb) |
  ((Not (And v va)), vb) \<Rightarrow> not (and (compose_minus v vb) (compose_minus va vb)) |
  (v, (Not (And va vb))) \<Rightarrow> not (and (compose_minus v va) (compose_minus v vb)) |
  _ \<Rightarrow> Bc True
  )) else Bc False)"

lemma valid_implies_satisfiable: "valid c \<Longrightarrow> satisfiable c"
  by (simp add: valid_def satisfiable_def)

definition cexp_equiv :: "cexp \<Rightarrow> cexp \<Rightarrow> bool" where
  "cexp_equiv c c' \<equiv> (\<forall>a s. cval c a s = cval c' a s)"

lemma cexp_equiv_reflexive: "cexp_equiv x x"
  by (simp add: cexp_equiv_def gexp_equiv_reflexive)

lemma gNegate: "gexp_equiv (gNot g) (gexp.Bc True) = gexp_equiv g (gexp.Bc False)"
proof
  show "gexp_equiv (gNot g) (gexp.Bc True) \<Longrightarrow> gexp_equiv g (gexp.Bc False)"
  proof(induct g)
    case (Bc x)
    then show ?case
      by (simp add: gexp_equiv_def gval.simps)
  next
    case (Eq x1a x2)
    then show ?case
      by (simp add: gexp_equiv_def gval.simps)
  next
    have test: "\<And>x1a x2 s. maybe_not
              (case MaybeBoolInt (\<lambda>x y. y < x) (aval x1a s) (aval x2 s) of None \<Rightarrow> None
               | Some a \<Rightarrow> case MaybeBoolInt (\<lambda>x y. y < x) (aval x1a s) (aval x2 s) of None \<Rightarrow> None | Some b \<Rightarrow> Some (a \<or> b)) =
             Some True \<Longrightarrow>
         MaybeBoolInt (\<lambda>x y. y < x) (aval x1a s) (aval x2 s) = Some False"
  apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval x1a s) (aval x2 s)")
  by auto
    case (Gt x1a x2)
    then show ?case
      apply (simp add: gexp_equiv_def)
      apply clarify
      using test
      by (simp add: gval.simps)
  next
    have test: "\<And>g1 s g2. maybe_not
              (case maybe_not (case gval g1 s of None \<Rightarrow> None | Some a \<Rightarrow> case gval g2 s of None \<Rightarrow> None | Some b \<Rightarrow> Some (a \<or> b)) of
               None \<Rightarrow> None
               | Some a \<Rightarrow>
                   case maybe_not (case gval g1 s of None \<Rightarrow> None | Some a \<Rightarrow> case gval g2 s of None \<Rightarrow> None | Some b \<Rightarrow> Some (a \<or> b)) of
                   None \<Rightarrow> None | Some b \<Rightarrow> Some (a \<or> b)) =
             Some True \<Longrightarrow>
         maybe_not (case gval g1 s of None \<Rightarrow> None | Some a \<Rightarrow> case gval g2 s of None \<Rightarrow> None | Some b \<Rightarrow> Some (a \<or> b)) = Some False"
  apply (case_tac "gval g1 s")
   apply simp+
  apply (case_tac "gval g2 s")
  by auto
    case (Nor g1 g2)
    then show ?case
      apply (simp add: gexp_equiv_def)
      apply clarify
      using test
      by (simp add: gval.simps)
  next
    case (Null x)
    then show ?case
      by (simp add: gexp_equiv_def gval.simps)
  qed
  show "gexp_equiv g (gexp.Bc False) \<Longrightarrow> gexp_equiv (gNot g) (gexp.Bc True)"
    by (simp add: gexp_equiv_def gval.simps)
qed

lemma cexp_equiv_valid: "valid c \<longrightarrow> cexp_equiv c (Bc True)"
  by (simp add: valid_def cexp_equiv_def cval_def gval.simps)

declare gval.simps [simp]
lemma cexp_equiv_redundant_and: "cexp_equiv (and c (and c c')) (and c c')"
  apply (simp add: cexp_equiv_def gexp_equiv_def cval_def)
  apply clarify
proof(induct c rule: cexp2gexp.induct)
  case (1 uu b)
  then show ?case
    apply (cases b)
     apply simp
    apply (case_tac c')
          apply simp
         apply (case_tac x2)
          apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval a s)")
        apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x5)")
       apply simp+
     apply (case_tac "gval (cexp2gexp a x6) s")
      apply simp+
    apply (case_tac "gval (cexp2gexp a x71) s")
     apply simp+
    apply (case_tac "gval (cexp2gexp a x72) s")
    by auto
next
  case (2 b)
  then show ?case
    apply (cases c')
          apply simp
         apply (case_tac x2)
          apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval a s)")
        apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x5)")
       apply simp+
     apply (case_tac "gval (cexp2gexp a x6) s")
      apply simp+
    apply (case_tac "gval (cexp2gexp a x71) s")
     apply simp+
    apply (case_tac "gval (cexp2gexp a x72) s")
    by auto
next
  case (3 b v)
  then show ?case
    apply (cases c')
          apply simp
          apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some v) (aval a s)")
           apply simp+
         apply (case_tac x2)
          apply simp+
         apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some v) (aval a s)")
          apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some v) (aval a s)")
         apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some v) (aval a s)")
        apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval a s)")
        apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some v) (aval a s)")
       apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x5)")
       apply simp+
     apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some v) (aval a s)")
      apply simp+
     apply (case_tac "gval (cexp2gexp a x6) s")
      apply simp+
    apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some v) (aval a s)")
     apply simp+
    apply (case_tac "gval (cexp2gexp a x71) s")
     apply simp+
    apply (case_tac "gval (cexp2gexp a x72) s")
    by auto
next
  case (4 b v)
  then show ?case
    apply (cases c')
          apply simp+
          apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some v)")
           apply simp+
         apply (case_tac x2)
          apply simp+
         apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some v)")
          apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some v)")
         apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some v)")
        apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval a s)")
        apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some v)")
       apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x5)")
       apply simp+
     apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some v)")
      apply simp+
     apply (case_tac "gval (cexp2gexp a x6) s")
      apply simp+
    apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some v)")
     apply simp+
    apply (case_tac "gval (cexp2gexp a x71) s")
     apply simp+
    apply (case_tac "gval (cexp2gexp a x72) s")
    by auto
next
  case (5 b v)
  then show ?case
    apply (cases c')
          apply simp
         apply (case_tac x2)
          apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval a s)")
        apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x5)")
       apply simp+
     apply (case_tac "gval (cexp2gexp a x6) s")
      apply simp+
    apply (case_tac "gval (cexp2gexp a x71) s")
     apply simp+
    apply (case_tac "gval (cexp2gexp a x72) s")
    by auto
next
case (6 b v)
  then show ?case
    apply (cases c')
          apply simp+
          apply (case_tac "gval (cexp2gexp a v) s")
           apply simp+
         apply (case_tac x2)
          apply simp+
         apply (case_tac "gval (cexp2gexp a v) s")
          apply simp+
        apply (case_tac "gval (cexp2gexp a v) s")
         apply simp+
       apply (case_tac "gval (cexp2gexp a v) s")
        apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval a s)")
        apply simp+
      apply (case_tac "gval (cexp2gexp a v) s")
       apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x5)")
       apply simp+
     apply (case_tac "gval (cexp2gexp a v) s")
      apply simp+
     apply (case_tac "gval (cexp2gexp a x6) s")
      apply simp+
    apply (case_tac "gval (cexp2gexp a v) s")
     apply simp+
    apply (case_tac "gval (cexp2gexp a x71) s")
     apply simp+
    apply (case_tac "gval (cexp2gexp a x72) s")
    by auto
next
case (7 b v va)
  then show ?case
    apply simp
    apply (cases c')
          apply simp
          apply (case_tac "gval (cexp2gexp a v) s")
           apply simp+
          apply (case_tac "gval (cexp2gexp a va) s")
           apply simp+
          apply auto[1]
         apply (case_tac x2)
          apply simp+
         apply (case_tac "gval (cexp2gexp a v) s")
          apply simp+
         apply (case_tac "gval (cexp2gexp a va) s")
          apply simp+
        apply (case_tac "gval (cexp2gexp a v) s")
         apply simp+
        apply (case_tac "gval (cexp2gexp a va) s")
         apply simp+
        apply auto[1]
       apply simp
       apply (case_tac "gval (cexp2gexp a v) s")
        apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval a s)")
        apply simp+
        apply (case_tac "gval (cexp2gexp a va) s")
         apply simp+
       apply (case_tac "gval (cexp2gexp a va) s")
        apply simp+
       apply auto[1]
      apply simp
      apply (case_tac "gval (cexp2gexp a v) s")
       apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x5)")
       apply simp+
       apply (case_tac "gval (cexp2gexp a va) s")
        apply simp+
      apply (case_tac "gval (cexp2gexp a va) s")
       apply simp+
      apply auto[1]
     apply simp
     apply (case_tac "gval (cexp2gexp a v) s")
    apply simp+
     apply (case_tac "gval (cexp2gexp a x6) s")
      apply simp+
      apply (case_tac "gval (cexp2gexp a va) s")
       apply simp+
     apply (case_tac "gval (cexp2gexp a va) s")
      apply simp+
     apply auto[1]
    apply simp
    apply (case_tac "gval (cexp2gexp a v) s")
     apply simp+
    apply (case_tac "gval (cexp2gexp a x71) s")
     apply simp+
     apply (case_tac "gval (cexp2gexp a va) s")
      apply simp+
    apply (case_tac "gval (cexp2gexp a x72) s")
     apply simp+
     apply (case_tac "gval (cexp2gexp a va) s")
      apply simp+
    apply (case_tac "gval (cexp2gexp a va) s")
     apply simp+
    by auto
qed

lemma and_symmetric: "cexp_equiv (and x y) (and y x)"
proof(induct x)
  case Undef
  then show ?case
    apply (simp add: cexp_equiv_def gexp_equiv_def cval_def)
    apply clarify
    apply (case_tac y)
          apply simp
         apply (case_tac x2)
          apply simp+
        apply auto[1]
       apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval a s)")
        apply simp+
       apply auto[1]
      apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x5)")
       apply simp+
      apply auto[1]
     apply simp+
     apply (case_tac "gval (cexp2gexp a x6) s")
      apply simp+
     apply auto[1]
    apply simp+
    apply (case_tac "gval (cexp2gexp a x71) s")
     apply simp+
    apply (case_tac "gval (cexp2gexp a x72) s")
    by auto
next
  case (Bc x)
  then show ?case
    apply (simp add: cexp_equiv_def gexp_equiv_def cval_def)
    apply (case_tac x)
     apply simp
    apply clarify
    apply (case_tac y)
           apply simp+
          apply (case_tac x2)
           apply simp+
    apply clarify
    apply (case_tac y)
          apply simp+
         apply (case_tac x2)
          apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval a s)")
        apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x5)")
       apply simp+
     apply (case_tac "gval (cexp2gexp a x6) s")
      apply simp+
    apply (case_tac "gval (cexp2gexp a x71) s")
     apply simp+
    apply (case_tac "gval (cexp2gexp a x72) s")
    by auto
next
  case (Eq x)
  then show ?case
    apply (simp add: cexp_equiv_def gexp_equiv_def cval_def)
    apply clarify
    apply (case_tac y)
          apply auto[1]
         apply (case_tac x2)
          apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval a s)")
        apply simp+
       apply auto[1]
      apply simp
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x5)")
       apply simp+
      apply auto[1]
     apply simp
     apply (case_tac "gval (cexp2gexp a x6) s")
      apply simp+
     apply auto[1]
    apply simp
    apply (case_tac "gval (cexp2gexp a x71) s")
     apply simp+
    apply (case_tac "gval (cexp2gexp a x72) s")
    by auto
next
  case (Lt x)
  then show ?case
    apply (simp add: cexp_equiv_def gexp_equiv_def cval_def)
    apply clarify
    apply (cases y)
          apply simp+
          apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x) (aval a s)")
           apply simp+
          apply auto[1]
         apply simp
         apply (case_tac x2)
          apply simp+
         apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x) (aval a s)")
          apply simp+
         apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x) (aval a s)")
         apply simp+
        apply auto[1]
       apply simp
         apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x) (aval a s)")
        apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval a s)")
         apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval a s)")
        apply simp+
       apply auto[1]
      apply simp
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x) (aval a s)")
       apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x5)")
        apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x5)")
       apply simp+
      apply auto[1]
     apply simp
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x) (aval a s)")
      apply simp+
      apply (case_tac "gval (cexp2gexp a x6) s")
       apply simp+
      apply (case_tac "gval (cexp2gexp a x6) s")
      apply simp+
     apply auto[1]
    apply simp
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x) (aval a s)")
     apply simp+
     apply (case_tac "gval (cexp2gexp a x71) s")
      apply simp+
     apply (case_tac "gval (cexp2gexp a x72) s")
      apply simp+
     apply (case_tac "gval (cexp2gexp a x71) s")
      apply simp+
     apply (case_tac "gval (cexp2gexp a x72) s")
    by auto
next
  case (Gt x)
  then show ?case
    apply (simp add: cexp_equiv_def gexp_equiv_def cval_def)
    apply clarify
    apply (cases y)
          apply simp
          apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x)")
           apply simp+
          apply auto[1]
         apply (case_tac x2)
          apply simp
         apply simp+
          apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x)")
          apply simp+
          apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x)")
         apply simp+
        apply auto[1]
       apply simp
          apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x)")
        apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval a s)")
         apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval a s)")
        apply simp+
       apply auto[1]
      apply simp
          apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x)")
       apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x5)")
        apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x5)")
       apply simp+
      apply auto[1]
     apply simp
     apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x)")
      apply simp+
      apply (case_tac "gval (cexp2gexp a x6) s")
       apply simp+
      apply (case_tac "gval (cexp2gexp a x6) s")
      apply simp+
     apply auto[1]
    apply simp
     apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x)")
     apply simp+
     apply (case_tac "gval (cexp2gexp a x71) s")
      apply simp+
     apply (case_tac "gval (cexp2gexp a x72) s")
      apply simp+
     apply (case_tac "gval (cexp2gexp a x71) s")
      apply simp+
     apply (case_tac "gval (cexp2gexp a x72) s")
    by auto
next
  case (Not x)
  then show ?case
    apply (simp add: cexp_equiv_def gexp_equiv_def cval_def)
    apply clarify
    apply (cases y)
          apply simp
          apply (case_tac "gval (cexp2gexp a x) s")
           apply simp+
          apply auto[1]
         apply (case_tac x2)
          apply simp+
          apply (case_tac "gval (cexp2gexp a x) s")
          apply simp+
          apply (case_tac "gval (cexp2gexp a x) s")
         apply simp+
        apply auto[1]
       apply simp
          apply (case_tac "gval (cexp2gexp a x) s")
        apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval a s)")
         apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval a s)")
        apply simp+
       apply auto[1]
      apply simp
 apply (case_tac "gval (cexp2gexp a x) s")
       apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x5)")
        apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x5)")
       apply simp+
      apply auto[1]
     apply simp
 apply (case_tac "gval (cexp2gexp a x) s")
      apply simp+
      apply (case_tac "gval (cexp2gexp a x6) s")
       apply simp+
      apply (case_tac "gval (cexp2gexp a x6) s")
      apply simp+
     apply auto[1]
    apply simp
 apply (case_tac "gval (cexp2gexp a x) s")
     apply simp+
     apply (case_tac "gval (cexp2gexp a x71) s")
      apply simp+
     apply (case_tac "gval (cexp2gexp a x72) s")
      apply simp+
     apply (case_tac "gval (cexp2gexp a x71) s")
     apply simp+
     apply (case_tac "gval (cexp2gexp a x72) s")
    by auto
next
  case (And x1 x2)
  then show ?case
    apply (simp add: cexp_equiv_def gexp_equiv_def cval_def)
    apply clarify
    apply (cases y)
          apply simp
          apply (case_tac "gval (cexp2gexp a x1) s")
           apply simp+
          apply (case_tac "gval (cexp2gexp a x2) s")
           apply simp+
          apply auto[1]
         apply (case_tac x2a)
          apply simp+
         apply (case_tac "gval (cexp2gexp a x1) s")
          apply simp+
         apply (case_tac "gval (cexp2gexp a x2) s")
          apply simp+
        apply (case_tac "gval (cexp2gexp a x1) s")
         apply simp+
         apply (case_tac "gval (cexp2gexp a x2) s")
         apply simp+
        apply auto[1]
       apply simp
       apply (case_tac "gval (cexp2gexp a x1) s")
        apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval a s)")
         apply simp+
       apply (case_tac "gval (cexp2gexp a x2) s")
        apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval a s)")
         apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval a s)")
        apply simp+
       apply auto[1]
      apply simp
      apply (case_tac "gval (cexp2gexp a x1) s")
       apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x5)")
        apply simp+
      apply (case_tac "gval (cexp2gexp a x2) s")
       apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x5)")
        apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval a s) (Some x5)")
       apply simp+
      apply auto[1]
     apply simp
     apply (case_tac "gval (cexp2gexp a x1) s")
      apply simp+
      apply (case_tac "gval (cexp2gexp a x6) s")
       apply simp+
     apply (case_tac "gval (cexp2gexp a x2) s")
      apply simp+
      apply (case_tac "gval (cexp2gexp a x6) s")
       apply simp+
     apply (case_tac "gval (cexp2gexp a x6) s")
      apply simp+
     apply auto[1]
    apply simp
    apply (case_tac "gval (cexp2gexp a x1) s")
     apply simp+
     apply (case_tac "gval (cexp2gexp a x71) s")
      apply simp+
     apply (case_tac "gval (cexp2gexp a x72) s")
      apply simp+
    apply (case_tac "gval (cexp2gexp a x2) s")
     apply simp+
     apply (case_tac "gval (cexp2gexp a x71) s")
      apply simp+
     apply (case_tac "gval (cexp2gexp a x72) s")
      apply simp+
    apply (case_tac "gval (cexp2gexp a x71) s")
     apply simp+
    apply (case_tac "gval (cexp2gexp a x72) s")
    by auto
qed

lemma cexp_equiv_symmetric: "cexp_equiv x y \<Longrightarrow> cexp_equiv y x"
  by (simp add: cexp_equiv_def gexp_equiv_def)

lemma cexp_equiv_transitive: "cexp_equiv x y \<Longrightarrow> cexp_equiv y z \<Longrightarrow> cexp_equiv x z"
  by (simp add: cexp_equiv_def gexp_equiv_def)

lemma gval_and_none: "gval (cexp2gexp a y) x = None \<Longrightarrow> gval (cexp2gexp a (and z y)) x = None"
proof(induct y rule: cexp2gexp.induct)
case (1 uu b)
  then show ?case
    by simp
next
  case (2 a)
  then show ?case
    by simp
next
  case (3 b v)
  then show ?case
    apply simp
    apply (case_tac z)
          apply simp
         apply (case_tac x2)
          apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval b x)")
        apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval b x) (Some x5)")
       apply simp+
     apply (case_tac "gval (cexp2gexp b x6) x")
      apply simp+
    apply (case_tac "gval (cexp2gexp b x71) x")
     apply simp+
    apply (case_tac "gval (cexp2gexp b x72) x")
    by auto
next
  case (4 b v)
  then show ?case
    apply simp
    apply (case_tac z)
          apply simp
         apply (case_tac x2)
          apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval b x)")
        apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval b x) (Some x5)")
       apply simp+
     apply (case_tac "gval (cexp2gexp b x6) x")
      apply simp+
    apply (case_tac "gval (cexp2gexp b x71) x")
     apply simp+
    apply (case_tac "gval (cexp2gexp b x72) x")
    by auto
next
  case (5 a v)
  then show ?case
    by simp
next
  case (6 b v)
  then show ?case
    apply simp
    apply (case_tac "gval (cexp2gexp b v) x")
     apply simp
     apply (case_tac z)
           apply simp
          apply (case_tac x2)
           apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval b x)")
         apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval b x) (Some x5)")
        apply simp+
      apply (case_tac "gval (cexp2gexp b x6) x")
       apply simp+
     apply (case_tac "gval (cexp2gexp b x71) x")
      apply simp+
     apply (case_tac "gval (cexp2gexp b x72) x")
    by auto
next
  case (7 b v va)
  then show ?case
    apply simp
    apply (case_tac "gval (cexp2gexp b v) x")
     apply simp
     apply (case_tac z)
    apply simp
          apply (case_tac x2)
           apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval b x)")
         apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval b x) (Some x5)")
         apply simp+
      apply (case_tac "gval (cexp2gexp b x6) x")
       apply simp+
     apply (case_tac "gval (cexp2gexp b x71) x")
      apply simp+
     apply (case_tac "gval (cexp2gexp b x72) x")
      apply simp+
    apply (case_tac "gval (cexp2gexp b va) x")
     apply simp
     apply (case_tac z)
           apply simp
          apply (case_tac x2)
           apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval b x)")
         apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval b x) (Some x5)")
        apply simp+
      apply (case_tac "gval (cexp2gexp b x6) x")
       apply simp+
     apply (case_tac "gval (cexp2gexp b x71) x")
      apply simp+
     apply (case_tac "gval (cexp2gexp b x72) x")
    by auto
qed

lemma and_is_And [simp]:  "cval (and x y) = cval (And x y)"
  apply (rule ext)+
  apply (simp add: cval_def)
  proof (induction x rule: cexp2gexp.induct)
case (1 uu b)
  then show ?case
    apply simp
    apply (case_tac "gval (cexp2gexp x y) xa")
     apply simp
     apply (case_tac b)
      apply simp+
     apply (case_tac y)
           apply simp
          apply (case_tac x2)
           apply simp+
    apply (case_tac b)
     apply simp
    apply (case_tac y)
           apply simp
          apply (case_tac x2)
    by auto
next
  case (2 b)
  then show ?case
    apply simp
    apply (case_tac "gval (cexp2gexp x y) xa")
     apply simp
     apply (case_tac y)
    apply simp
    apply (case_tac x2)
           apply simp+
    apply (case_tac y)
          apply simp
    apply (case_tac x2)
    by auto
next
  case (3 b v)
  then show ?case
    apply simp
    apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some v) (aval x xa)")
     apply simp
     apply (case_tac y)
    apply simp
    apply (case_tac x2)
           apply simp+
        apply auto[1]
           apply simp+
    apply (case_tac "gval (cexp2gexp x y) xa")
     apply simp
     apply (case_tac y)
    apply simp
    apply (case_tac x2)
           apply simp+
    apply (case_tac y)
          apply simp
    apply (case_tac x2)
    by auto
next
  case (4 a v)
  then show ?case
    apply simp
    apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval x xa) (Some v)")
     apply simp
     apply (case_tac y)
    apply simp
    apply (case_tac x2)
           apply simp+
        apply auto[1]
           apply simp+
    apply (case_tac "gval (cexp2gexp x y) xa")
     apply simp
     apply (case_tac y)
    apply simp
    apply (case_tac x2)
           apply simp+
    apply (case_tac y)
          apply simp
    apply (case_tac x2)
    by auto
next
  case (5 a v)
  then show ?case
    apply simp
    apply (case_tac "gval (cexp2gexp x y) xa")
     apply simp
     apply (case_tac y)
    apply simp
    apply (case_tac x2)
           apply simp+
    apply (case_tac y)
          apply simp
    apply (case_tac x2)
    by auto
next
  case (6 a v)
  then show ?case
    apply simp
    apply (case_tac "gval (cexp2gexp x v) xa")
     apply simp
     apply (case_tac y)
           apply simp
          apply (case_tac x2)
           apply simp+
      apply auto[1]
     apply simp+
    apply (case_tac "gval (cexp2gexp x y) xa")
     apply simp
     apply (case_tac y)
    apply simp
    apply (case_tac x2)
           apply simp+
    apply (case_tac y)
          apply simp
    apply (case_tac x2)
    by auto
next
  case (7 b v va)
  then show ?case
    apply simp
    apply (case_tac "gval (cexp2gexp x v) xa")
     apply simp
     apply (case_tac y)
    apply simp
    apply (case_tac x2)
           apply simp+
    apply (case_tac y)
          apply simp
    apply (case_tac x2)
           apply simp+
     apply auto[1]
    apply simp
    apply (case_tac "gval (cexp2gexp x va) xa")
     apply simp
     apply (case_tac y)
    apply simp
    apply (case_tac x2)
           apply simp+
     apply auto[1]
    apply simp
    apply (case_tac "gval (cexp2gexp x y) xa")
     apply simp
     apply (case_tac y)
    apply simp
    apply (case_tac x2)
           apply simp+
    apply (case_tac y)
          apply simp
    apply (case_tac x2)
    by auto
qed

lemma and_true [simp]: "and x (Bc True) = x"
  proof (cases x)
  case Undef
    then show ?thesis by simp
  next
    case (Bc x2)
    then show ?thesis by (cases x2, simp_all)
  next
    case (Eq x3)
    then show ?thesis by simp
  next
  case (Lt x4)
  then show ?thesis by simp
  next
  case (Gt x5)
  then show ?thesis by simp
  next
    case (Not x6)
    then show ?thesis by simp
  next
    case (And x71 x72)
    then show ?thesis by simp
  qed

theorem not_is_Not[simp]: "cval (not x) = cval (Not x)"
  apply (rule ext)+
  apply (simp add: cval_def)
proof(induct x rule: cexp2gexp.induct)
case (1 uu b)
  then show ?case
    apply (case_tac b)
    by auto
next
case (2 a)
  then show ?case
    by simp
next
case (3 a v)
  then show ?case
    apply simp
    apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some v) (aval x xa)")
    by auto
next
case (4 a v)
  then show ?case
    apply simp
    apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval x xa) (Some v)")
    by auto
next
  case (5 a v)
  then show ?case
    by simp
next
  case (6 a v)
  then show ?case
    apply simp
    apply (case_tac "gval (cexp2gexp x v) xa")
    by auto
next
case (7 a v va)
  then show ?case
    apply simp
    apply (case_tac "gval (cexp2gexp x v) xa")
     apply simp+
    apply (case_tac "gval (cexp2gexp x va) xa")
    by auto
qed 

lemma true_not_false: "cval (Bc True) = cval (Not (Bc False))"
  apply (rule ext)
  apply (simp add: cval_def)
  by auto

lemma false_not_true: "cval (Bc False) = cval (Not (Bc True))"
  apply (rule ext)
  apply (simp add: cval_def)
  by auto

lemma satisfiable_eq: "satisfiable (Eq x3)"
  apply (simp add: satisfiable_def cval_def)
  using aval.simps(1) by blast

lemma satisfiable_neq: "satisfiable (Neq x3)"
  apply (simp add: satisfiable_def cval_def)
  by (metis aval.simps(1) option.inject value.simps(4))

lemma satisfiable_leq: "satisfiable (Leq (Num x))"
  apply (simp add: satisfiable_def cval_def)
proof -
  have "maybe_not (case MaybeBoolInt (\<lambda>i ia. ia < i) (aval (L (Num x)) elem_0) (Some (Num x)) of None \<Rightarrow> None | Some b \<Rightarrow> case MaybeBoolInt (\<lambda>i ia. ia < i) (aval (L (Num x)) elem_0) (Some (Num x)) of None \<Rightarrow> None | Some ba \<Rightarrow> Some (b \<or> ba)) = Some True"
    by auto
  then show "\<exists>a f. maybe_not (case MaybeBoolInt (\<lambda>i ia. ia < i) (aval a f) (Some (Num x)) of None \<Rightarrow> None | Some b \<Rightarrow> case MaybeBoolInt (\<lambda>i ia. ia < i) (aval a f) (Some (Num x)) of None \<Rightarrow> None | Some ba \<Rightarrow> Some (b \<or> ba)) = Some True"
    by blast
qed


lemma satisfiable_geq: "satisfiable (Geq (Num x))"
  apply (simp add: satisfiable_def cval_def)
proof -
  have "maybe_not (case MaybeBoolInt (\<lambda>i ia. ia < i) (Some (Num x)) (aval (L (Num x)) elem_0) of None \<Rightarrow> None | Some b \<Rightarrow> case MaybeBoolInt (\<lambda>i ia. ia < i) (Some (Num x)) (aval (L (Num x)) elem_0)  of None \<Rightarrow> None | Some ba \<Rightarrow> Some (b \<or> ba)) = Some True"
    by auto
  then show "\<exists>a f. maybe_not (case MaybeBoolInt (\<lambda>i ia. ia < i) (Some (Num x)) (aval a f) of None \<Rightarrow> None | Some b \<Rightarrow> case MaybeBoolInt (\<lambda>i ia. ia < i)(Some (Num x))  (aval a f) of None \<Rightarrow> None | Some ba \<Rightarrow> Some (b \<or> ba)) = Some True"
    by blast
qed

lemma satisfiable_lt: "satisfiable (Lt (Num x))"
  apply (simp add: satisfiable_def cval_def)
  by (metis (full_types) MaybeBoolInt.simps(1) aval.simps(1) lt_ex)

lemma unsatisfiable_lt: "\<not> satisfiable (Lt (Str s))"
  by (simp add: satisfiable_def cval_def)

lemma satisfiable_gt: "satisfiable (Gt (Num x4))"
  apply (simp add: satisfiable_def cval_def)
  by (metis (full_types) MaybeBoolInt.simps(1) aval.simps(1) zless_iff_Suc_zadd)

lemma unsatisfiable_gt: "\<not> satisfiable (Gt (Str s))"
  by (simp add: satisfiable_def cval_def)

lemma satisfiable_true[simp]: "satisfiable (Bc True)"
  by (simp add: satisfiable_def cval_def)

lemma valid_true[simp]: "valid (Bc True)"
  by (simp add: valid_def cval_def)

lemma unsatisfiable_false[simp]: "\<not> satisfiable (Bc False)"
  by (simp add: satisfiable_def cval_def)

lemma satisfiable_not_undef: "satisfiable (Not (Undef))"
  apply (simp add: satisfiable_def cval_def)
  using aval.simps(1) by blast

lemma cval_double_negation: "cval (Not (Not v)) = cval v"
  by (metis cexp.simps(54) not.simps not_is_Not)

lemma plus_num_str: "compose_plus (Eq (Str s)) (Eq (Num n)) = Bc False"
  apply simp
  apply (simp add: valid_def satisfiable_def cval_def)
  by (metis aval.simps(1) option.inject value.simps(4))


lemma and_x_y_undef: "and x y = Undef \<Longrightarrow> and y x = Undef"
proof (induction x)
case Undef
  then show ?case
    apply (cases y)
          prefer 2
          apply (case_tac x2)
    by simp_all
next
  case (Bc x)
  then show ?case
    apply (cases x)
     apply (cases y)
           apply (simp, simp, simp, simp, simp, simp, simp)
    apply (cases y)
          prefer 2
          apply (case_tac x2)
    by simp_all
next
  case (Eq x)
  then show ?case
    apply (cases y)
          apply simp
         apply (case_tac x2)
          apply simp
         apply simp
    apply (metis and.simps(25) cexp.distinct(11))
    by simp_all
next
  case (Lt x)
  then show ?case
    apply (cases y)
          apply simp
         apply (case_tac x2)
          apply simp
         apply simp
        apply simp
       apply (metis and.simps(33) cexp.distinct(11))
    by simp_all
next
case (Gt x)
  then show ?case
    apply (cases y)
          apply simp
         apply (case_tac x2)
          apply simp
         apply simp
        apply simp
       apply simp
      apply (metis and.simps(41) cexp.distinct(11))
    by simp_all
next
  case (Not x)
  then show ?case
    apply (cases y)
          apply simp
         apply (case_tac x2)
          apply simp
         apply simp
        apply simp
       apply simp
      apply simp
     apply (metis and.simps(49) cexp.distinct(11))
    by simp
next
  case (And x1 x2)
  then show ?case
    apply (cases y)
          apply simp
         apply simp
         apply (case_tac x2a)
          apply simp
         apply simp
        apply simp
       apply simp
      apply simp
     apply simp
    by (metis and.simps(57) cexp.distinct(11))
qed

definition mutually_exclusive :: "cexp \<Rightarrow> cexp \<Rightarrow> bool" where
  "mutually_exclusive x y = (\<forall>a i. (cval x i a= Some True \<longrightarrow> cval y i a \<noteq> Some True) \<and>
                                 (cval y i a = Some True \<longrightarrow> cval x i a \<noteq> Some True))"

lemma mutually_exclusive_unsatisfiable_conj: "mutually_exclusive x y = (\<not> satisfiable (And x y))"
  apply (simp add: mutually_exclusive_def satisfiable_def cval_def)
  apply standard
   apply clarify
   apply (case_tac "gval (cexp2gexp a x) s")
    apply simp+
   apply (case_tac "gval (cexp2gexp a y) s")
    apply simp+
  apply clarify
proof -
  fix a :: "vname \<Rightarrow> value option" and i :: aexp
  assume a1: "\<forall>a s. maybe_not (case maybe_not (case gval (cexp2gexp a x) s of None \<Rightarrow> None | Some aa \<Rightarrow> case gval (cexp2gexp a x) s of None \<Rightarrow> None | Some b \<Rightarrow> Some (aa \<or> b)) of None \<Rightarrow> None | Some aa \<Rightarrow> case maybe_not (case gval (cexp2gexp a y) s of None \<Rightarrow> None | Some aa \<Rightarrow> case gval (cexp2gexp a y) s of None \<Rightarrow> None | Some b \<Rightarrow> Some (aa \<or> b)) of None \<Rightarrow> None | Some b \<Rightarrow> Some (aa \<or> b)) \<noteq> Some True"
have "gval (cexp2gexp i y) a = Some True \<and> gval (cexp2gexp i x) a = Some True \<longrightarrow> maybe_not (case maybe_not (case gval (cexp2gexp i x) a of None \<Rightarrow> None | Some b \<Rightarrow> case gval (cexp2gexp i x) a of None \<Rightarrow> None | Some ba \<Rightarrow> Some (b \<or> ba)) of None \<Rightarrow> None | Some b \<Rightarrow> case maybe_not (case gval (cexp2gexp i y) a of None \<Rightarrow> None | Some b \<Rightarrow> case gval (cexp2gexp i y) a of None \<Rightarrow> None | Some ba \<Rightarrow> Some (b \<or> ba)) of None \<Rightarrow> None | Some ba \<Rightarrow> Some (b \<or> ba)) = Some True"
  by simp
  then show "(gval (cexp2gexp i x) a = Some True \<longrightarrow> gval (cexp2gexp i y) a \<noteq> Some True) \<and> (gval (cexp2gexp i y) a = Some True \<longrightarrow> gval (cexp2gexp i x) a \<noteq> Some True)"
using a1 by blast
qed

lemma unsatisfiable_conj_mutually_exclusive: "\<not> satisfiable (And x y) = mutually_exclusive x y"
  by (simp add: mutually_exclusive_unsatisfiable_conj)

lemma mutually_exclusive_reflexive: "satisfiable x \<Longrightarrow> \<not> mutually_exclusive x x"
  apply (simp add: mutually_exclusive_def satisfiable_def)
  by auto

lemma mutually_exclusive_symmetric: "mutually_exclusive x y \<Longrightarrow> mutually_exclusive y x"
  by (simp add: mutually_exclusive_def)

lemma not_mutually_exclusive_true: "satisfiable x = (\<not> mutually_exclusive x (Bc True))"
  apply (simp add: mutually_exclusive_def satisfiable_def)
  using valid_def valid_true by blast

lemma cval_values: "(cval x i a \<noteq> Some False) = (cval x i a = Some True \<or> cval x i a = None)"
  by auto

lemma x_neq_not_x: "x \<noteq> cexp.Not x"
  apply (induct_tac x)
  by auto

lemma gval_And: "gval (cexp2gexp a (And c1 c2)) = gval (gAnd (cexp2gexp a c1) (cexp2gexp a c2))"
  apply (rule ext)
  by simp

lemma gval_not: "gval (cexp2gexp a (Not c)) = gval (gNot (cexp2gexp a c))"
  apply (rule ext)
  by simp

end
