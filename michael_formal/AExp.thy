section{*Extended Finite State Machines*}
text{*
This section presents the theories associated with EFSMs. First we define a language of arithmetic
expressions for guards, outputs, and updates similar to that in IMP \cite{fixme}. We then go on to
define the guard logic such that nonsensical guards (such as testing to see if an integer is greater
than a string) can never evaluate to true. Next, the guard language is defined in terms of
arithmetic expressions and binary relations. In the interest of simplifying the conversion of guards
to constraints, we use a Nor logic, although we define syntax hacks for the expression of guards
using other logical operators. With the underlying types defined, we then define EFSMs and prove
that they are prefix-closed, that is to say that if a string of inputs is accepted by the machine
then all of its prefixes are also accepted.
*}
subsection {* Arithmetic Expressions *}
text{*
This theory defines a language of arithmetic expressions over literal values and variables. Here,
values are limited to integers and strings. Variables may be either inputs or registers. We also
limit ourselves to a simple arithmetic of plus and minus as a proof of concept.
*}

theory AExp
  imports Value VName Utils
begin

type_synonym datastate = "vname \<Rightarrow> value option"

datatype aexp = L "value" | V vname | Plus aexp aexp | Minus aexp aexp

syntax (xsymbols)
  Plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" (*infix "+" 60*)
  Minus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" (*infix "-" 60*)

instantiation aexp :: "show" begin
fun shows_prec_aexp :: "nat \<Rightarrow> aexp \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_prec_aexp n (L i) c = shows_prec n i c" |
  "shows_prec_aexp n (V i) c = shows_prec n i c" |
  "shows_prec_aexp a (Plus v va) c = ''(''@(shows_prec a v '''')@''+''@(shows_prec a va '''')@'')''@c"|
  "shows_prec_aexp a (Minus v va) c = ''(''@(shows_prec a v '''')@''-''@(shows_prec a va '''')@'')''@c"

primrec shows_list_aexp_aux :: "aexp list \<Rightarrow> string list" where
  "shows_list_aexp_aux [] = ''''" |
  "shows_list_aexp_aux (h#t) = (shows_prec 0 h '''')#(shows_list_aexp_aux t)"

definition shows_list_aexp :: "aexp list \<Rightarrow> char list \<Rightarrow> char list" where
"shows_list_aexp lst c = (join (shows_list_aexp_aux lst) '', '')@c"

instance proof
  fix y :: aexp
  fix r s p
  show "shows_prec p y (r @ s) = shows_prec p y r @ s"
  proof (induction y)
    case (L x)
    then show ?case by (simp add: shows_prec_append)
  next
    case (V x)
    then show ?case by (simp add: shows_prec_append)
  next
    case (Plus y1 y2)
    then show ?case by (simp add: shows_prec_append)
  next
    case (Minus y1 y2)
    then show ?case by (simp add: shows_prec_append)
  qed
next
  fix xs :: "aexp list"
  fix r s p
  show "shows_list xs (r @ s) = shows_list xs r @ s"
  proof (induction xs)
    case Nil
    then show ?case by (simp add: shows_list_aexp_def)
  next
    case (Cons a xs)
    then show ?case by (simp add: shows_list_aexp_def)
  qed
qed
end

fun value_plus :: "value option \<Rightarrow> value option \<Rightarrow> value option" (*infix "+" 40*) where
  "value_plus (Some (Num x)) (Some (Num y)) = Some (Num (x+y))" |
  "value_plus _ _ = None"

lemma plus_no_string [simp]:"value_plus a b \<noteq> Some (Str x)"
  using value_plus.elims by blast

lemma value_plus_symmetry: "value_plus x y = value_plus y x"
  proof (cases x)
    case None
    then show ?thesis by simp
  next
    case (Some a)
    then show ?thesis
      apply (cases y)
       apply simp
      apply (case_tac a)
       apply (case_tac aa)
        apply simp
       apply simp
      apply (case_tac aa)
      by simp_all
  qed

fun value_minus :: "value option \<Rightarrow> value option \<Rightarrow> value option" (*infix "-" 40*) where
  "value_minus (Some (Num x)) (Some (Num y)) = Some (Num (x-y))" |
  "value_minus _ _ = None"

lemma minus_no_string [simp]:"value_minus a b \<noteq> Some (Str x)"
  using value_minus.elims by blast

fun aval :: "aexp \<Rightarrow> datastate \<Rightarrow> value option" where
  "aval (L x) s = Some x" |
  "aval (V x) s = s x" |
  "aval (Plus a\<^sub>1 a\<^sub>2) s = value_plus (aval a\<^sub>1 s)(aval a\<^sub>2 s)" |
  "aval (Minus a\<^sub>1 a\<^sub>2) s = value_minus (aval a\<^sub>1 s) (aval a\<^sub>2 s)"

lemma aval_plus_symmetry: "aval (Plus x y) s = aval (Plus y x) s"
  by (simp add: value_plus_symmetry)

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. None"
declare null_state_def [simp]

syntax
  "_maplet"  :: "['a, 'a] \<Rightarrow> maplet"             ("_ /:=/ _")
  "_maplets" :: "['a, 'a] \<Rightarrow> maplet"             ("_ /[:=]/ _")
  "_Map"     :: "maplets \<Rightarrow> 'a \<rightharpoonup> 'b"            ("(1<_>)")

lemma aexp_deterministic_string: "(show (x::aexp) = show y) = (x = y)"
proof (induct x)
  case (L x)
  then show ?case sorry    
next
  case (V x)
  then show ?case sorry
next
  case (Plus x1 x2)
  then show ?case sorry
next
  case (Minus x1 x2)
  then show ?case sorry
qed
end
