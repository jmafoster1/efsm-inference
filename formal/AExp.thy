section\<open>Extended Finite State Machines\<close>
text\<open>
This section presents the theories associated with EFSMs. First we define a language of arithmetic
expressions for guards, outputs, and updates similar to that in IMP \cite{fixme}. We then go on to
define the guard logic such that nonsensical guards (such as testing to see if an integer is greater
than a string) can never evaluate to true. Next, the guard language is defined in terms of
arithmetic expressions and binary relations. In the interest of simplifying the conversion of guards
to constraints, we use a Nor logic, although we define syntax hacks for the expression of guards
using other logical operators. With the underlying types defined, we then define EFSMs and prove
that they are prefix-closed, that is to say that if a string of inputs is accepted by the machine
then all of its prefixes are also accepted.
\<close>
subsection \<open>Arithmetic Expressions\<close>
text\<open>
This theory defines a language of arithmetic expressions over literal values and variables. Here,
values are limited to integers and strings. Variables may be either inputs or registers. We also
limit ourselves to a simple arithmetic of plus and minus as a proof of concept.
\<close>

theory AExp
  imports Value VName FinFun.FinFun
begin

declare One_nat_def [simp del]
unbundle finfun_syntax

type_synonym registers = "nat \<Rightarrow>f value option"
type_synonym datastate = "vname \<Rightarrow> value option"

text_raw\<open>\snip{aexptype}{1}{2}{%\<close>
datatype aexp = L "value" | V vname | Plus aexp aexp | Minus aexp aexp
text_raw\<open>}%endsnip\<close>

syntax (xsymbols)
  Plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" (*infix "+" 60*)
  Minus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" (*infix "-" 60*)

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

abbreviation null_state ("<>") where
  "null_state \<equiv> (K$ None)"

nonterminal maplets and maplet

syntax
  "_maplet"  :: "['a, 'a] \<Rightarrow> maplet"             ("_ /:=/ _")
  "_maplets" :: "['a, 'a] \<Rightarrow> maplet"             ("_ /[:=]/ _")
  ""         :: "maplet \<Rightarrow> maplets"             ("_")
  "_Maplets" :: "[maplet, maplets] \<Rightarrow> maplets" ("_,/ _")
  "_MapUpd"  :: "['a \<rightharpoonup> 'b, maplets] \<Rightarrow> 'a \<rightharpoonup> 'b" ("_/'(_')" [900, 0] 900)
  "_Map"     :: "maplets \<Rightarrow> 'a \<rightharpoonup> 'b"            ("(1[_])")
  "_Map"     :: "maplets \<Rightarrow> 'a \<rightharpoonup> 'b"            ("(1<_>)")

translations
  "_MapUpd m (_Maplets xy ms)"  \<rightleftharpoons> "_MapUpd (_MapUpd m xy) ms"
  "_MapUpd m (_maplet  x y)"    \<rightleftharpoons> "m(x $:= CONST Some y)"
  "_Map ms"                     \<rightleftharpoons> "_MapUpd (CONST empty) ms"
  "_Map (_Maplets ms1 ms2)"     \<leftharpoondown> "_MapUpd (_Map ms1) ms2"
  "_Maplets ms1 (_Maplets ms2 ms3)" \<leftharpoondown> "_Maplets (_Maplets ms1 ms2) ms3"

(*syntax
  "_maplet"  :: "['a, 'a] \<Rightarrow> maplet"             ("_ /:=/ _")
  "_maplets" :: "['a, 'a] \<Rightarrow> maplet"             ("_ /[:=]/ _")
  "_Map"     :: "maplets \<Rightarrow> 'a \<rightharpoonup> 'b"            ("(1<_>)")*)

instantiation aexp :: plus begin
fun plus_aexp :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus_aexp (L (Num n1)) (L (Num n2)) = L (Num (n1+n2))" |
  "plus_aexp x y = Plus x y"

instance by standard
end

instantiation aexp :: minus begin
fun minus_aexp :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "minus_aexp (L (Num n1)) (L (Num n2)) = L (Num (n1-n2))" |
  "minus_aexp x y = Minus x y"

instance by standard
end

definition input2state :: "value list \<Rightarrow> registers" where
  "input2state n = fold (\<lambda>(k, v) f. f(k $:= Some v)) (enumerate 0 n) (K$ None)"

primrec input2state_prim :: "value list \<Rightarrow> nat \<Rightarrow> registers" where
  "input2state_prim [] _ = (K$ None)" |
  "input2state_prim (v#t) k = (input2state_prim t (k+1))(k $:= Some v)"

lemma input2state_append: "input2state (i @ [a]) = (input2state i)(length i $:= Some a)"
  apply (simp add: eq_finfun_All_ext finfun_All_def finfun_All_except_def)
  apply clarify
  by (simp add: input2state_def enumerate_eq_zip)

lemma fold_conv_foldr: "fold f xs = foldr f (rev xs)"
  by (simp add: foldr_conv_fold)

lemma length_map: "length i > 0 \<Longrightarrow> [Suc 0..<length i] @ [length i] = map Suc [0..<length i]"
  by (simp add: Suc_leI map_Suc_upt)

lemma input2state_out_of_bounds: "i \<ge> length ia \<Longrightarrow> input2state ia $ i = None"
proof(induct ia rule: rev_induct)
  case Nil
  then show ?case
    by (simp add: input2state_def)
next
  case (snoc a as)
  then show ?case
    by (simp add: input2state_def enumerate_eq_zip)
qed

lemma input2state_within_bounds: "input2state i $ x = Some a \<Longrightarrow> x < length i"
  by (metis input2state_out_of_bounds not_le_imp_less option.distinct(1))

lemma input2state_not_None: "input2state i $ x \<noteq> None \<Longrightarrow> x < length i"
  by (meson input2state_out_of_bounds leI)


lemma input2state_empty: "input2state [] $ x1 = None"
  by (simp add: input2state_out_of_bounds)

lemma input2state_nth: "i < length ia \<Longrightarrow> input2state ia $ i = Some (ia ! i)"
proof(induct ia rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc a ia)
  then show ?case
    apply (simp add: input2state_def enumerate_eq_zip)
    by (simp add: finfun_upd_apply nth_append)
qed

lemma input2state_cons:
  "x1 > 0 \<Longrightarrow>
   x1 < length ia \<Longrightarrow>
   input2state (a # ia) $ x1 = input2state ia $ (x1-1)"
  by (simp add: input2state_nth)

lemma input2state_cons_shift: "input2state i $ x1 = Some a \<Longrightarrow> input2state (b # i) $ (Suc x1) = Some a"
proof(induct i rule: rev_induct)
  case Nil
  then show ?case
    by (simp add: input2state_def)
next
  case (snoc x xs)
  then show ?case
    using input2state_within_bounds[of xs x1 a]
    using input2state_cons[of "Suc x1" "xs @ [x]" b]
    apply simp
    apply (case_tac "x1 < length xs")
     apply simp
    by (metis finfun_upd_apply input2state_append input2state_nth length_Cons length_append_singleton lessI list.sel(3) nth_tl)
qed

lemma input2state_exists: "\<exists>i. input2state i $ x1 = Some a"
proof(induct x1)
  case 0
  then show ?case
    apply (rule_tac x="[a]" in exI)
    by (simp add: input2state_def)
next
  case (Suc x1)
  then show ?case
    apply clarify
    apply (rule_tac x="a#i" in exI)
    by (simp add: input2state_cons_shift)
qed

primrec repeat :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "repeat 0 _ = []" |
  "repeat (Suc m) a = a#(repeat m a)"

lemma length_repeat: "length (repeat n a) = n"
proof(induct n)
  case 0
  then show ?case
    by simp
next
  case (Suc a)
  then show ?case
    by simp
qed

lemma length_append_repeat: "length (i@(repeat a y)) \<ge> length i"
  by simp

lemma length_input2state_repeat: "input2state i $ x = Some a \<Longrightarrow> y < length (i @ repeat y a)"
  by (metis append.simps(1) append_eq_append_conv input2state_within_bounds length_append length_repeat list.size(3) neqE not_add_less2 zero_order(3))

lemma input2state_double_exists: "\<exists>i. input2state i $ x = Some a \<and> input2state i $ y = Some a"
  apply (insert input2state_exists[of x a])
  apply clarify
  apply (case_tac "x \<ge> y")
  apply (rule_tac x="list_update i y a" in exI)
  apply (metis (no_types, lifting) input2state_within_bounds input2state_nth input2state_out_of_bounds le_trans length_list_update not_le_imp_less nth_list_update_eq nth_list_update_neq)
  apply (rule_tac x="list_update (i@(repeat y a)) y a" in exI)
  apply (simp add: not_le)
  by (metis length_input2state_repeat input2state_nth input2state_out_of_bounds le_trans length_append_repeat length_list_update not_le_imp_less nth_append nth_list_update_eq nth_list_update_neq option.distinct(1))

lemma input2state_double_exists_2: "x \<noteq> y \<Longrightarrow> \<exists>i. input2state i $ x = Some a \<and> input2state i $ y = Some a'"
  apply (insert input2state_exists[of x a])
  apply clarify
  apply (case_tac "x \<ge> y")
  apply (rule_tac x="list_update i y a'" in exI)
  apply (metis (no_types, lifting) input2state_within_bounds input2state_nth input2state_out_of_bounds le_trans length_list_update not_le_imp_less nth_list_update_eq nth_list_update_neq)
  apply (rule_tac x="list_update (i@(repeat y a')) y a'" in exI)
  apply (simp add: not_le)
  apply standard
  apply (metis input2state_nth input2state_within_bounds le_trans length_append_repeat length_list_update linorder_not_le nth_append nth_list_update_neq order_refl)
  by (metis input2state_nth length_append length_input2state_repeat length_list_update length_repeat nth_list_update_eq)

definition join_ir :: "value list \<Rightarrow> registers \<Rightarrow> datastate" where
  "join_ir i r \<equiv> (\<lambda>x. case x of
    R n \<Rightarrow> r $ n |
    I n \<Rightarrow> (input2state i) $ n
  )"

lemmas datastate = join_ir_def input2state_def

lemma join_ir_empty[simp]: "join_ir [] <> = (\<lambda>x. None)"
  apply (rule ext)
  apply (simp add: join_ir_def)
  apply (case_tac x)
   apply (simp add: input2state_def)
  by simp

lemma join_ir_double_exists: "\<exists>i r. join_ir i r v = Some a \<and> join_ir i r v' = Some a"
proof(cases v)
  case (I x1)
  then show ?thesis
    apply (simp add: join_ir_def)
    apply (cases v')
     apply (simp add: input2state_double_exists input2state_exists)
    using input2state_exists by auto
next
  case (R x2)
  then show ?thesis
    apply (simp add: join_ir_def)
    apply (cases v')
    using input2state_exists apply force
    using input2state_double_exists by fastforce
qed

lemma join_ir_double_exists_2: "v \<noteq> v' \<Longrightarrow> \<exists>i r. join_ir i r v = Some a \<and> join_ir i r v' = Some a'"
proof(cases v)
  case (I x1)
  assume "v \<noteq> v'"
  then show ?thesis
    apply (simp add: join_ir_def)
    apply (cases v')
     apply (simp add: I input2state_double_exists_2)
    using I input2state_exists by auto
next
  case (R x2)
  assume "v \<noteq> v'"
  then show ?thesis
    apply (simp add: join_ir_def)
    apply (cases v')
     apply simp
    using R input2state_exists apply auto[1]
    apply (simp add: R)
    apply (rule_tac x="(K$ None)(x2 $:= Some a)(x2a $:= Some a')" in exI)
    by simp
qed

lemma aval_plus_aexp: "aval (a+b) s = aval (Plus a b) s"
  apply (case_tac a)
     apply (case_tac x1)
      apply (case_tac b)
         apply (case_tac x1b)
  by auto

lemma aval_minus_aexp: "aval (a-b) s = aval (Minus a b) s"
  apply (case_tac a)
     apply (case_tac x1)
      apply (case_tac b)
         apply (case_tac x1b)
  by auto

fun aexp_constrains :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" where
  "aexp_constrains (L l) a = (L l = a)" |
  "aexp_constrains (V v) v' = (V v = v')" |
  "aexp_constrains (Plus a1 a2) v = ((Plus a1 a2) = v \<or> (Plus a1 a2) = v \<or> (aexp_constrains a1 v \<or> aexp_constrains a2 v))" |
  "aexp_constrains (Minus a1 a2) v = ((Minus a1 a2) = v \<or> (aexp_constrains a1 v \<or> aexp_constrains a2 v))"

lemma constrains_implies_not_equal: "\<not> aexp_constrains x a \<Longrightarrow> x \<noteq> a"
  using aexp_constrains.elims(3) by blast

fun aexp_same_structure :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" where
  "aexp_same_structure (L v) (L v') = True" |
  "aexp_same_structure (V v) (V v') = True" |
  "aexp_same_structure (Plus a1 a2) (Plus a1' a2') = (aexp_same_structure a1 a1' \<and> aexp_same_structure a2 a2')" |
  "aexp_same_structure (Minus a1 a2) (Minus a1' a2') = (aexp_same_structure a1 a1' \<and> aexp_same_structure a2 a2')" |
  "aexp_same_structure _ _ = False"

fun enumerate_aexp_inputs :: "aexp \<Rightarrow> nat set" where
  "enumerate_aexp_inputs (L _) = {}" |
  "enumerate_aexp_inputs (V (I n)) = {n}" |
  "enumerate_aexp_inputs (V (R n)) = {}" |
  "enumerate_aexp_inputs (Plus v va) = enumerate_aexp_inputs v \<union> enumerate_aexp_inputs va" |
  "enumerate_aexp_inputs (Minus v va) = enumerate_aexp_inputs v \<union> enumerate_aexp_inputs va"

fun enumerate_aexp_inputs_list :: "aexp \<Rightarrow> nat list" where
  "enumerate_aexp_inputs_list (L _) = []" |
  "enumerate_aexp_inputs_list (V (I n)) = [n]" |
  "enumerate_aexp_inputs_list (V (R n)) = []" |
  "enumerate_aexp_inputs_list (Plus v va) = enumerate_aexp_inputs_list v @ enumerate_aexp_inputs_list va" |
  "enumerate_aexp_inputs_list (Minus v va) = enumerate_aexp_inputs_list v @ enumerate_aexp_inputs_list va"

fun enumerate_aexp_regs :: "aexp \<Rightarrow> nat set" where
  "enumerate_aexp_regs (L _) = {}" |
  "enumerate_aexp_regs (V (R n)) = {n}" |
  "enumerate_aexp_regs (V (I _)) = {}" |
  "enumerate_aexp_regs (Plus v va) = enumerate_aexp_regs v \<union> enumerate_aexp_regs va" |
  "enumerate_aexp_regs (Minus v va) = enumerate_aexp_regs v \<union> enumerate_aexp_regs va"

fun enumerate_aexp_regs_list :: "aexp \<Rightarrow> nat list" where
  "enumerate_aexp_regs_list (L _) = []" |
  "enumerate_aexp_regs_list (V (R n)) = [n]" |
  "enumerate_aexp_regs_list (V (I _)) = []" |
  "enumerate_aexp_regs_list (Plus v va) = enumerate_aexp_regs_list v @ enumerate_aexp_regs_list va" |
  "enumerate_aexp_regs_list (Minus v va) = enumerate_aexp_regs_list v @ enumerate_aexp_regs_list va"

lemma enumerate_aexp_inputs_list: "enumerate_aexp_inputs l = set (enumerate_aexp_inputs_list l)"
proof(induct l)
case (L x)
  then show ?case
  by simp
next
  case (V x)
  then show ?case
    apply (cases x)
    by auto
next
  case (Plus l1 l2)
  then show ?case
    by simp
next
  case (Minus l1 l2)
  then show ?case
    by simp
qed

definition max_input :: "aexp \<Rightarrow> nat option" where
  "max_input g = (let inputs = (enumerate_aexp_inputs g) in if inputs = {} then None else Some (Max inputs))"

lemma enumerate_aexp_regs_list: "set (enumerate_aexp_regs_list l) = enumerate_aexp_regs l"
proof(induct l)
case (L x)
then show ?case
  by simp
next
  case (V x)
  then show ?case
    apply (cases x)
    by auto
next
  case (Plus l1 l2)
  then show ?case
    by simp
next
  case (Minus l1 l2)
  then show ?case 
    by simp
qed


lemma enumerate_aexp_regs_empty_reg_unconstrained:
  "enumerate_aexp_regs a = {} \<Longrightarrow> \<forall>r. \<not> aexp_constrains a (V (R r))"
proof(induct a)
case (L x)
  then show ?case
    by simp
next
  case (V x)
  then show ?case
    apply (cases x)
     apply simp
    by simp
next
  case (Plus a1 a2)
  then show ?case
    by simp
next
  case (Minus a1 a2)
  then show ?case
    by simp
qed

lemma set_enumerate_aexp_inputs_list: 
"set (fold (@) (map enumerate_aexp_inputs_list l) []) = (\<Union> (set (map enumerate_aexp_inputs l)))"
proof(induct l)
case Nil
  then show ?case
    by simp
next
case (Cons a l)
  then show ?case
    using enumerate_aexp_inputs_list
    by (simp add: fold_append_concat_rev inf_sup_aci(5))
qed

lemma enumerate_aexp_inputs_empty_input_unconstrained:
  "enumerate_aexp_inputs a = {} \<Longrightarrow> \<forall>r. \<not> aexp_constrains a (V (I r))"
proof(induct a)
case (L x)
  then show ?case
    by simp
next
  case (V x)
  then show ?case
    apply (cases x)
     apply simp
    by simp
next
  case (Plus a1 a2)
  then show ?case
    by simp
next
  case (Minus a1 a2)
  then show ?case
    by simp
qed

lemma input_unconstrained_aval_input_swap:
  "\<forall>i. \<not> aexp_constrains a (V (I i)) \<Longrightarrow> aval a (join_ir i r) = aval a (join_ir i' r)"
proof(induct a)
case (L x)
  then show ?case
    by simp
next
  case (V x)
  then show ?case
    apply (cases x)
     apply simp
    by (simp add: join_ir_def)
next
  case (Plus a1 a2)
  then show ?case
    by simp
next
  case (Minus a1 a2)
  then show ?case
    by simp
qed

lemma input_unconstrained_aval_register_swap:
  "\<forall>i. \<not> aexp_constrains a (V (R i)) \<Longrightarrow> aval a (join_ir i r) = aval a (join_ir i r')"
proof(induct a)
case (L x)
  then show ?case
    by simp
next
  case (V x)
  then show ?case
    apply (cases x)
     apply (simp add: join_ir_def)
    by simp
next
  case (Plus a1 a2)
  then show ?case
    by simp
next
  case (Minus a1 a2)
  then show ?case
    by simp
qed

lemma unconstrained_variable_swap_aval: 
  "\<forall>i. \<not> aexp_constrains a (V (I i)) \<Longrightarrow>
   \<forall>r. \<not> aexp_constrains a (V (R r)) \<Longrightarrow>
   aval a s = aval a s'"
proof(induct a)
case (L x)
  then show ?case
    by simp
next
  case (V x)
  then show ?case
    apply (cases x)
    by auto
next
  case (Plus a1 a2)
  then show ?case
    by simp
next
  case (Minus a1 a2)
  then show ?case
    by simp
qed

end
