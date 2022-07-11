theory Registers
imports "FinFun.FinFun" Value
begin

definition "registers = {A :: (nat, value option) finfun. finfun_default A = None}"
typedef registers = "{A :: (nat, value option) finfun. finfun_default A = None}"
  morphisms regs Abs_regs
  apply (rule_tac x="finfun_const None" in exI)
  by (simp add: finfun_default_const)

subsection \<open>Correspondence Relation\<close>
definition FR :: "(nat, value option) finfun \<Rightarrow> registers \<Rightarrow> bool" where
  "FR = (\<lambda>f r. finfun_default f = None \<and> r = Abs_regs f)"

setup_lifting type_definition_registers

instantiation registers :: equal begin
definition equal_registers :: "registers \<Rightarrow> registers \<Rightarrow> bool" where
  "equal_registers r r' = (regs r = regs r')"
instance
  apply standard
  by (simp add: equal_registers_def regs_inject)
end

lift_definition registers_update :: "registers \<Rightarrow> nat \<Rightarrow> value option \<Rightarrow> registers" is "finfun_update"
  by (simp add: finfun_default_update_const)

lift_definition registers_apply :: "registers \<Rightarrow> nat \<Rightarrow> value option" is "finfun_apply" .
notation registers_apply (infixl "$r" 999)

lemma registers_ext: "(\<And>a. f $r a = g $r a) \<Longrightarrow> f = g"
  by (metis finfun_ext registers_apply.rep_eq regs_inject)

lift_definition registers_to_list :: "registers \<Rightarrow> nat list" is finfun_to_list .

text \<open>A little syntax magic to write larger states compactly:\<close>
lift_definition null_state :: "registers" is "finfun_const None"
  by (simp add: finfun_default_const)
notation null_state ("<>")

nonterminal fupdbinds and fupdbind

syntax
  "_fupdbind" :: "'a \<Rightarrow> 'a \<Rightarrow> fupdbind"             ("(2_ $r:=/ _)")
  ""         :: "fupdbind \<Rightarrow> fupdbinds"             ("_")
  "_fupdbinds":: "fupdbind \<Rightarrow> fupdbinds \<Rightarrow> fupdbinds" ("_,/ _")
  "_fUpdate"  :: "'a \<Rightarrow> fupdbinds \<Rightarrow> 'a"            ("_/'((_)')" [1000, 0] 900)
  "_State" :: "fupdbinds => 'a" ("<_>")

translations
  "_fUpdate f (_fupdbinds b bs)" \<rightleftharpoons> "_fUpdate (_fUpdate f b) bs"
  "f(x$r:=y)" \<rightleftharpoons> "CONST registers_update f x y"
  "_State ms" == "_fUpdate <> ms"
  "_State (_updbinds b bs)" <= "_fUpdate (_State b) bs"

lemma apply_empty_None [simp]: "<> $r x2 = None"
  by (simp add: null_state.rsp null_state_def registers_apply.abs_eq)

lemma update_None: "r $r i = None \<Longrightarrow> (r(i' $r:= a)) $r i = <i' $r:= a> $r i"
  apply (case_tac "i = i'")
   apply (simp add: registers_apply.rep_eq registers_update.rep_eq)
  by (simp add: null_state.rep_eq registers_apply.rep_eq registers_update.rep_eq)

lemma update_value [simp]: "(r(i $r:= a)) $r i = a"
  by (simp add: registers_apply.rep_eq registers_update.rep_eq)

lemma update_irrelevant [simp]: "i \<noteq> i' \<Longrightarrow> (r(i' $r:= a)) $r i = r $r i"
  by (simp add: registers_apply.rep_eq registers_update.rep_eq)

lemma registers_update_twist: "a \<noteq> a' \<Longrightarrow> (f(a $r:= b))(a' $r:= b') = (f(a' $r:= b'))(a $r:= b)"
  by (metis finfun_update_twist registers_update.rep_eq regs_inject)

lemma registers_update_twice [simp]:
  "(f(a $r:= b))(a $r:= b') = f(a $r:= b')"
  by transfer simp

lemma Abs_regs_update: "f \<in> {A. finfun_default A = None} \<Longrightarrow> Abs_regs f = f' \<Longrightarrow> Abs_regs (finfun_update f x a) = f'(x $r:= a)"
  by (metis Abs_regs_inverse registers_update.rep_eq regs_inverse)

lemma ex_default_if_finite: "infinite (UNIV::'a set) \<Longrightarrow> \<exists>n. finfun_apply (f::('a, 'b) finfun) n = finfun_default f"
  apply (case_tac "\<exists>a. a \<notin> {x. finfun_apply (finfun_dom f) x}")
   prefer 2
  using ex_new_if_finite finite_finfun_dom apply blast
  apply (erule_tac exE)
  apply (rule_tac x=a in exI)
  by (simp add: finfun_dom_conv)

lemma ex_fresh_register: "\<exists>n. registers_apply r n = None"
  by (metis (full_types, lifting) ex_default_if_finite infinite_UNIV_nat mem_Collect_eq registers_apply.rep_eq regs)

lemma ex_fresh_register_double: "\<exists>n. registers_apply r n = None \<and> registers_apply r' n = None"
  apply (simp add: registers_apply.rep_eq)
  apply (case_tac "\<exists>a. a \<notin> {x. finfun_apply (finfun_dom (registers.regs r)) x \<or> finfun_apply (finfun_dom (registers.regs r')) x}")
   prefer 2
  using ex_new_if_finite finite_finfun_dom apply blast
  apply (erule_tac exE)
  apply (rule_tac x=a in exI)
  using finfun_dom_conv regs by fastforce

lemma registers_upd_triv [simp]: "f(x $r:= f $r x) = f"
  by (metis finfun_upd_triv registers_apply.rep_eq registers_update.rep_eq regs_inject)

subsubsection \<open>Bundles for concrete syntax\<close>

bundle registers_syntax begin
notation
  registers_update ("_'(_ $r:= _')" [1000, 0, 0] 1000) and
  registers_apply (infixl "$r" 999)
end

bundle no_registers_syntax begin
no_notation
  registers_update ("_'(_ $r:= _')" [1000, 0, 0] 1000) and
  registers_apply (infixl "$r" 999)
end

hide_const registers

end