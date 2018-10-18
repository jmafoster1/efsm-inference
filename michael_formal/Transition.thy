theory Transition
imports GExp "not4afp/Show_Unit"
begin

type_synonym guard = "gexp"
type_synonym output_function = "aexp"
type_synonym update_function = "(vname \<times> aexp)"

record transition =
  Label :: String.literal
  Arity :: nat
  Guard :: "guard list"
  Outputs :: "output_function list"
  Updates :: "update_function list"

primrec outputs2string_aux :: "output_function list \<Rightarrow> nat \<Rightarrow> string list" where
  "outputs2string_aux [] _ = []" |
  "outputs2string_aux (h#t) n = (''o''@(show n)@'':=''@(show h))#(outputs2string_aux t (n+1))"

definition outputs2string :: "output_function list \<Rightarrow> string" where
  "outputs2string lst = join (outputs2string_aux lst 1) '',''"

fun updates2string :: "update_function list \<Rightarrow> string" where
  "updates2string [] = ''''" |
  "updates2string [(r, u)] = ((show r)@'':=''@(show u))" |
  "updates2string ((r, u)#t) = ((show r)@'':=''@(show u))@(updates2string t)"

lemma transition_equality: "((x::transition) = y) = ((Label x) = (Label y) \<and>
                                (Arity x) = (Arity y) \<and>
                                (Guard x) = (Guard y) \<and>
                                (Outputs x) = (Outputs y) \<and>
                                (Updates x) = (Updates y))"
proof
  fix x y :: transition
  assume "x = y"
  show "Label x = Label y \<and> Arity x = Arity y \<and> Guard x = Guard y \<and> Outputs x = Outputs y \<and> Updates x = Updates y"
    by (simp add: \<open>x = y\<close>)
next
  fix x y :: transition
  assume "Label x = Label y \<and> Arity x = Arity y \<and> Guard x = Guard y \<and> Outputs x = Outputs y \<and> Updates x = Updates y"
  show "x = y"
    by (simp add: \<open>Label x = Label y \<and> Arity x = Arity y \<and> Guard x = Guard y \<and> Outputs x = Outputs y \<and> Updates x = Updates y\<close>)
qed

lemma shows_string_deterministic: "show (x::string) = show (y::string) \<Longrightarrow> x = y"
proof (induct x)
  case Nil
  then show ?case
    apply (simp add: shows_prec_list_def)
    by (simp add: shows_list_char_def shows_string_def)
next
  case (Cons a x)
  then show ?case
    apply (simp add: shows_prec_list_def)
    by (simp add: shows_list_char_def shows_string_def)
qed

lemma string_implode_empty: "String.implode '''' = STR ''''"
  by (metis String.implode_explode_eq zero_literal.rep_eq)

lemma show_empty_guards: "([] = Guard x) = (show (Guard x) = '''')"
proof
  show "[] = Guard x \<Longrightarrow> show (Guard x) = []"
    by (simp add: shows_prec_list_def)
next
  show "show (Guard x) = [] \<Longrightarrow> [] = Guard x "
  proof (induct "Guard x")
    case Nil
    then show ?case
      by (simp add: shows_prec_list_def)
  next
    case (Cons a xa)
    then show ?case
      apply (simp add: shows_prec_list_def)
      by (metis append_is_Nil_conv show_g_not_empty shows_list_gexp.elims)
  qed
qed

(* This uses an smt but I'm very very glad it's true! *)
lemma implode_true: "String.implode ''True'' = STR ''True''"
  apply (simp add: String.implode_def)
  by (metis Literal.rep_eq literal.explode_inverse zero_literal.rep_eq)

lemma implode_x_equality: "(\<forall>x. x \<in> set X \<longrightarrow> String.ascii_of x = x) \<and> (\<forall>y. y \<in> set Y \<longrightarrow> String.ascii_of y = y) \<Longrightarrow>  String.implode X = String.implode Y \<Longrightarrow> show X = show Y"
proof (induct X)
  case Nil
  then show ?case
    apply (simp add: string_implode_empty)
    by (metis Nil_is_map_conv String.explode_implode_eq zero_literal.rep_eq)
next
  case (Cons a x)
  then show ?case
    apply simp
    by (smt Cons.prems(2) String.explode_implode_eq String.implode_explode_eq String.not_digit7_ascii_of list.map(2) literal.explode_cases mem_Collect_eq)
qed

lemma show_nat_ok: "\<forall>x. x \<in> set (show (g::nat)) \<longrightarrow> String.ascii_of x = x"
proof (induct g)
  case 0
  then show ?case
    by (simp add: shows_prec_nat_def)
next
  case (Suc g)
  then show ?case
    apply (simp add: shows_prec_nat_def)
    apply safe
     apply (case_tac "sod (Suc g) = CHR ''0''")
      apply simp
     apply (case_tac "sod (Suc g) = CHR ''1''")
      apply simp
     apply (case_tac "sod (Suc g) = CHR ''2''")
      apply simp
     apply (case_tac "sod (Suc g) = CHR ''3''")
      apply simp
     apply (case_tac "sod (Suc g) = CHR ''4''")
      apply simp
     apply (case_tac "sod (Suc g) = CHR ''5''")
      apply simp
     apply (case_tac "sod (Suc g) = CHR ''6''")
      apply simp
     apply (case_tac "sod (Suc g) = CHR ''7''")
      apply simp
     apply (case_tac "sod (Suc g) = CHR ''8''")
     apply simp
     apply (case_tac "sod (Suc g) = CHR ''9''")
      apply simp
    using sod_values apply blast
    apply (case_tac "Suc g div 10")
     apply simp
    apply simp
    apply safe
     apply (smt String.ascii_of_Char sod_values)
    sorry
qed

lemma show_int_ok: "\<forall>x. x \<in> set (show (g::int)) \<longrightarrow> String.ascii_of x = x"
proof (induct g)
  case (nonneg n)
  then show ?case
    by (simp add: shows_prec_int_def show_nat_ok)
next
  case (neg n)
  then show ?case
    by (simp add: shows_prec_int_def show_nat_ok shows_string_def)
qed

lemma show_vname_ok: "\<forall>x. x \<in> set (show (g::vname)) \<longrightarrow> String.ascii_of x = x"
proof (cases g)
  case (I x1)
  then show ?thesis
    by (simp add: show_nat_ok)
next
  case (R x2)
  then show ?thesis
    by (simp add: show_nat_ok)
qed

lemma show_value_ok: "\<forall>x. x \<in> set (show (g::value)) \<longrightarrow> String.ascii_of x = x"
proof (cases g)
  case (Num x1)
  then show ?thesis
    by (simp add: show_int_ok)
next
  case (Str x2)
  then show ?thesis
    apply simp
    apply (simp add: shows_prec_literal_def)
    using String.ascii_of_idem literal.explode by blast
qed

lemma show_aexp_ok: "\<forall>x. x \<in> set (show (g::aexp)) \<longrightarrow> String.ascii_of x = x"
proof (induct g)
  case (L x)
  then show ?case
    apply (cases x)
    using show_value_ok shows_prec_aexp.simps(1) apply presburger
    using show_value_ok shows_prec_aexp.simps(1) by presburger
next
  case (V x)
  then show ?case
    by (simp add: show_vname_ok)
next
  case (Plus g1 g2)
  then show ?case
    by simp
next
  case (Minus g1 g2)
  then show ?case
    by simp
qed

lemma show_gexp_ok: "\<forall>x. x \<in> set (show (g::gexp)) \<longrightarrow> String.ascii_of x = x"
proof (induct g)
  case (Bc v)
  then show ?case
    apply (cases v)
     apply simp
    by simp
next
  case (Eq a1 a2)
  then show ?case
    by (simp add: show_aexp_ok)
next
  case (Gt x1a x2)
  then show ?case
    by (simp add: show_aexp_ok)
next
  case (Nor g1 g2)
  then show ?case
    by simp
next
  case (Null x)
  then show ?case
    by (simp add: show_vname_ok)
qed

lemma show_gexp_list_ok: "\<forall>x. x \<in> set (show (g::gexp list)) \<longrightarrow> String.ascii_of x = x"
proof (induct g)
  case Nil
  then show ?case
    by (simp add: shows_prec_list_def)
next
  case (Cons g gs)
  then show ?case
  proof (induct gs)
    case Nil
    then show ?case
      by (simp add: show_gexp_ok shows_prec_list_def)
  next
    case (Cons a as)
    then show ?case
      by (simp add: show_gexp_ok shows_prec_list_def)
  qed
qed

lemma show_aexp_list_ok: "\<forall>x. x \<in> set (show (g::aexp list)) \<longrightarrow> String.ascii_of x = x"
proof (induct g)
case Nil
  then show ?case
      by (simp add: shows_prec_list_def)
next
  case (Cons a as)
  then show ?case
  proof (induct as)
    case Nil
    then show ?case
      by (simp add: shows_prec_list_def show_aexp_ok)
  next
    case (Cons a as)
    then show ?case
      by (simp add: shows_prec_list_def show_aexp_ok)
  qed
qed

lemma updates2string_ok: "\<forall>x. x \<in> set (updates2string (g::update_function list)) \<longrightarrow> String.ascii_of x = x"
proof (induct g)
  case Nil
  then show ?case
    by simp
next
  case (Cons a as)
  then show ?case
  proof (induct as)
    case Nil
    then show ?case
      apply simp
      apply (cases a)
      apply simp
      using show_aexp_ok show_vname_ok by blast
  next
    case (Cons u us)
    then show ?case
      apply (cases a)
      apply (cases u)
      apply simp
      using show_aexp_ok show_vname_ok by blast
  qed
qed


lemma cons_gexp_show_list: "String.implode (show ((x::gexp) # xs)) = String.implode (show ((y::gexp) # ys)) \<Longrightarrow> show (x # xs) = show (y # ys)"
  using implode_x_equality show_gexp_list_ok shows_string_deterministic by blast
  
lemma string_implode_guards_deterministic_contra: "(show (x::guard list) \<noteq> show (y::guard list)) = (String.implode (show (x::gexp list)) \<noteq> String.implode (show (y::guard list)))"
proof (induct x)
  case Nil
  then show ?case
    apply (simp add: shows_prec_list_def string_implode_empty)
    by (metis Nil_is_map_conv String.explode_implode_eq string_implode_empty zero_literal.rep_eq)
next
  case (Cons a x)
  then show ?case
    apply (simp add: shows_prec_list_def string_implode_empty)
    by (metis Nil_is_map_conv String.explode_implode_eq cons_gexp_show_list neq_Nil_conv shows_list_gexp.simps(1) shows_prec_list_def)
qed

lemma string_implode_guards_deterministic: "String.implode (show (x::gexp list)) = String.implode (show (y::guard list)) = (show (x::guard list) = show (y::guard list))"
  using string_implode_guards_deterministic_contra by auto

lemma cons_aexp_show_list: "String.implode (show ((x::aexp) # xs)) = String.implode (show ((y::aexp) # ys)) \<Longrightarrow> show (x # xs) = show (y # ys)"
  using implode_x_equality show_aexp_list_ok shows_string_deterministic by blast

lemma string_implode_outputs_deterministic_contra: "(show (x::output_function list) \<noteq> show (y::output_function list)) = (String.implode (show (x::output_function list)) \<noteq> String.implode (show (y::output_function list)))"
proof (induct x)
  case Nil
  then show ?case
    apply (simp add: shows_prec_list_def string_implode_empty)
    by (metis implode.rep_eq list.map(2) neq_Nil_conv string_implode_empty zero_literal.rep_eq)
next
  case (Cons x xs)
  then show ?case
    apply (simp add: shows_prec_list_def string_implode_empty)
    by (metis implode_x_equality show_aexp_list_ok shows_prec_list_def shows_string_deterministic)
qed

lemma string_implode_outputs_deterministic: "String.implode (show (Outputs x)) = String.implode (show (Outputs y)) = (show (Outputs x) = show (Outputs y))"
  using string_implode_outputs_deterministic_contra by auto

lemma string_implode_updates_deterministic_contra: "(updates2string (x::update_function list) \<noteq> updates2string (y::update_function list)) = (String.implode (updates2string (x::update_function list)) \<noteq> String.implode (updates2string (y::update_function list)))"
  proof (induct x)
    case Nil
    then show ?case
      apply (simp add: string_implode_empty)
      by (metis Nil_is_map_conv String.explode_implode_eq string_implode_empty)
  next
    case (Cons a x)
    then show ?case
      apply (simp add: shows_prec_list_def string_implode_empty)
      by (metis implode_x_equality shows_string_deterministic updates2string_ok)
  qed

lemma string_implode_updates_deterministic: "(String.implode (updates2string (Updates x)) = String.implode (updates2string (Updates y))) = ((updates2string (Updates x)) = (updates2string (Updates y)))"
  using string_implode_updates_deterministic_contra by auto

lemma show_guards_determinism_aux: "(show ((g::gexp) # gs) = show ((a::gexp) # as)) = (g # gs = a # as)"
proof (induct gs)
  case Nil
  then show ?case
  proof
    show "show [g] = show (a # as) \<Longrightarrow> [g] = a # as"
    proof (induct as)
      case Nil
      then show ?case
        apply (simp add: shows_prec_list_def)
        sorry
    next
      case (Cons a as)
      then show ?case sorry
    qed
  next
    show "[g] = a # as \<Longrightarrow> show [g] = show (a # as)"
      by simp
  qed
next
  case (Cons a gs)
  then show ?case sorry
qed

lemma show_guards_determinism: "(show (x::guard list) = show (y::guard list)) = (x = y)"
proof (induct x)
  case Nil
  then show ?case
    apply (simp add: shows_prec_list_def string_implode_empty)
    by (metis append_Cons append_Nil append_is_Nil_conv show_g_not_empty shows_list_gexp.elims shows_list_gexp.simps(1))
next
  case (Cons g gs)
  then show ?case
  proof (induct y)
    case Nil
    then show ?case
      apply (simp add: shows_prec_list_def)
      using show_g_not_empty shows_list_gexp.elims by force
  next
    case (Cons a as)
    then show ?case
      by (simp add: show_guards_determinism_aux)
  qed
qed

lemma show_outputs_determinism: "(show (Outputs x) = show (Outputs y)) = (Outputs x = Outputs y)"
  sorry

lemma show_updates_determinism: "(updates2string (Updates x) = updates2string (Updates y)) = (Updates x = Updates y)"
  sorry



instantiation "transition_ext" :: (linorder) linorder begin
definition less_eq_transition_ext :: "'a::linorder transition_scheme \<Rightarrow> 'a transition_scheme \<Rightarrow> bool" where
"less_eq_transition_ext t1 t2 = (if Label t1 = Label t2 then
                                   (if Arity t1 = Arity t2 then
                                      (if String.implode (show (Guard t1)) = String.implode (show (Guard t2)) then
                                         (if String.implode (show (Outputs t1)) = String.implode (show (Outputs t2)) then
                                            (if String.implode (updates2string (Updates t1)) = String.implode (updates2string (Updates t2)) then
                                               less_eq (more t1) (more t2)
                                           else String.implode (updates2string (Updates t1)) < String.implode (updates2string (Updates t2)))
                                         else String.implode (show (Outputs t1)) < String.implode (show (Outputs t2)))
                                       else String.implode (show (Guard t1)) < String.implode (show (Guard t2)))
                                    else (Arity t1) < (Arity t2))
                                 else Label t1 < Label t2)"

definition less_transition_ext :: "'a::linorder transition_scheme \<Rightarrow> 'a transition_scheme \<Rightarrow> bool" where
"less_transition_ext t1 t2 = (if Label t1 = Label t2 then
                                   (if Arity t1 = Arity t2 then
                                      (if String.implode (show (Guard t1)) = String.implode (show (Guard t2)) then
                                         (if String.implode (show (Outputs t1)) = String.implode (show (Outputs t2)) then
                                            (if String.implode (updates2string (Updates t1)) = String.implode (updates2string (Updates t2)) then
                                               less (more t1) (more t2)
                                           else String.implode (updates2string (Updates t1)) < String.implode (updates2string (Updates t2)))
                                         else String.implode (show (Outputs t1)) < String.implode (show (Outputs t2)))
                                       else String.implode (show (Guard t1)) < String.implode (show (Guard t2)))
                                    else (Arity t1) < (Arity t2))
                                 else Label t1 < Label t2)"

instance proof
  fix x y::"('a::linorder) transition_ext"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (smt less_eq_transition_ext_def leD leI less_transition_ext_def not_less_iff_gr_or_eq)
next
  fix x::"('a::linorder) transition_ext"
  show "x \<le> x"
    by (simp add: less_eq_transition_ext_def)
next
  fix x y z::"('a::linorder) transition_ext"
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (smt less_eq_transition_ext_def less_trans not_less_iff_gr_or_eq order_trans)
next
  fix x y::"('a::linorder) transition_ext"
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    apply (simp add: less_eq_transition_ext_def)
    apply (case_tac "Label x = Label y")
     apply simp
     apply (case_tac "Arity x = Arity y")
      apply simp
      apply (case_tac "String.implode (show (Guard x)) = String.implode (show (Guard y))")
       apply simp
       apply (case_tac "String.implode (show (Outputs x)) = String.implode (show (Outputs y))")
        apply simp
        apply (case_tac "String.implode (updates2string (Updates x)) = String.implode (updates2string (Updates y))")
         apply (simp add: string_implode_guards_deterministic string_implode_outputs_deterministic string_implode_updates_deterministic)
         apply (simp add: show_guards_determinism show_outputs_determinism show_updates_determinism)
         apply (simp add: string_implode_guards_deterministic string_implode_outputs_deterministic string_implode_updates_deterministic)
         apply (simp add: string_implode_guards_deterministic string_implode_outputs_deterministic string_implode_updates_deterministic)
         apply (simp add: string_implode_guards_deterministic string_implode_outputs_deterministic string_implode_updates_deterministic)
         apply (simp add: string_implode_guards_deterministic string_implode_outputs_deterministic string_implode_updates_deterministic)
    by (simp add: string_implode_guards_deterministic string_implode_outputs_deterministic string_implode_updates_deterministic)
next
  fix x y::"('a::linorder) transition_ext"
  show "x \<le> y \<or> y \<le> x "
    apply safe
    using less_eq_transition_ext_def by auto
qed
end
end