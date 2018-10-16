theory Transition
imports GExp "not4afp/Show_Unit"
begin

type_synonym guard = "gexp"
type_synonym output_function = "aexp"
type_synonym update_function = "(vname \<times> aexp)"

record transition =
  Label :: string
  Arity :: nat
  Guard :: "guard list"
  Outputs :: "output_function list"
  Updates :: "update_function list"

primrec outputs2string_aux :: "output_function list \<Rightarrow> nat \<Rightarrow> string list" where
  "outputs2string_aux [] _ = []" |
  "outputs2string_aux (h#t) n = (''o''@(show n)@'':=''@(show h))#(outputs2string_aux t (n+1))"

definition outputs2string :: "output_function list \<Rightarrow> string" where
  "outputs2string lst = join (outputs2string_aux lst 1) '',''"

fun updates2string_aux :: "update_function list \<Rightarrow> string list" where
  "updates2string_aux [] = []" |
  "updates2string_aux ((r, u)#t) = ((show r)@'':=''@(show u))#(updates2string_aux t)"

definition updates2string :: "update_function list \<Rightarrow> string" where
  "updates2string lst = join (updates2string_aux lst) '',''"

instantiation transition_ext:: ("show") "show" begin
definition shows_prec_transition_ext :: "nat \<Rightarrow> 'a::show transition_scheme \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_prec_transition_ext n t l = (Label t)@'':''@(show (Arity t))@'':[''@(show (Guard t))@'']/''@(outputs2string (Outputs t))@''[''@(updates2string (Updates t))@'']''@show (more t)@l"

primrec shows_list_transition_ext_aux :: "'a::show transition_scheme list \<Rightarrow> string list" where
  "shows_list_transition_ext_aux [] = ''''" |
  "shows_list_transition_ext_aux (h#t) = (shows_prec 0 h '''')#(shows_list_transition_ext_aux t)"

definition shows_list_transition_ext :: "'a::show transition_scheme list \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_list_transition_ext lst c = (join (shows_list_transition_ext_aux lst) '', '')@c"

instance proof
  fix x::"'a::show transition_ext"
  fix p r s
  show "shows_prec p x (r @ s) = shows_prec p x r @ s"
    by (simp add: shows_prec_append shows_prec_transition_ext_def)
next
  fix xs::"'a::show transition_ext list"
  fix p r s
  show "shows_list xs (r @ s) = shows_list xs r @ s"
  proof (induction xs)
    case Nil
    then show ?case by (simp add: shows_list_transition_ext_def)
  next
    case (Cons a xs)
    then show ?case by (simp add: shows_list_transition_ext_def)
  qed
qed
end

lemma transition_string_not_empty: "(show (t::transition)) \<noteq> ''''"
  apply (case_tac "(Label t) \<noteq> ''''")
   apply (simp add: shows_prec_transition_ext_def)
  by (simp add: shows_prec_transition_ext_def)

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

lemma show_transition_deterministic: "(show (y::('a::show) transition_scheme) = (show (x::'a transition_scheme))) \<Longrightarrow> (x = y)"
  apply (simp add: shows_prec_transition_ext_def)
  apply (case_tac "Label x = Label y")
   apply simp
   apply (case_tac "Arity x = Arity y")
    apply simp
    apply (case_tac "Guard x = Guard y")
     apply simp
    apply (case_tac "Outputs x = Outputs y")
      apply simp
      apply (case_tac "Updates x = Updates y")
       apply simp
  sorry 

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

lemma string_implode_guards_deterministic: "String.implode (show (Guard x)) = String.implode (show (Guard y)) = (show (Guard x) = show (Guard y))"
proof (induct "Guard x")
  case Nil
  then show ?case
    apply (simp add: show_empty_guards string_implode_empty)
    sorry
next
  case (Cons a xa)
  then show ?case sorry
qed

lemma string_implode_outputs_deterministic: "String.implode (show (Outputs x)) = String.implode (show (Outputs y)) = (show (Outputs x) = show (Outputs y))"
proof (induct "Outputs x")
  case Nil
  then show ?case
sorry
next
  case (Cons a xa)
  then show ?case sorry
qed

lemma string_implode_updates_deterministic: "(String.implode (updates2string (Updates x)) = String.implode (updates2string (Updates y))) = ((updates2string (Updates x)) = (updates2string (Updates y)))"
  sorry

lemma show_guards_determinism: "(show (Guard x) = show (Guard y)) = (Guard x = Guard y)"
  sorry

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
                                 else String.implode (Label t1) < String.implode (Label t2))"

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
                                 else String.implode (Label t1) < String.implode (Label t2))"

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
    sorry
qed
end

definition "x = \<lparr>Label = [CHR 0x01], Arity = 1, Guard = [], Outputs = [L (Num (- 1))], Updates = []\<rparr>"
definition "y = \<lparr>Label = [CHR 0x81], Arity = 2, Guard = [], Outputs = [L (Str [CHR 0x81])], Updates = []\<rparr>"

lemma "x \<ge> y"
  apply (simp add: x_def y_def less_eq_transition_ext_def)
  apply (simp only: String.implode_def)
  apply simp
end