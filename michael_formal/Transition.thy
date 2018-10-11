theory Transition
imports GExp
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
  "outputs2string_aux (h#t) n = (''o''@(showsp_nat 1 n '''')@'':=''@(shows_prec 1 h ''''))#(outputs2string_aux t (n+1))"

definition outputs2string :: "output_function list \<Rightarrow> string" where
  "outputs2string lst = join (outputs2string_aux lst 1) '',''"

fun updates2string_aux :: "update_function list \<Rightarrow> string list" where
  "updates2string_aux [] = []" |
  "updates2string_aux ((r, u)#t) = ((shows_prec 1 r '''')@'':=''@(shows_prec 1 u ''''))#(updates2string_aux t)"

definition updates2string :: "update_function list \<Rightarrow> string" where
  "updates2string lst = join (updates2string_aux lst) '',''"

instantiation transition_ext:: ("show") "show" begin
definition shows_prec_transition_ext :: "nat \<Rightarrow> 'a::show transition_scheme \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_prec_transition_ext n t c = (Label t)@'':''@(showsp_nat 1 (Arity t) '''')@'':[''@(shows_list (Guard t) '''')@'']/''@(outputs2string (Outputs t))@''[''@(updates2string (Updates t))@'']''@shows_prec n (more t) c"

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

lemma transition_string_not_empty: "(shows_prec n (t::transition) l) \<noteq> ''''"
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

lemma "((shows_prec n (y::transition) l) = (shows_prec n x l)) = (x = y)"
proof
  fix x y :: transition
  fix n l
  show "shows_prec n y l = shows_prec n x l \<Longrightarrow> x = y"
    apply (simp add: shows_prec_transition_ext_def)
    apply (simp add: transition_equality)
   

  

instantiation "transition_ext" :: ("show") linorder begin
definition less_eq_transition_ext :: "'a::show transition_scheme \<Rightarrow> 'a transition_scheme \<Rightarrow> bool" where
"less_eq_transition_ext t1 t2 = less_eq (String.implode (shows_prec 1 t1 '''')) (String.implode (shows_prec 1 t2 ''''))"

definition less_transition_ext :: "'a::show transition_scheme \<Rightarrow> 'a transition_scheme \<Rightarrow> bool" where
"less_transition_ext t1 t2 = less (String.implode (shows_prec 1 t1 '''')) (String.implode (shows_prec 1 t2 ''''))"

instance proof
  fix x y::"'a::show transition_ext"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    apply (simp add: less_transition_ext_def less_eq_transition_ext_def)
    by auto
next
  fix x::"'a::show transition_ext"
  show "x \<le> x"
    by (simp add: Transition.less_eq_transition_ext_def)
next
  fix x y z::"'a::show transition_ext"
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    using less_eq_transition_ext_def by auto
next
  fix x y::"'a::show transition_ext"
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    apply (simp add: less_eq_transition_ext_def)
    
end


end