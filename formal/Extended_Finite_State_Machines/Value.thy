section\<open>Values\<close>

text\<open>Our EFSM implementation can currently handle integers and strings. Here we define a sum type
which combines these. We also define an arithmetic in terms of values such that EFSMs do not need
to be strongly typed.\<close>

theory Value
imports Trilean HOL.Real
begin

text_raw\<open>\snip{valuetype}{1}{2}{%\<close>
datatype "value" = Int int | Real real | Str String.literal
text_raw\<open>}%endsnip\<close>

text_raw\<open>\snip{maybeIntArith}{1}{2}{%\<close>
fun maybe_arith :: "(real \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> value option \<Rightarrow> value option \<Rightarrow> value option" where
  "maybe_arith f (Some (value.Int x)) (Some (value.Int y)) = Some (value.Int (floor (f x y)))" |
  "maybe_arith f (Some (value.Real x)) (Some (value.Real y)) = Some (value.Real (f x y))" |
  "maybe_arith _ _ _ = None"
text_raw\<open>}%endsnip\<close>

lemma maybe_arith_light_induct:
  assumes int_case: "\<And> f x1 x2. P (maybe_arith f (Some (value.Int x1)) (Some (value.Int x2)) )"
  and real_case: "\<And> f x1 x2. P (maybe_arith f (Some (value.Real x1)) (Some (value.Real x2)) )"
  and str_case: "\<And> f x1 x2. P (maybe_arith f (Some (value.Str x1)) (Some (value.Str x2)) )"
  and none_case: "\<And> f. P (maybe_arith f None None )"
shows "P (maybe_arith f x y)"
  apply (induct x y arbitrary: f rule: maybe_arith.induct)
  using int_case apply fastforce
  using real_case apply fastforce
  using none_case by auto

lemma maybe_arith_not_None:
  "maybe_arith f a b \<noteq> None = ((\<exists>n n'. a = Some (value.Int n) \<and> b = Some (value.Int n')) \<or>
                               (\<exists>n n'. a = Some (value.Real n) \<and> b = Some (value.Real n')))"
  by (induct a b arbitrary: f rule: maybe_arith.induct, auto)

lemma maybe_arith_never_string: "maybe_arith f a b \<noteq> Some (Str x)"
  using maybe_arith.elims by blast

definition "value_plus a b = maybe_arith (+) a b"

lemma value_plus_never_string: "value_plus a b \<noteq> Some (Str x)"
  by (simp add: value_plus_def maybe_arith_never_string)

lemma value_plus_symmetry: "value_plus x y = value_plus y x"
  apply (simp add: value_plus_def)
  apply (case_tac "\<exists>n1 n2. x = Some (value.Int n1) \<and> y = Some (value.Int n2)", clarsimp)
  apply (case_tac "\<exists>n1 n2. x = Some (value.Real n1) \<and> y = Some (value.Real n2)", clarsimp)
  by (metis maybe_arith_not_None)

definition "value_minus = maybe_arith (-)"

lemma value_minus_never_string: "value_minus a b \<noteq> Some (Str x)"
  by (simp add: maybe_arith_never_string value_minus_def)

definition "value_times = maybe_arith (*)"

lemma value_times_never_string: "value_times a b \<noteq> Some (Str x)"
  by (simp add: maybe_arith_never_string value_times_def)

definition "value_divide = maybe_arith (/)"

lemma value_divide_never_string: "value_divide a b \<noteq> Some (Str x)"
  by (simp add: maybe_arith_never_string value_divide_def)

fun MaybeBoolInt :: "(int \<Rightarrow> int \<Rightarrow> bool) \<Rightarrow> value option \<Rightarrow> value option \<Rightarrow> trilean" where
  "MaybeBoolInt f (Some (value.Int a)) (Some (value.Int b)) = (if f a b then true else false)" |
  "MaybeBoolInt _ _ _ = invalid"

lemma MaybeBoolInt_not_num_1:
  "\<forall>n. r \<noteq> Some (value.Int n) \<Longrightarrow> MaybeBoolInt f n r = invalid"
  using MaybeBoolInt.elims by blast

definition value_gt :: "value option \<Rightarrow> value option \<Rightarrow> trilean"  where
  "value_gt a b \<equiv> MaybeBoolInt (>) a b"

definition value_ge :: "value option \<Rightarrow> value option \<Rightarrow> trilean"  where
  "value_ge a b \<equiv> MaybeBoolInt (\<ge>) a b"

definition value_le :: "value option \<Rightarrow> value option \<Rightarrow> trilean"  where
  "value_le a b \<equiv> MaybeBoolInt (\<le>) a b"

fun value_eq :: "value option \<Rightarrow> value option \<Rightarrow> trilean" where
  "value_eq None _ = invalid" |
  "value_eq _ None = invalid" |
  "value_eq (Some a) (Some b) = (if a = b then true else false)"

lemma value_eq_true: "(value_eq a b = true) = (\<exists>x y. a = Some x \<and> b = Some y \<and> x = y)"
  by (cases a; cases b, auto)

lemma value_eq_false: "(value_eq a b = false) = (\<exists>x y. a = Some x \<and> b = Some y \<and> x \<noteq> y)"
  by (cases a; cases b, auto)

lemma value_gt_true_Some: "value_gt a b = true \<Longrightarrow> (\<exists>x. a = Some x) \<and> (\<exists>y. b = Some y)"
  by (cases a; cases b, auto simp: value_gt_def)

lemma value_gt_true: "(value_gt a b = true) = (\<exists>x y. a = Some (value.Int x) \<and> b = Some (value.Int y) \<and> x > y)"
  apply (cases a)
  using value_gt_true_Some apply blast
  apply (cases b)
  using value_gt_true_Some apply blast
  subgoal for aa bb by (cases aa; cases bb, auto simp: value_gt_def)
  done

lemma value_gt_false_Some: "value_gt a b = false \<Longrightarrow> (\<exists>x. a = Some x) \<and> (\<exists>y. b = Some y)"
  by (cases a; cases b, auto simp: value_gt_def)

end
