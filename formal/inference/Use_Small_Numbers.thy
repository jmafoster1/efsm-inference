theory Use_Small_Numbers
imports Inference
begin

fun is_Num :: "value \<Rightarrow> bool" where
  "is_Num (Num _) = True" |
  "is_Num _ = False"

definition trace_enumerate_ints :: "execution \<Rightarrow> int list" where
  "trace_enumerate_ints t = map (\<lambda>x. case x of Num n \<Rightarrow> n) (fold List.union (map (\<lambda>(_, inputs, outputs). filter is_Num (inputs@(these outputs))) t) [])"

definition log_enumerate_ints :: "log \<Rightarrow> int list" where
  "log_enumerate_ints l = fold List.union (map trace_enumerate_ints l) []"

lemma distinct_fold_insert: "distinct (fold List.insert a [])"
proof(induct a)
  case Nil
  then show ?case
    by simp
next
  case (Cons a1 a2)
  then show ?case
    by (metis List.union_def distinct_union)
qed

lemma distinct_fold_union_empty: "distinct (fold List.union l [])"
proof(induct l)
case Nil
  then show ?case
    by simp
next
case (Cons a l)
  then show ?case
    apply (simp add: List.union_def)
    using distinct_fold_insert
    by (simp add: fold_invariant)
qed

lemma "distinct (log_enumerate_ints l)"
  by (simp add: log_enumerate_ints_def distinct_fold_union_empty)

definition make_small :: "(int \<Rightarrow> int option) \<Rightarrow> value list \<Rightarrow> value list" where
  "make_small f l = map (\<lambda>x. case x of value.Str s \<Rightarrow> x | Num n \<Rightarrow> case (f n) of Some n' \<Rightarrow> Num n') l"

definition make_small_option :: "(int \<Rightarrow> int option) \<Rightarrow> outputs \<Rightarrow> outputs" where
  "make_small_option f l = map (\<lambda>x. case x of None \<Rightarrow> None | Some (value.Str s) \<Rightarrow> x | Some (Num n) \<Rightarrow> case (f n) of Some n' \<Rightarrow> Some (Num n')) l"

definition enumerate :: "'a list \<Rightarrow> ('a \<times> int) list" where
  "enumerate l = zip l [0..int (length l)]"

definition map_of :: "('a \<times> 'b) list \<Rightarrow> ('a \<Rightarrow> 'b option)" where
  "map_of l = foldr (\<lambda>(a, b) m. m(a:= Some b)) l (\<lambda>x. None)"

definition use_smallest_ints :: "log \<Rightarrow> log" where
  "use_smallest_ints l = (let
    ints = log_enumerate_ints l;
    f = map_of (enumerate ints)
    in map (\<lambda>t. map (\<lambda>(l, inputs, outputs). (l, make_small f inputs, make_small_option f outputs)) t) l
  )"

end