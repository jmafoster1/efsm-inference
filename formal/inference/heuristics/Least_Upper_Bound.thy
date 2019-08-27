theory Least_Upper_Bound
  imports "../Inference"
begin

fun literal_args :: "gexp \<Rightarrow> bool" where
  "literal_args (Bc v) = False" |
  "literal_args (Eq (V _) (L _)) = True" |
  "literal_args (Eq _ _) = False" |
  "literal_args (Lt va v) = False" |
  "literal_args (Null v) = False" |
  "literal_args (Nor v va) = (literal_args v \<and> literal_args va)"

definition "all_literal_args t = fold (\<and>) (map literal_args (Guard t)) True"

definition merge_guards :: "gexp list \<Rightarrow> gexp list \<Rightarrow> gexp list" where
  "merge_guards g1 g2 = (let intersection = (set g1) \<inter> (set g2) in [gOr (fold gAnd (filter (\<lambda>x. x \<notin> intersection) g1) (Bc True)) (fold gAnd g2 (Bc True))])"

fun lob :: update_modifier where
  "lob t1ID t2ID s new old _ = (let
     t1 = (get_by_id new t1ID);
     t2 = (get_by_id new t2ID) in
     if Outputs t1 = Outputs t2 \<and> Updates t1 = Updates t2 \<and> all_literal_args t1 \<and> all_literal_args t2 then
      Some (replace (drop_transitions new {|t2ID|}) t1ID \<lparr>Label = Label t1, Arity = Arity t1, Guard = merge_guards (Guard t1) (Guard t2), Outputs = Outputs t1, Updates = Updates t1\<rparr>)
     else None
   )"

end