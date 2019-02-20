theory Type_Inference
  imports "../GExp" "~~/src/HOL/Library/FSet" FinFun.FinFun
begin

unbundle finfun_syntax

datatype type = NULL | NUM | STRING | UNBOUND

fun aexp_get_variables :: "aexp \<Rightarrow> vname list" where
  "aexp_get_variables (L _) = []" |
  "aexp_get_variables (V v) = [v]" |
  "aexp_get_variables (Plus a1 a2) = remdups (aexp_get_variables a1 @ aexp_get_variables a2)" |
  "aexp_get_variables (Minus a1 a2) = remdups (aexp_get_variables a1 @ aexp_get_variables a2)"

definition assign_all :: "type \<Rightarrow> vname list \<Rightarrow> (vname \<times> type) list" where
  "assign_all t l = remdups (map (\<lambda>v. (v, t)) l)"

fun infer_types_aux :: "gexp \<Rightarrow> ((vname \<times> type) list \<times> (vname \<times> vname) list)" where
  "infer_types_aux (Bc _) = ([], [])" |
  "infer_types_aux (Null v) = (assign_all NULL (aexp_get_variables v), [])" |
  "infer_types_aux (Lt a1 a2) = (assign_all NUM ((aexp_get_variables a1) @ (aexp_get_variables a2)), [])" |
  "infer_types_aux (Nor g1 g2) = (let (t1, g1) = infer_types_aux g1; (t2, g2) = infer_types_aux g2 in ((remdups (t1 @ t2), remdups (g1@g2))))" |
  "infer_types_aux (Eq (L _) (L _)) = ([], [])" |
  "infer_types_aux (Eq (V v1) (V v2)) = ([], [(v1, v2)])" |
  "infer_types_aux (Eq (V v) (L (Str s))) = ([(v, STRING)], [])" |
  "infer_types_aux (Eq (V v) (L (Num s))) = ([(v, NUM)], [])" |
  "infer_types_aux (Eq (L (Str s)) (V v)) = ([(v, STRING)], [])" |
  "infer_types_aux (Eq (L (Num s)) (V v)) = ([(v, NUM)], [])" |
  "infer_types_aux (Eq a (Plus a1 a2)) = (assign_all NUM ((aexp_get_variables (Plus a1 a2)) @ (aexp_get_variables a)), [])" |
  "infer_types_aux (Eq a (Minus a1 a2)) = (assign_all NUM ((aexp_get_variables (Minus a1 a2)) @ (aexp_get_variables a)), [])" |
  "infer_types_aux (Eq (Plus a1 a2) a) = (assign_all NUM ((aexp_get_variables (Plus a1 a2)) @ (aexp_get_variables a)), [])" |
  "infer_types_aux (Eq (Minus a1 a2) a) = (assign_all NUM ((aexp_get_variables (Minus a1 a2)) @ (aexp_get_variables a)), [])"

fun collapse_group :: "(vname \<times> vname) \<Rightarrow> vname list list \<Rightarrow> vname list list" where
  "collapse_group (v1, v2) [] = [[v1, v2]]" |
  "collapse_group (v1, v2) (h#t) = (if ListMem v1 h \<or> ListMem v2 h then ((remdups (v1#v2#h))#t) else collapse_group (v1, v2) t)"

primrec collapse_groups :: "(vname \<times> vname) list \<Rightarrow> vname list list \<Rightarrow> vname list list" where
  "collapse_groups [] g = g" |
  "collapse_groups (h#t) g = collapse_groups t (collapse_group h g)"

primrec get_type_of :: "vname \<Rightarrow> (vname \<times> type) list \<Rightarrow> type" where
  "get_type_of _ [] = UNBOUND" |
  "get_type_of v (h#t) = (if fst h = v then snd h else get_type_of v t)"

primrec get_group_type :: "vname list \<Rightarrow> (vname \<times> type) list \<Rightarrow> type" where
  "get_group_type [] _ = UNBOUND" |
  "get_group_type (h#t) types = (let gt = get_type_of h types in (if gt = UNBOUND then get_group_type t types else gt))"

primrec assign_group_types :: "vname list list \<Rightarrow> (vname \<times> type) list \<Rightarrow> (vname \<times> type) list" where
  "assign_group_types [] types = types" |
  "assign_group_types (h#t) types = assign_group_types t (assign_all (get_group_type h types) h)"

primrec fun_of :: "('a \<times> 'b) list \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow>f 'b)" where
  "fun_of [] b = (K$ b)" |
  "fun_of (h#t) b = (fun_of t b)(fst h $:= snd h)"

definition type_check_var :: "vname \<Rightarrow> (vname \<times> type) list \<Rightarrow> bool" where
  "type_check_var v l = (card (set (map (\<lambda>(_, t). t) (filter (\<lambda>(v', _). v' = v) l))) \<ge> 1)"

definition type_check :: "(vname \<times> type) list \<Rightarrow> bool" where
  "type_check l = (\<forall>x \<in> set l. type_check_var (fst x) l)"

definition infer_types :: "gexp \<Rightarrow> (vname \<Rightarrow>f type) option" where
  "infer_types g = (let (types, groups) = infer_types_aux g;
                        type_lst = assign_group_types (collapse_groups groups []) types in
                    if type_check type_lst then
                      Some (fun_of type_lst UNBOUND)
                    else None
                   )"
end