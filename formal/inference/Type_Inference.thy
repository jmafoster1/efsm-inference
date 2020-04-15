theory Type_Inference
  imports "EFSM.GExp" "HOL-Library.FSet" FinFun.FinFun
begin

unbundle finfun_syntax

datatype type = NUM | STRING | UNBOUND

fun aexp_get_variables :: "vname aexp \<Rightarrow> vname list" where
  "aexp_get_variables (L _) = []" |
  "aexp_get_variables (V v) = [v]" |
  "aexp_get_variables (Plus a1 a2) = remdups (aexp_get_variables a1 @ aexp_get_variables a2)" |
  "aexp_get_variables (Minus a1 a2) = remdups (aexp_get_variables a1 @ aexp_get_variables a2)" |
  "aexp_get_variables (Times a1 a2) = remdups (aexp_get_variables a1 @ aexp_get_variables a2)"

definition assign_all :: "type \<Rightarrow> vname list \<Rightarrow> (vname \<times> type) list" where
  "assign_all t l = remdups (map (\<lambda>v. (v, t)) l)"

fun add_pair :: "(vname \<times> type) \<Rightarrow> (vname \<times> type) list \<Rightarrow> (vname \<times> type) list" where
  "add_pair p [] = [p]" |
  "add_pair (v, t) ((v', t')#tail) = (
    if v = v' then
      if t = UNBOUND then
        (v, t')#tail
      else
        (v, t)#tail
    else (v', t')#(add_pair (v, t) tail))"

primrec add_pairs :: "(vname \<times> type) list \<Rightarrow> (vname \<times> type) list \<Rightarrow> (vname \<times> type) list" where
  "add_pairs [] l = l" |
  "add_pairs (h#t) l = (add_pair h (add_pairs t l))"

fun is_num :: "value \<Rightarrow> bool" where
  "is_num (Num _) = True" |
  "is_num (Str _) = False"

fun is_str :: "value \<Rightarrow> bool" where
  "is_str (Num _) = False" |
  "is_str (Str _) = True"

fun infer_types_aux :: "vname gexp \<Rightarrow> ((vname \<times> type) list \<times> (vname \<times> vname) list)" where
  "infer_types_aux (Bc _) = ([], [])" |
  "infer_types_aux (Gt a1 a2) = (assign_all NUM ((aexp_get_variables a1) @ (aexp_get_variables a2)), [])" |
  "infer_types_aux (Nor g1 g2) = (let (t1, g1) = infer_types_aux g1; (t2, g2) = infer_types_aux g2 in ((add_pairs t1  t2, remdups (g1@g2))))" |
  "infer_types_aux (Eq (L _) (L _)) = ([], [])" |
  "infer_types_aux (In v va) = (if \<forall>v' \<in> set va. is_num v' then ([(v, NUM)], []) else
                                if \<forall>v' \<in> set va. is_str v' then ([(v, STRING)], []) else ([], []))" |
  "infer_types_aux (Eq (V v1) (V v2)) = ([], [(v1, v2)])" |
  "infer_types_aux (Eq (V v) (L (Str s))) = ([(v, STRING)], [])" |
  "infer_types_aux (Eq (V v) (L (Num s))) = ([(v, NUM)], [])" |
  "infer_types_aux (Eq (L (Str s)) (V v)) = ([(v, STRING)], [])" |
  "infer_types_aux (Eq (L (Num s)) (V v)) = ([(v, NUM)], [])" |
  "infer_types_aux (Eq _ _) = ([], [])"

fun collapse_group :: "(vname \<times> vname) \<Rightarrow> vname list list \<Rightarrow> vname list list" where
  "collapse_group (v1, v2) [] = [remdups [v1, v2]]" |
  "collapse_group (v1, v2) (h#t) = (
     if List.member h v1 \<or> List.member h v2 then
       (remdups (v1#v2#h))#t
     else
       collapse_group (v1, v2) t
   )"

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

definition infer_types :: "vname gexp \<Rightarrow> (vname \<Rightarrow>f type) option" where
  "infer_types g = (let (types, groups) = infer_types_aux g;
                        type_lst = assign_group_types (collapse_groups groups []) types in
                    if type_check type_lst then
                      Some (fun_of type_lst UNBOUND)
                    else None
                   )"

fun type_of :: "vname aexp \<Rightarrow> (vname \<Rightarrow>f type) \<Rightarrow> type" where
  "type_of (L (Num _)) _ = NUM" |
  "type_of (L (Str _)) _ = STRING" |
  "type_of (V v) types = finfun_apply types v" |
  "type_of (Plus _ _) _ = NUM" |
  "type_of (Minus _ _) _ = NUM" |
  "type_of (Times _ _) _ = NUM"

fun type_check_aux :: "type \<Rightarrow> type \<Rightarrow> bool" where
  "type_check_aux NUM NUM = True" |
  "type_check_aux STRING STRING = True" |
  "type_check_aux UNBOUND _ = True" |
  "type_check_aux _ UNBOUND = True" |
  "type_check_aux NUM _ = False" |
  "type_check_aux _ NUM = False"

definition aexp_type_check :: "vname aexp \<Rightarrow> vname aexp \<Rightarrow> (vname \<Rightarrow>f type) \<Rightarrow> bool" where
  "aexp_type_check a1 a2 t = type_check_aux (type_of a1 t) (type_of a2 t)"

end
