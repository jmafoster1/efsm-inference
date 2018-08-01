theory Option_Logic
imports AExp
begin

fun MaybeBoolInt :: "(int \<Rightarrow> int \<Rightarrow> bool) \<Rightarrow> value option \<Rightarrow> value option \<Rightarrow> bool option" where
  "MaybeBoolInt f (Some (Num a)) (Some (Num b)) = Some (f a b)" |
  "MaybeBoolInt _ _ _ = None"

abbreviation ValueGt :: "value option \<Rightarrow> value option \<Rightarrow> bool option"  where
  "ValueGt a b \<equiv> MaybeBoolInt (\<lambda>x::int.\<lambda>y::int.(x>y)) a b"

abbreviation ValueLt :: "value option \<Rightarrow> value option \<Rightarrow> bool option"  where
  "ValueLt a b \<equiv> MaybeBoolInt (\<lambda>x::int.\<lambda>y::int.(x<y)) a b"

abbreviation maybe_or :: "bool option \<Rightarrow> bool option \<Rightarrow> bool option" where
  "maybe_or x y \<equiv> (case (x, y) of
    (Some a, Some b) \<Rightarrow> Some (a \<or> b) |
    _ \<Rightarrow> None
  )"

abbreviation maybe_and :: "bool option \<Rightarrow> bool option \<Rightarrow> bool option" where
  "maybe_and x y \<equiv> (case (x, y) of
    (Some a, Some b) \<Rightarrow> Some (a \<and> b) |
    _ \<Rightarrow> None
  )"

abbreviation maybe_not :: "bool option \<Rightarrow> bool option" where
  "maybe_not x \<equiv> (case x of Some a \<Rightarrow> Some (\<not>a) | None \<Rightarrow> None)"

end