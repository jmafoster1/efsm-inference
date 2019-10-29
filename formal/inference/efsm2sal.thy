theory efsm2sal
  imports "EFSM_Dot"
begin

definition replace :: "String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal" where
  "replace s old new = s"

code_printing constant replace \<rightharpoonup> (Scala) "_.replaceAll(_, _)"

definition escape :: "String.literal \<Rightarrow> (String.literal \<times> String.literal) list \<Rightarrow> String.literal" where
  "escape s replacements = fold (\<lambda>(old, new) s'. replace s' old new) replacements s"

definition "replacements = [
  (STR ''/'', STR ''_SOL__''),
  (STR 0x5C+STR 0x5C, STR ''_BSOL__''),
  (STR '' '', STR ''_SPACE__''),
  (STR 0x5C+STR ''('', STR ''_LPAR__''),
  (STR 0x5C+STR '')'', STR ''_RPAR__''),
  (STR 0x5C+STR ''.'', STR ''_PERIOD__''),
  (STR ''@'', STR ''_COMMAT__'')
]"

fun aexp2sal :: "aexp \<Rightarrow> String.literal" where
  "aexp2sal (L (Num n)) = STR ''Some(Num(''+ show_int n + STR ''))''"|
  "aexp2sal (L (value.Str n)) = STR ''Some(Str(String__''+ (if n = STR '''' then STR ''_EMPTY__'' else escape n replacements) + STR ''))''" |
  "aexp2sal (V (vname.I i)) = STR ''Some(i('' + show_nat (i+1) + STR ''))''" |
  "aexp2sal (V (vname.R i)) = STR ''r__'' + show_nat i" |
  "aexp2sal (Plus a1 a2) = STR ''value_plus(''+aexp2sal a1 + STR '', '' + aexp2sal a2 + STR '')''" |
  "aexp2sal (Minus a1 a2) = STR ''value_minus(''+aexp2sal a1 + STR '', '' + aexp2sal a2 + STR '')''"

fun gexp2sal :: "gexp \<Rightarrow> String.literal" where
  "gexp2sal (Bc True) = STR ''True''" |
  "gexp2sal (Bc False) = STR ''False''" |
  "gexp2sal (Eq a1 a2) = STR ''gval(value_eq('' + aexp2sal a1 + STR '', '' + aexp2sal a2 + STR ''))''" |
  "gexp2sal (Gt a1 a2) = STR ''gval(value_gt('' + aexp2sal a1 + STR '', '' + aexp2sal a2 + STR ''))''" |
  "gexp2sal (In v l) = join (map (\<lambda>l'.  STR ''gval(value_eq('' + aexp2sal (V v) + STR '', '' + aexp2sal (L l') + STR ''))'') l) STR '' OR ''" |
  "gexp2sal (Nor g1 g2) = STR ''NOT (gval('' + gexp2sal g1 + STR '') OR gval( '' + gexp2sal g2 + STR ''))''" |
  "gexp2sal (Null a1) = STR ''a1 = None''"

fun guards2sal :: "gexp list \<Rightarrow> String.literal" where
  "guards2sal [] = STR ''TRUE''" |
  "guards2sal G = join (map gexp2sal G) STR '' AND ''"


fun aexp2sal_num :: "aexp \<Rightarrow> nat \<Rightarrow> String.literal" where
  "aexp2sal_num (L (Num n)) m = STR ''Some(Num(''+ show_int n + STR ''))''"|
  "aexp2sal_num (L (value.Str n)) m = STR ''Some(Str(String__''+ (if n = STR '''' then STR ''_EMPTY__'' else escape n replacements) + STR ''))''" |
  "aexp2sal_num (V (vname.I i)) m = STR ''Some(i('' + show_nat (i+1) + STR ''))''" |
  "aexp2sal_num (V (vname.R i)) m = STR ''r__'' + show_nat i + STR ''.'' + show_nat m" |
  "aexp2sal_num (Plus a1 a2) m = STR ''value_plus(''+aexp2sal a1 + STR '', '' + aexp2sal a2 + STR '')''" |
  "aexp2sal_num (Minus a1 a2) m = STR ''value_minus(''+aexp2sal a1 + STR '', '' + aexp2sal a2 + STR '')''"

fun gexp2sal_num :: "gexp \<Rightarrow> nat \<Rightarrow> String.literal" where
  "gexp2sal_num (Bc True) m = STR ''True''" |
  "gexp2sal_num (Bc False) m = STR ''False''" |
  "gexp2sal_num (Eq a1 a2) m = STR ''gval(value_eq('' + aexp2sal_num a1 m + STR '', '' + aexp2sal_num a2 m + STR ''))''" |
  "gexp2sal_num (Gt a1 a2) m = STR ''gval(value_gt('' + aexp2sal_num a1 m + STR '', '' + aexp2sal_num a2 m + STR ''))''" |
  "gexp2sal_num (In v l) m = join (map (\<lambda>l'.  STR ''gval(value_eq('' + aexp2sal_num (V v) m + STR '', '' + aexp2sal_num (L l') m + STR ''))'') l) STR '' OR ''" |
  "gexp2sal_num (Nor g1 g2) m = STR ''NOT (gval('' + gexp2sal_num g1 m + STR '') OR gval( '' + gexp2sal_num g2 m + STR ''))''" |
  "gexp2sal_num (Null a1) m = STR ''a1 = None''"

fun guards2sal_num :: "gexp list \<Rightarrow> nat \<Rightarrow> String.literal" where
  "guards2sal_num [] _ = STR ''TRUE''" |
  "guards2sal_num G m = join (map (\<lambda>g. gexp2sal_num g m) G) STR '' AND ''"

end