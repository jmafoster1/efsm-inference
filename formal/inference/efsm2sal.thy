theory efsm2sal
  imports "EFSM_Dot"
begin

fun aexp2sal :: "aexp \<Rightarrow> String.literal" where
  "aexp2sal (L (Num n)) = STR ''Some(Num(''+ show_int n + STR ''))''"|
  "aexp2sal (L (value.Str n)) = STR ''Some(Str(String_''+ n + STR ''))''" |
  "aexp2sal (V (vname.I i)) = STR ''Some(i('' + show_nat (i+1) + STR ''))''" |
  "aexp2sal (V (vname.R i)) = STR ''r('' + show_nat i + STR '')''" |
  "aexp2sal (Plus a1 a2) = STR ''value_plus(''+aexp2sal a1 + STR '', '' + aexp2sal a2 + STR '')''" |
  "aexp2sal (Minus a1 a2) = STR ''value_minus(''+aexp2sal a1 + STR '', '' + aexp2sal a2 + STR '')''"

fun gexp2sal :: "gexp \<Rightarrow> String.literal" where
  "gexp2sal (Bc True) = STR ''True''" |
  "gexp2sal (Bc False) = STR ''False''" |
  "gexp2sal (Eq a1 a2) = STR ''gval(value_eq('' + aexp2sal a1 + STR '', '' + aexp2sal a2 + STR ''))''" |
  "gexp2sal (Lt a1 a2) = STR ''gval(value_lt('' + aexp2sal a1 + STR '', '' + aexp2sal a2 + STR ''))''" |
  "gexp2sal (In v l) = join (map (\<lambda>l'.  STR ''gval(value_eq('' + aexp2sal (V v) + STR '', '' + aexp2sal (L l') + STR ''))'') l) STR '' OR ''" |
  "gexp2sal (Nor g1 g2) = STR ''NOT (gval('' + gexp2sal g1 + STR '') OR gval( '' + gexp2sal g2 + STR ''))''" |
  "gexp2sal (Null a1) = STR ''a1 = None''"

fun guards2sal :: "gexp list \<Rightarrow> String.literal" where
  "guards2sal [] = STR ''TRUE''" |
  "guards2sal G = join (map gexp2sal G) STR '' AND''"

end