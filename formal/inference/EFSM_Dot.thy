theory EFSM_Dot
imports Inference
begin

fun string_of_digit :: "nat \<Rightarrow> String.literal"
where
  "string_of_digit n =
    (if n = 0 then (STR ''0'')
    else if n = 1 then (STR ''1'')
    else if n = 2 then (STR ''2'')
    else if n = 3 then (STR ''3'')
    else if n = 4 then (STR ''4'')
    else if n = 5 then (STR ''5'')
    else if n = 6 then (STR ''6'')
    else if n = 7 then (STR ''7'')
    else if n = 8 then (STR ''8'')
    else (STR ''9''))"

abbreviation newline :: String.literal where
  "newline \<equiv> STR ''\010''"

abbreviation quote :: String.literal where
  "quote \<equiv> STR ''\"''"

definition shows_string :: "String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal"
where
  "shows_string = (+)"

fun showsp_nat :: "String.literal \<Rightarrow> nat \<Rightarrow> String.literal \<Rightarrow> String.literal"
where
  "showsp_nat p n =
    (if n < 10 then shows_string (string_of_digit n)
    else showsp_nat p (n div 10) o shows_string (string_of_digit (n mod 10)))"
declare showsp_nat.simps [simp del]

definition showsp_int :: "String.literal \<Rightarrow> int \<Rightarrow> String.literal \<Rightarrow> String.literal"
where
  "showsp_int p i =
    (if i < 0 then shows_string STR ''-'' o showsp_nat p (nat (- i)) else showsp_nat p (nat i))"

definition "show_int n  \<equiv> showsp_int ((STR '''')) n ((STR ''''))"
definition "show_nat n  \<equiv> showsp_nat ((STR '''')) n ((STR ''''))"

definition replace_backslash :: "String.literal \<Rightarrow> String.literal" where
  "replace_backslash s = String.implode (fold (@) (map (\<lambda>x. if x = CHR 0x5c then [CHR 0x5c,CHR 0x5c] else [x]) (String.explode s)) '''')"

code_printing
  constant replace_backslash \<rightharpoonup> (Scala) "_.replace(\"\\\\\", \"\\\\\\\\\")"

fun value2dot :: "value \<Rightarrow> String.literal" where
  "value2dot (value.Str s) = quote + replace_backslash s + quote" |
  "value2dot (Num n) = show_int n"

fun vname2dot :: "vname \<Rightarrow> String.literal" where
  "vname2dot (vname.I n) = STR ''i<sub>''+(show_nat (n+1))+STR ''</sub>''" |
  "vname2dot (R n) = STR ''r<sub>''+(show_nat n)+STR ''</sub>''"

fun aexp2dot :: "aexp \<Rightarrow> String.literal" where
  "aexp2dot (L v) = value2dot v" |
  "aexp2dot (V v) = vname2dot v" |
  "aexp2dot (Plus a1 a2) = (aexp2dot a1)+STR '' + ''+(aexp2dot a2)" |
  "aexp2dot (Minus a1 a2) = (aexp2dot a1)+STR '' - ''+(aexp2dot a2)"

fun join :: "String.literal list \<Rightarrow> String.literal \<Rightarrow> String.literal" where
  "join [] _ = (STR '''')" |
  "join [a] _ = a" |
  "join (h#t) s = h+s+(join t s)"

fun gexp2dot :: "gexp \<Rightarrow> String.literal" where
  "gexp2dot (gexp.Bc True) = (STR ''True'')" |
  "gexp2dot (gexp.Bc False) = (STR ''False'')" |
  "gexp2dot (gexp.Eq a1 a2) = (aexp2dot a1)+STR '' = ''+(aexp2dot a2)" |
  "gexp2dot (gexp.Gt a1 a2) = (aexp2dot a1)+STR '' &gt; ''+(aexp2dot a2)" |
  "gexp2dot (gexp.In v l) = (vname2dot v)+STR ''&isin;{''+(join (map value2dot l) STR '', '')+STR ''}''" |
  "gexp2dot (gexp.Nor g1 g2) = STR ''!(''+(gexp2dot g1)+STR ''&or;''+(gexp2dot g2)+STR '')''" |
  "gexp2dot (gexp.Null v) = (aexp2dot v)+STR '' = NULL''"

primrec guards2dot_aux :: "gexp list \<Rightarrow> String.literal list" where
  "guards2dot_aux [] = []" |
  "guards2dot_aux (h#t) = (gexp2dot h)#(guards2dot_aux t)"

lemma gexp2dot_aux_code [code]: "guards2dot_aux l = map gexp2dot l"
  by (induct l, simp_all)

primrec updates2dot_aux :: "update_function list \<Rightarrow> String.literal list" where
  "updates2dot_aux [] = []" |
  "updates2dot_aux (h#t) = ((vname2dot (R (fst h)))+STR '' := ''+(aexp2dot (snd h)))#(updates2dot_aux t)"

lemma updates2dot_aux_code [code]: "updates2dot_aux l = map (\<lambda>(r, u). (vname2dot (R r))+STR '' := ''+(aexp2dot u)) l"
  by (induct l, auto)

fun opred2dot :: "opred \<Rightarrow> String.literal" where
  "opred2dot (Bc True) = STR ''true''" |
  "opred2dot (Bc False) = STR ''false''" |
  "opred2dot (opred.Eq v) = STR ''= '' + (aexp2dot v)" |
  "opred2dot (opred.Gt v) = STR ''> '' + (aexp2dot v)" |
  "opred2dot (opred.Null) = STR ''NONE''" |
  "opred2dot (opred.In l) = STR ''&isin; {''+(join (map value2dot l) STR '', '')+STR ''}''" |
  "opred2dot (opred.Nor p1 p2) = STR ''!('' + opred2dot p1 + STR ''||'' + opred2dot p2 + STR '')''"

primrec outputs2dot :: "output_function list \<Rightarrow> nat \<Rightarrow> String.literal list" where
  "outputs2dot [] _ = []" |
  "outputs2dot (h#t) n = ((STR ''o<sub>''+(show_nat n))+STR ''</sub> ''+(opred2dot h))#(outputs2dot t (n+1))"

fun updates2dot :: "update_function list \<Rightarrow> String.literal" where
  "updates2dot [] = (STR '''')" |
  "updates2dot a = STR ''&#91;''+(join (updates2dot_aux a) STR '', '')+STR ''&#93;''"

fun guards2dot :: "gexp list \<Rightarrow> String.literal" where
  "guards2dot [] = (STR '''')" |
  "guards2dot a = STR ''&#91;''+(join (guards2dot_aux a) STR '', '')+STR ''&#93;''"

definition latter2dot :: "transition \<Rightarrow> String.literal" where
  "latter2dot t = (let l = (join (outputs2dot (Outputs t) 1) STR '', '')+(updates2dot (Updates t)) in (if l = (STR '''') then (STR '''') else STR ''/''+l))"

definition transition2dot :: "transition \<Rightarrow> String.literal" where
  "transition2dot t = (Label t)+STR '':''+(show_nat (Arity t))+(guards2dot (Guard t))+(latter2dot t)"

definition efsm2dot :: "transition_matrix \<Rightarrow> String.literal" where
  "efsm2dot e = STR ''digraph EFSM{''+newline+
                STR ''  graph [rankdir=''+quote+(STR ''LR'')+quote+STR '', fontname=''+quote+STR ''Latin Modern Math''+quote+STR ''];''+newline+
                STR ''  node [color=''+quote+(STR ''black'')+quote+STR '', fillcolor=''+quote+(STR ''white'')+quote+STR '', shape=''+quote+(STR ''circle'')+quote+STR '', style=''+quote+(STR ''filled'')+quote+STR '', fontname=''+quote+STR ''Latin Modern Math''+quote+STR ''];''+newline+
                STR ''  edge [fontname=''+quote+STR ''Latin Modern Math''+quote+STR ''];''+newline+newline+
                  STR ''  s0[fillcolor=''+quote+STR ''gray''+quote+STR '', label=<s<sub>0</sub>>];''+newline+
                  (join (map (\<lambda>s. STR ''  s''+show_nat s+STR ''[label=<s<sub>'' +show_nat s+ STR ''</sub>>];'') (sorted_list_of_fset (EFSM.S e - {|0|}))) (newline))+newline+newline+
                  (join ((map (\<lambda>((from, to), t). STR ''  s''+(show_nat from)+STR ''->s''+(show_nat to)+STR ''[label=<<i>''+(transition2dot t)+STR ''</i>>];'') (sorted_list_of_fset e))) newline)+newline+
                STR ''}''"

definition iefsm2dot :: "iEFSM \<Rightarrow> String.literal" where
  "iefsm2dot e = STR ''digraph EFSM{''+newline+
                 STR ''  graph [rankdir=''+quote+(STR ''LR'')+quote+STR '', fontname=''+quote+STR ''Latin Modern Math''+quote+STR ''];''+newline+
                 STR ''  node [color=''+quote+(STR ''black'')+quote+STR '', fillcolor=''+quote+(STR ''white'')+quote+STR '', shape=''+quote+(STR ''circle'')+quote+STR '', style=''+quote+(STR ''filled'')+quote+STR '', fontname=''+quote+STR ''Latin Modern Math''+quote+STR ''];''+newline+
                 STR ''  edge [fontname=''+quote+STR ''Latin Modern Math''+quote+STR ''];''+newline+newline+
                  (join (map (\<lambda>s. STR ''  s''+show_nat s+STR ''[label=<s<sub>'' +show_nat s+ STR ''</sub>>];'') (sorted_list_of_fset (S e - {|0|}))) (newline))+newline+newline+
                  (join ((map (\<lambda>(uid, (from, to), t). STR ''  s''+(show_nat from)+STR ''->s''+(show_nat to)+STR ''[label=<<i> (''+show_nat uid+STR '')''+(transition2dot t)+STR ''</i>>];'') (sorted_list_of_fset e))) newline)+newline+
                STR ''}''"

abbreviation newline_str :: string where
  "newline_str \<equiv> ''\010''"

abbreviation quote_str :: string where
  "quote_str \<equiv> ''0x22''"

definition iefsm2dot_str :: "iEFSM \<Rightarrow> string" where
  "iefsm2dot_str e = ''digraph EFSM{''@newline_str@
                 ''  graph [rankdir=''@quote_str@''LR''@quote_str@'', fontname=''@quote_str@''Latin Modern Math''@quote_str@''];''@newline_str@
                 ''  node [color=''@quote_str@''black''@quote_str@'', fillcolor=''@quote_str@''white''@quote_str@'', shape=''@quote_str@''circle''@quote_str@'', style=''@quote_str@''filled''@quote_str@'', fontname=''@quote_str@''Latin Modern Math''@quote_str@''];''@newline_str@
                 ''  edge [fontname=''@quote_str@''Latin Modern Math''@quote_str@''];''@newline_str@
                  (String.explode (join (sorted_list_of_fset (fimage (\<lambda>(uid, (from, to), t).STR ''  ''+(show_nat from)+STR ''->''+(show_nat to)+STR ''[label=<(''+(show_nat uid)+STR '') ''+(transition2dot t)+STR ''>]'') e)) newline)@newline_str)@
                ''}''"
end