theory EFSM_Dot
imports Show.Show_Instances Inference
begin

fun value2dot :: "value \<Rightarrow> String.literal" where
  "value2dot (Str s) = String.implode s" |
  "value2dot (Num n) = String.implode (show n)"

fun vname2dot :: "vname \<Rightarrow> String.literal" where
  "vname2dot (I n) = STR ''i<sub>''+String.implode (show n)+STR ''</sub>''" |
  "vname2dot (R n) = STR ''r<sub>''+String.implode (show n)+STR ''</sub>''"

fun aexp2dot :: "aexp \<Rightarrow> String.literal" where
  "aexp2dot (L v) = value2dot v" |
  "aexp2dot (V v) = vname2dot v" |
  "aexp2dot (Plus a1 a2) = (aexp2dot a1)+STR '' + ''+(aexp2dot a2)" |
  "aexp2dot (Minus a1 a2) = (aexp2dot a1)+STR '' - ''+(aexp2dot a2)"

fun gexp2dot :: "gexp \<Rightarrow> String.literal" where
  "gexp2dot (GExp.Bc True) = STR ''True''" |
  "gexp2dot (GExp.Bc False) = STR ''False''" |
  "gexp2dot (GExp.Eq a1 a2) = (aexp2dot a1)+STR '' = ''+(aexp2dot a2)" |
  "gexp2dot (GExp.Lt a1 a2) = (aexp2dot a1)+STR '' &lt; ''+(aexp2dot a2)" |
  "gexp2dot (Nor g1 g2) = STR ''!(''+(gexp2dot g1)+STR ''&or;''+(gexp2dot g2)+STR '')''" |
  "gexp2dot (Null v) = (vname2dot v)+STR '' = NULL''"

fun join :: "String.literal list \<Rightarrow> String.literal \<Rightarrow> String.literal" where
  "join [] _ = STR ''''" |
  "join [a] _ = a" |
  "join (h#t) s = h+s+(join t s)"

primrec guards2dot_aux :: "gexp list \<Rightarrow> String.literal list" where
  "guards2dot_aux [] = []" |
  "guards2dot_aux (h#t) = (gexp2dot h)#(guards2dot_aux t)"

primrec updates2dot_aux :: "update_function list \<Rightarrow> String.literal list" where
  "updates2dot_aux [] = []" |
  "updates2dot_aux (h#t) = ((vname2dot (fst h))+STR '' := ''+(aexp2dot (snd h)))#(updates2dot_aux t)"

primrec outputs2dot :: "output_function list \<Rightarrow> nat \<Rightarrow> String.literal list" where
  "outputs2dot [] _ = []" |
  "outputs2dot (h#t) n = ((STR ''o<sub>''+String.implode (show n))+STR ''</sub> := ''+(aexp2dot h))#(outputs2dot t (n+1))"

fun updates2dot :: "update_function list \<Rightarrow> String.literal" where
  "updates2dot [] = STR ''''" |
  "updates2dot a = STR ''&#91;''+(join (updates2dot_aux a) STR '','')+STR ''&#93;''"

fun guards2dot :: "guard list \<Rightarrow> String.literal" where
  "guards2dot [] = STR ''''" |
  "guards2dot a = STR ''&#91;''+(join (guards2dot_aux a) STR '','')+STR ''&#93;''"

definition latter2dot :: "transition \<Rightarrow> String.literal" where
  "latter2dot t = (let l = (join (outputs2dot (Outputs t) 1) STR '','')+(updates2dot (Updates t)) in (if l = STR '''' then STR '''' else STR ''/''+l))"

definition transition2dot :: "transition \<Rightarrow> String.literal" where
  "transition2dot t = String.implode (Label t)+STR '':''+String.implode (show (Arity t))+(guards2dot (Guard t))+(latter2dot t)"

abbreviation newline :: String.literal where
  "newline \<equiv> STR ''\010''"

abbreviation quote :: String.literal where
  "quote \<equiv> STR ''\"''"

definition efsm2dot :: "transition_matrix \<Rightarrow> String.literal" where
  "efsm2dot e = STR ''digraph EFSM{''+newline+
                STR ''graph [rankdir=''+quote+STR ''LR''+quote+STR '', fontname=''+quote+STR ''Latin Modern Math''+quote+STR ''];''+newline+
                STR ''node [color=''+quote+STR ''black''+quote+STR '', fillcolor=''+quote+STR ''white''+quote+STR '', shape=''+quote+STR ''circle''+quote+STR '', style=''+quote+STR ''filled''+quote+STR '', fontname=''+quote+STR ''Latin Modern Math''+quote+STR ''];''+newline+
                STR ''edge [fontname=''+quote+STR ''Latin Modern Math''+quote+STR ''];''+newline+
                  (join (sorted_list_of_fset (fimage (\<lambda>((from, to), t). String.implode (show from)+STR ''->''+String.implode (show to)+STR ''[label=<''+(transition2dot t)+STR ''>]'') e)) newline)+newline+
                STR ''}''"

definition iefsm2dot :: "iEFSM \<Rightarrow> String.literal" where
  "iefsm2dot e = STR ''digraph EFSM{''+newline+
                 STR ''  graph [rankdir=''+quote+STR ''LR''+quote+STR '', fontname=''+quote+STR ''Latin Modern Math''+quote+STR ''];''+newline+
                 STR ''  node [color=''+quote+STR ''black''+quote+STR '', fillcolor=''+quote+STR ''white''+quote+STR '', shape=''+quote+STR ''circle''+quote+STR '', style=''+quote+STR ''filled''+quote+STR '', fontname=''+quote+STR ''Latin Modern Math''+quote+STR ''];''+newline+
                 STR ''  edge [fontname=''+quote+STR ''Latin Modern Math''+quote+STR ''];''+newline+
                  (join (sorted_list_of_fset (fimage (\<lambda>(uid, (from, to), t).STR ''  ''+String.implode (show from)+STR ''->''+String.implode (show to)+STR ''[label=<(''+String.implode (show uid)+STR '') ''+(transition2dot t)+STR ''>]'') e)) newline)+newline+
                STR ''}''"
end