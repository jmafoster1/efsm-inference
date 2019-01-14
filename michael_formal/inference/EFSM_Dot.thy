theory EFSM_Dot
imports Show.Show_Instances Inference
begin

fun value2dot :: "value \<Rightarrow> string" where
  "value2dot (Str s) = s" |
  "value2dot (Num n) = show n"

fun vname2dot :: "vname \<Rightarrow> string" where
  "vname2dot (I n) = ''i<sub>''@(show n)@''</sub>''" |
  "vname2dot (R n) = ''r<sub>''@(show n)@''</sub>''"

fun aexp2dot :: "aexp \<Rightarrow> string" where
  "aexp2dot (L v) = value2dot v" |
  "aexp2dot (V v) = vname2dot v" |
  "aexp2dot (Plus a1 a2) = (aexp2dot a1)@''+''@(aexp2dot a2)" |
  "aexp2dot (Minus a1 a2) = (aexp2dot a1)@''-''@(aexp2dot a2)"

fun gexp2dot :: "gexp \<Rightarrow> string" where
  "gexp2dot (GExp.Bc b) = show b" |
  "gexp2dot (GExp.Eq a1 a2) = (aexp2dot a1)@'' = ''@(aexp2dot a2)" |
  "gexp2dot (GExp.Lt a1 a2) = (aexp2dot a1)@'' &lt; ''@(aexp2dot a2)" |
  "gexp2dot (Nor g1 g2) = ''!(''@(gexp2dot g1)@''&or;''@(gexp2dot g2)@'')''" |
  "gexp2dot (Null v) = (vname2dot v)@'' = NULL''"

fun join :: "string list \<Rightarrow> string \<Rightarrow> string" where
  "join [] _ = ''''" |
  "join [a] _ = a" |
  "join (h#t) s = h@s@(join t s)"

primrec guards2dot_aux :: "gexp list \<Rightarrow> string list" where
  "guards2dot_aux [] = []" |
  "guards2dot_aux (h#t) = (gexp2dot h)#(guards2dot_aux t)"

primrec updates2dot_aux :: "update_function list \<Rightarrow> string list" where
  "updates2dot_aux [] = []" |
  "updates2dot_aux (h#t) = ((vname2dot (fst h))@'' := ''@(aexp2dot (snd h)))#(updates2dot_aux t)"

primrec outputs2dot :: "output_function list \<Rightarrow> nat \<Rightarrow> string list" where
  "outputs2dot [] _ = []" |
  "outputs2dot (h#t) n = ((''o<sub>''@(show n))@''</sub> := ''@(aexp2dot h))#(outputs2dot t (n+1))"

fun updates2dot :: "update_function list \<Rightarrow> string" where
  "updates2dot [] = []" |
  "updates2dot a = ''&#91;''@(join (updates2dot_aux a) '','')@''&#93;''"

fun guards2dot :: "guard list \<Rightarrow> string" where
  "guards2dot [] = []" |
  "guards2dot a = ''&#91;''@(join (guards2dot_aux a) '','')@''&#93;''"

definition latter2dot :: "transition \<Rightarrow> string" where
  "latter2dot t = (let l = (join (outputs2dot (Outputs t) 1) '','')@(updates2dot (Updates t)) in (if l = [] then [] else ''/''@l))"

definition transition2dot :: "transition \<Rightarrow> string" where
  "transition2dot t = (Label t)@'':''@(show (Arity t))@(guards2dot (Guard t))@(latter2dot t)"

abbreviation newline :: string where
  "newline \<equiv> [CHR ''\010'']"

abbreviation quote :: string where
  (* "quote \<equiv> [CHR ''\"'']" *)
  "quote \<equiv> ''0x22''"

definition efsm2dot :: "transition_matrix \<Rightarrow> string" where
  "efsm2dot e = ''digraph EFSM{''@newline@
                  ''graph [rankdir=''@quote@''LR''@quote@'', fontname=''@quote@''Latin Modern Math''@quote@''];''@newline@
                  ''node [color=''@quote@''black''@quote@'', fillcolor=''@quote@''white''@quote@'', shape=''@quote@''circle''@quote@'', style=''@quote@''filled''@quote@'', fontname=''@quote@''Latin Modern Math''@quote@''];''@newline@
                  ''edge [fontname=''@quote@''Latin Modern Math''@quote@''];''@newline@
                  (join (sorted_list_of_fset (fimage (\<lambda>((from, to), t). (show from)@''->''@(show to)@''[label=<''@(transition2dot t)@''>]'') e)) newline)@newline@
                ''}''"

definition iefsm2dot :: "iEFSM \<Rightarrow> string" where
  "iefsm2dot e = ''digraph EFSM{''@newline@
                  ''  graph [rankdir=''@quote@''LR''@quote@'', fontname=''@quote@''Latin Modern Math''@quote@''];''@newline@
                  ''  node [color=''@quote@''black''@quote@'', fillcolor=''@quote@''white''@quote@'', shape=''@quote@''circle''@quote@'', style=''@quote@''filled''@quote@'', fontname=''@quote@''Latin Modern Math''@quote@''];''@newline@
                  ''  edge [fontname=''@quote@''Latin Modern Math''@quote@''];''@newline@
                  (join (sorted_list_of_fset (fimage (\<lambda>(uid, (from, to), t). ''  ''@(show from)@''->''@(show to)@''[label=<(''@(show uid)@'') ''@(transition2dot t)@''>]'') e)) newline)@newline@
                ''}''"



end