theory To_String
imports Show.Show_Instances FinFun.FinFun "Inference"
begin

fun join :: "string list \<Rightarrow> string \<Rightarrow> string" where
  "join [] _ = []" |
  "join [a] _ = a" |
  "join (a#b#t) s = (a@s)@(join (b#t) s)"

definition show_list :: "('a :: show) list \<Rightarrow> string" where
  "show_list l = ''[''@(join (map show l) '', '')@'']''"

instantiation finfun :: ("{show, linorder}", "show") "show" begin

definition show_finfun :: "('a, 'b) finfun \<Rightarrow> string" where
  "show_finfun f = (
      ''{''@ (join (map (\<lambda>k. (show k @ '': '' @ show (finfun_apply f k))) (finfun_to_list f)) '', '') @''}''
  )"

definition shows_prec_finfun :: "nat \<Rightarrow> ('a, 'b) finfun \<Rightarrow> string \<Rightarrow> string" where
  "shows_prec_finfun n f s = (show_finfun f) @ s"

definition shows_list_finfun :: "('a, 'b) finfun list \<Rightarrow> string \<Rightarrow> string" where
  "shows_list_finfun l s = (''[''@(join (map show_finfun l) '', '')@'']'') @ s"

instance
  apply standard
   apply (simp add: shows_prec_finfun_def)
  by (simp add: shows_list_finfun_def)
end

instantiation "real" :: "show" begin
definition split_real :: "real \<Rightarrow> (real \<times> real)" where
  "split_real r = (let f = floor r in (f, r-f))"

lemma split_real_int_part: "split_real r = (i, d) \<Longrightarrow> (\<exists>i'::int. i = i')"
  apply (simp add: split_real_def Let_def)
  by auto

lemma split_real_decimal_part: "split_real r = (i, d) \<Longrightarrow> abs d < 1"
  apply (simp add: split_real_def Let_def)
  by linarith

lemma split_real_inverse: "split_real r = (i, d) \<Longrightarrow> i + d = r"
  by (simp add: split_real_def Let_def)

fun showsp_decimal :: "string \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> string \<Rightarrow> string"
where
  "showsp_decimal p n places =
    (if n = 0 then shows_string p else if places = 0 then shows_string ''...'' else
     showsp_decimal p (n*10 - (floor (n * 10))) (places - 1) o shows_string (show (floor (n * 10))))"
declare showsp_decimal.simps [simp del]

definition "show_decimal n p  \<equiv> rev (showsp_decimal '''' n p ''.'')"

definition show_real :: "nat \<Rightarrow> real \<Rightarrow> char list" where
  "show_real precision r = showsp_int 0 (floor r) (show_decimal (r - floor r) precision)"

definition shows_prec_real :: "nat \<Rightarrow> real \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_prec_real precision r s = (show_real precision r) @ s"

definition shows_list_real :: "real list \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_list_real l s = show_list (''[''@(join (map (show_real 3) l) '', '')@'']'') @ s"

instance
  apply standard
   apply (simp add: shows_prec_real_def)
  by (simp add: shows_list_real_def)
end

instantiation "value" :: "show" begin
fun show_value :: "value \<Rightarrow> string" where
  "show_value (value.Int i) = show i" |
  "show_value (value.Real r) = show r" |
  "show_value (value.Str s) = [CHR 0x22] @ String.explode s @ [CHR 0x22]"

definition shows_prec_value :: "nat \<Rightarrow> value \<Rightarrow> string \<Rightarrow> string" where
  "shows_prec_value n v s = show_value v @ s"

definition shows_list_value :: "value list \<Rightarrow> string \<Rightarrow> string" where
  "shows_list_value l s = show_list (''[''@(join (map show_value l) '', '')@'']'') @ s"

instance
  apply standard
   apply (simp add: shows_prec_value_def)
  by (simp add: shows_list_value_def)
end

definition "to_string" :: "('a :: show) \<Rightarrow> String.literal" where
  "to_string a = String.implode (show a)"

end