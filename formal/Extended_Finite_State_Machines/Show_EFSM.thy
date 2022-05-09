theory Show_EFSM
imports EFSM Show.Show_Instances
begin


lemma "show 5 = ''5''"
  apply (simp add: shows_prec_nat_def)
  oops

instantiation "value" :: "show" begin
fun showsp_value :: "value showsp" where
  "showsp_value p (value.Int a) = shows_string (show a)" |
  "showsp_value p (value.Str a) = shows_string (String.explode a)" |
  "showsp_value p (value.Real a) = shows_string ''a''"

instance
  apply standard
  subgoal for p x r s
    apply (induct x)

end

end