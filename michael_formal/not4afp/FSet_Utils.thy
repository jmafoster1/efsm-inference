theory FSet_Utils
  imports "~~/src/HOL/Library/FSet"
begin
lemma fset_both_sides: "(Abs_fset s = f) = (fset (Abs_fset s) = fset f)"
  by (simp add: fset_inject)
end