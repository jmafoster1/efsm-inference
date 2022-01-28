subsection\<open>Value Lexorder\<close>

text\<open>This theory defines a lexicographical ordering on values such that we can build orderings for
arithmetic expressions and guards. Here, numbers are defined as less than strings, else the natural
ordering on the respective datatypes is used.\<close>

theory Value_Lexorder
imports Value
begin

instantiation "value" :: linorder begin
text_raw\<open>\snip{valueorder}{1}{2}{%\<close>
fun less_value :: "value \<Rightarrow> value \<Rightarrow> bool" where
  "(value.Int i) < (Real f) = True" |
  "(value.Int i) < (Str s) = True" |
  "(Real f) < (value.Int i) = False" |
  "(Real f) < (value.Str n) = True" |
  "(Str s) < (value.Int i) = False" |
  "(Str s) < (value.Real f) = False" |
  "(Str s1) < (Str s2) = (s1 < s2)" |
  "(Real f1) < (Real f2) = (f1 < f2)" |
  "(value.Int i1) < (value.Int i2) = (i1 < i2)"
text_raw\<open>}%endsnip\<close>

definition less_eq_value :: "value \<Rightarrow> value \<Rightarrow> bool" where
  "less_eq_value v1 v2 = (v1 < v2 \<or> v1 = v2)"
declare less_eq_value_def [simp]

instance
  apply standard
  subgoal for x y by (induction rule: less_value.induct, auto)
  subgoal for x by simp
  subgoal for x y z
    apply (induction rule: less_value.induct)
            apply simp+
    using less_value.elims(2) apply fastforce
         apply simp
    using less_value.elims(2) apply fastforce
    using less_value.elims(2) apply fastforce
    subgoal for s1 s2 by (cases y, auto)
    subgoal for f1 f2 by (cases y, auto)
    subgoal for i1 i2 by (cases y, auto)
    done
  subgoal for x y
    by (induction rule: less_value.induct, auto)
  subgoal for x y
    by (induction rule: less_value.induct, auto)
  done
end

end
