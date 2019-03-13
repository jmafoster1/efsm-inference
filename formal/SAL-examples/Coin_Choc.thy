theory Coin_Choc
imports EFSM_LTL
begin


definition init :: transition where
"init \<equiv> \<lparr>
        Label = (STR ''init''),
        Arity = 0,
        Guard = [],
        Outputs = [],
        Updates = [(R 1, (L (Num 0)))]
      \<rparr>"

definition coin :: transition where
"coin \<equiv> \<lparr>
        Label = (STR ''coin''),
        Arity = 0,
        Guard = [],
        Outputs = [],
        Updates = [(R 1, (Plus (V (R 1)) (L (Num 1))))]
      \<rparr>"

definition vend :: transition where
"vend \<equiv> \<lparr>
        Label = (STR ''coin''),
        Arity = 0,
        Guard = [Ge (V (R 1)) (L (Num 0))],
        Outputs = [],
        Updates = [(R 1, (Minus (V (R 1)) (L (Num 1))))]
      \<rparr>"

definition drinks :: "transition_matrix" where
"drinks \<equiv> {|
          ((0,1), init),
          ((1,1), coin),
          ((1,2), vend)
          |}"

lemma "(not (LabelEq ''vend'') until (LabelEq ''coin'')) (watch drinks t)"


end