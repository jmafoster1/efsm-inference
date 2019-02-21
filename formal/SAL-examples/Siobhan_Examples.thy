theory Siobhan_Examples
imports "../EFSM"
begin

definition all_syntax :: transition where
  "all_syntax = \<lparr>
                  Label = STR ''test'',
                  Arity = 4,
                  Guard = [
                            Bc True,
                            Bc False,
                            Eq (Plus (V (R 1)) (V (I 1))) (L (Num 7)),
                            Gt (L (Num 3)) (Minus (V (I 4)) (V (R 3))),
                            Nor (Lt (V (R 2)) (L (Num 100))) (Lt (V (R 2)) (L (Num 100))),
                            Null (V (R 3))
                          ],
                  Outputs = [L (Num 5),
                             L (Str ''hello''),
                             V (R 2),
                             V (I 2),
                             Plus (L (Num 5)) (V (R 2)), Minus (Plus (L (Num 5)) (V (R 2))) (L (Num 5))],
                  Updates = [(R 1, Plus (L (Num 5)) (V (R 2))), (R 2, L (Str ''hello''))]
                \<rparr>"

end