theory Drinks_Machine_LTL
imports "../examples/Drinks_Machine" EFSM_LTL
begin

  (* costsMoney: THEOREM drinks |- G(X(cfstate=State_2) => gval(value_ge(r_2, Some(NUM(100))))); *)
lemma costsMoney: "alw(nxt(StateEq (Some 2)) impl (RegGt 2 100)) (watch drinks i)"
  oops

(* neverReachS2: THEOREM drinks |- label=select AND I(1) = STR(String_coke) AND
                                X(label=coin AND I(1) = NUM(100)) AND
                                X(X(label=vend AND I=InputSequence !empty)) => X(X(X(cfstate=State_2)));;*)
lemma neverReachS2:"(((((LabelEq ''select'') aand (InputInxEq 1 (Str ''coke'')))
                    aand
                    (nxt ((LabelEq ''coin'') aand (InputInxEq 1 (Num 100)))))
                    aand
                    (nxt(nxt((LabelEq ''vend'' aand (InputEq []))))))
                    impl
                    (nxt(nxt (nxt (StateEq (Some 2))))))
                    (watch drinks i)"
  oops

end