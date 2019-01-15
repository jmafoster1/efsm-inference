theory LinkedIn
imports "../EFSM" EFSM_LTL
begin

definition login :: "transition" where
"login \<equiv> \<lparr>
        Label = ''login'',
        Arity = 1,
        Guard = [Eq (V (I 1)) (L (Str ''free''))],
        Outputs = [],
        Updates = []
      \<rparr>"

definition viewFriend :: "transition" where
"viewFriend \<equiv> \<lparr>
        Label = ''view'',
        Arity = 3,
        Guard = [Eq (V (I 1)) (L (Str ''friendID'')), Eq (V (I 2)) (L (Str ''name'')), Eq (V (I 3)) (L (Str ''HM8p''))],
        Outputs = [L (Str ''friendID''), L (Str ''name''), L (Str ''HM8p'')],
        Updates = []
      \<rparr>"

definition viewOther :: "transition" where
"viewOther \<equiv> \<lparr>
        Label = ''view'',
        Arity = 3,
        Guard = [Eq (V (I 1)) (L (Str ''otherID'')), Eq (V (I 2)) (L (Str ''name'')), Eq (V (I 3)) (L (Str ''4Zof''))],
        Outputs = [L (Str ''otherID''), L (Str ''name''), L (Str ''4Zof'')],
        Updates = []
      \<rparr>"

definition viewOtherOON :: "transition" where
"viewOtherOON \<equiv> \<lparr>
        Label = ''view'',
        Arity = 3,
        Guard = [Eq (V (I 1)) (L (Str ''otherID'')), Eq (V (I 2)) (L (Str ''OUT_OF_NETWORK'')), Eq (V (I 3)) (L (Str ''MNn5''))],
        Outputs = [L (Str ''otherID''), L (Str ''OUT_OF_NETWORK''), L (Str ''MNn5'')],
        Updates = []
      \<rparr>"

definition viewOtherFuzz :: "transition" where
"viewOtherFuzz \<equiv> \<lparr>
        Label = ''view'',
        Arity = 3,
        Guard = [Eq (V (I 1)) (L (Str ''otherID'')), Eq (V (I 2)) (L (Str ''name'')), Eq (V (I 3)) (L (Str ''MNn5''))],
        Outputs = [L (Str ''otherID''), L (Str ''name''), L (Str ''MNn5'')],
        Updates = []
      \<rparr>"

definition pdfFriend :: "transition" where
"pdfFriend \<equiv> \<lparr>
        Label = ''pdf'',
        Arity = 3,
        Guard = [Eq (V (I 1)) (L (Str ''friendID'')), Eq (V (I 2)) (L (Str ''name'')), Eq (V (I 3)) (L (Str ''HM8p''))],
        Outputs = [],
        Updates = []
      \<rparr>"

definition pdfOther :: "transition" where
"pdfOther \<equiv> \<lparr>
        Label = ''pdf'',
        Arity = 3,
        Guard = [Eq (V (I 1)) (L (Str ''otherID'')), Eq (V (I 2)) (L (Str ''name'')), Eq (V (I 3)) (L (Str ''4Zof''))],
        Outputs = [],
        Updates = []
      \<rparr>"

definition pdfOtherOON :: "transition" where
"pdfOtherOON \<equiv> \<lparr>
        Label = ''pdf'',
        Arity = 3,
        Guard = [Eq (V (I 1)) (L (Str ''otherID'')), Eq (V (I 2)) (L (Str ''OUT_OF_NETWORK'')), Eq (V (I 3)) (L (Str ''MNn5''))],
        Outputs = [],
        Updates = []
      \<rparr>"

abbreviation "outside \<equiv> (0::nat)"
abbreviation "loggedIn \<equiv> (1::nat)"
abbreviation "viewDetailed \<equiv> (2::nat)"
abbreviation "viewSummary \<equiv> (3::nat)"
abbreviation "pdfDetailed \<equiv> (4::nat)"
abbreviation "pdfSummary \<equiv> (5::nat)"

definition linkedIn :: transition_matrix where
"linkedIn \<equiv> {|
              ((outside,loggedIn), login),    \<comment> \<open> If we want to go from state 1 to state 2, select will do that \<close>
              ((loggedIn,viewDetailed), viewFriend),
              ((loggedIn, viewDetailed), viewOther), \<comment> \<open> If we want to go from state 2 to state 3, vend will do that \<close>
              ((loggedIn,viewSummary), viewOtherOON),
              ((loggedIn, viewSummary), viewOtherFuzz), \<comment> \<open> If we want to go from state 2 to state 3, vend will do that \<close>
              ((viewSummary, pdfSummary), pdfOtherOON), \<comment> \<open> If we want to go from state 2 to state 3, vend will do that \<close>
              ((viewSummary, pdfDetailed), pdfOther), \<comment> \<open> If we want to go from state 2 to state 3, vend will do that \<close>
              ((viewDetailed, pdfDetailed), pdfFriend),
              ((viewDetailed, pdfDetailed), pdfOther) \<comment> \<open> If we want to go from state 2 to state 3, vend will do that \<close>
         |}"
end
