theory Code_Generation
  imports Inference "HOL-Library.Code_Target_Int" "../FSet_Utils"
begin

declare choice_def [code del]
declare nondeterministic_simulates_def [code del]
declare directly_subsumes_def [code del]

code_printing
  constant "choice" \<rightharpoonup> (Scala) "ScalaChoice" |
  constant "nondeterministic_simulates" \<rightharpoonup> (Scala) "ScalaNondeterministicSimulates" |
  constant "directly_subsumes" \<rightharpoonup> (Scala) "ScalaDirectlySubsumes"

export_code learn observe_trace in Scala
  file "../../src/Inference.scala"

end