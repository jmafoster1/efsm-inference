# Athena 2.0

EFSM inference tool which takes in system execution traces and returns an EFSM model of the observed behaviour. The inference process is formalised in [Isabelle/HOL](https://isabelle.in.tum.de/) and then exported to an executable tool using the code generator.

## Install requirements
In order to run the tool, certain requirements must be met:

1. Install [SBT](https://www.scala-sbt.org/)
2. Install a JDK (I used `openjdk-11-jdk-headless`)
3. Install [z3](https://github.com/Z3Prover/z3) with support for java and move `libz3java.so` and `libz3.so` into a directory in your java.library.path

The tool should now be runnable with the command `sbt run` from the `inference-tool` directory
