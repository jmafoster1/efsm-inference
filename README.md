# Athena 2.0

EFSM inference tool which takes in system execution traces and returns an EFSM model of the observed behaviour. The inference process is formalised in [Isabelle/HOL](https://isabelle.in.tum.de/) and then exported to an executable tool using the code generator.

## Install requirements
In order to run the tool, certain requirements must be met:

1. Install [SBT](https://www.scala-sbt.org/)
2. Install a JDK (I used `openjdk-11-jdk-headless`)
3. Install [z3](https://github.com/Z3Prover/z3) with support for java and move `libz3java.so` and `libz3.so` into a directory in your java.library.path
4. Install [SAL](http://sal.csl.sri.com/) and make sure it's in your `$PATH`

The tool should now be runnable by navigating to the `inference-tool` directory, opening SBT, and executing the command `run sample-traces/vend1.json`.

NOTE: Due to a bug in how the z3 binaries talk to SBT, it may be the case that SBT sometimes cannot find z3. In such cases, the program will throw a `java.lang.UnsatisfiedLinkError`. If this happens, the easiest thing to do is restart SBT and try running the program again.
