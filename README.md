# EFSM Inference

EFSM inference tool which takes in system execution traces and returns an EFSM model of the observed behaviour. The inference process is formalised in [Isabelle/HOL](https://www.isa-afp.org/entries/Extended_Finite_State_Machine_Inference.html) and then exported to an executable tool using the code generator. Further details of the process can be found in \[[1](#subsumptionPaper), [2](#inferencePaper)\].

## Compile and run

### Docker
The tool can be build and run using [Docker](https://www.docker.com) without the need to install any additional dependencies natively.
```
cd inference-tool
docker build -t inference .
docker run inference [<options>] trainfile testfile
```

You may additionally need to pass in "volume mounts" to Docker to enable it to access files on the host, i.e. `trainfile` and `testfile`, or to write logs to the host. This can be done by passing the `-v` option to `docker`, the structure being `-v <path on host>:<path on container>`. Please note that all paths must be absolute.

An example is as follows.
```
docker run -v ~/Documents/efsm-inference/inference-tool/sample-traces:/home/sbtuser/efsm-inference/sample-traces -v ~/Documents/efsm-inference/inference-tool/dotfiles:/home/sbtuser/efsm-inference/dotfiles inference -d dotfiles sample-traces/vend1.json sample-traces/vend2.json
```
Here, we run the container with `sample-traces` and `dotfiles` mounted as volumes. We then use `sample-traces/vend1.json` as our train file and `sample-traces/vend2.json` as our test file. We then use the `-d` option (full list below) to write all output to the `dotfiles` directory.

**NOTE:** To make output files visible after inference has run, you _must_ pass in your intended output directory as a volume to the docker container, otherwise it will disappear when the volume exits.

### Native build from source
In order to run the tool, certain requirements must be met:

1. Install [SBT](https://www.scala-sbt.org/)
2. Install a JDK (I used `openjdk-11-jdk-headless`)
3. Install [z3](https://github.com/Z3Prover/z3) with support for java and move `libz3java.so` and `libz3.so` into a directory in your java.library.path

The tool can be compiled by calling `sbt assembly` from within the `inference-tool` directory. This will create a jar file `inference-tool-assembly-0.1.0-SNAPSHOT.jar` in `inference-tool/scala-2.X/`. This can then be run with `java -jar target/scala-2.12/inference-tool-assembly-0.1.0-SNAPSHOT.jar [options] trainFile testFile`

## CLI Options
```
  --help                   prints this usage text
  -h, --heuristics <heuristic1>,<heuristic2>...
                           heuristics to give the inference process Heuristics.ValueSet(store, inputgen, inc, distinguish, same, ws, lob)
  -k, --k k                The depth of the k-tails (defaults to zero)
  -t, --numTraces numTraces
                           The number of traces in the log to actually use
  -i, --gpIterations GP iterations
                           The number of iterations to run the symbolic regression heuristic for (defaults to 50)
  -s, --strategy strategy  The preferred strategy to rank state merges Strategies.ValueSet(naive, naive_eq_bonus, rank, comprehensive, comprehensiveEQ, eq)
  -n, --nondeterminism nondeterminism checker
                           The preferred definition of nondeterminism - defaults to label, arity, and guard check Nondeterminisms.ValueSet(basic, labar, labar_d)
  -d, --dotfiles dir       The directory in which to save dotfiles produced during the inference process - defaults to 'dotfiles'
  --skip                   Set this flag to skip some model checking tests which should be trivially true
  --mkdir                  Set this flag to skip all inference and just test the making of directories
  -p, --preprocessor preprocessor
                           Preprocessor to use before inference begins Preprocessors.ValueSet(gp, dropGuards, none)
  --small                  Set this flag to map integers down to smaller values
  -l, --level level        The log level {info, debug, warn, error}
  -f, --logFile logFile    The name/location of the logFile
  -g, --guardSeed Random seed for guard GP
  -o, --outputSeed Random seed for output GP
  -u, --updateSeed Random seed for update GP
  trainFile                The json file listing the training traces
  testFile                 The json file listing the test traces
```

The JSON training and test files should contain a list of lists of objects of the form `{"label": "label1", "inputs": ["i1", "i2",...],"outputs": ["o1", "o2",...]},`. Examples can be found within the `inference-tool/experimental-data` directory.

## References
<a name="subsumptionPaper">[1]</a> [Formalising Extended Finite State Machine Transition Merging](https://doi.org/10.1007/978-3-030-30446-1_14)<br/>
Michael Foster, Achim D. Brucker, Ramsay G. Taylor, John Derrick<br/>
In Proceedings of the 20th International Conference on Formal Engineering Methods, 2018

<a name="inferencePaper">[2]</a> [Incorporating Data into EFSM Inference](https://doi.org/10.1007/978-3-030-30446-1_14)<br/>
Michael Foster, Achim D. Brucker, Ramsay G. Taylor, Siobhán North, John Derrick<br/>
In Software Engineering and Formal Methods, 2019

<a name="gpPaper">[2]</a> [Reverse-Engineering EFSMs with Data Dependencies](https://doi.org/10.1007/978-3-031-04673-5_3)<br/>
Michael Foster, John Derrick, Neil Walkinshaw<br/>
In Testing Software and Systems, 2021
