#!/bin/bash
module load apps/java
cd Documents/efsm-inference/inference-tool
export LD_LIBRARY_PATH=/home/acp17jmf/z3/build
rm -r dotfiles/* salfiles/*
~/jdk-11/bin/java -jar ~/inference-tool-assembly-0.1.0-SNAPSHOT.jar -p 3 -u 45 -h same,ws --skip sample-traces/liftDoors2.json
