#!/bin/bash
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=4
#SBATCH --mem=4000
#SBATCH --mail-user=jmafoster1@sheffield.ac.uk

module load Java/11

cd Documents/efsm-inference/inference-tool
export LD_LIBRARY_PATH=/home/acp17jmf/z3/build
rm -r dotfiles/* salfiles/*

srun --export=ALL java -jar ~/inference-tool-assembly-0.1.0-SNAPSHOT.jar -p 3 -u 45 -h same,ws --skip sample-traces/liftDoors2.json
