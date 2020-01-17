#!/bin/bash
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=1
#SBATCH --mem=4000
#SBATCH --time=15:00:00
#SBATCH --mail-user=jmafoster1@sheffield.ac.uk

module load Java/11

cd Documents/efsm-inference/inference-tool
export LD_LIBRARY_PATH=/home/acp17jmf/z3/build
mkdir liftdoors-$1-$2

srun --export=ALL java -jar target/scala-2.12/inference-tool-assembly-0.1.0-SNAPSHOT.jar -g $1 -p $2 -u $3 -h same,ws,distinguish -d $4-$1-$2-$3 experimental-data/$4-train.json experimental-data/$4-test.json
