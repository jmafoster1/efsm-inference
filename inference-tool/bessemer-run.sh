#!/bin/bash
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=1
#sBatch -c=4
#SBATCH --mem=8000
#SBATCH --time=10:00:00
#SBATCH --mail-user=jmafoster1@sheffield.ac.uk

module load Java/11

echo "bash bessemer-run.sh "$@
cd Documents/efsm-inference/inference-tool
export LD_LIBRARY_PATH=/home/acp17jmf/z3/build
mkdir -p results/$4-$5-$1-$2-$3

srun --export=ALL java -jar target/scala-2.12/inference-tool-assembly-0.1.0-SNAPSHOT.jar -s naive_eq_bonus -p $5 -g $1 -o $2 -u $3 -h same,ws,distinguish -d results/$4-$5-$1-$2-$3 experimental-data/$4-train.json experimental-data/$4-test.json
