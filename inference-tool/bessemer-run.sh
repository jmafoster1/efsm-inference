#!/bin/bash
#SBATCH --nodes=1
#SBATCH --ntasks-per-node=1
#sBatch -c=4
#SBATCH --mem=8000
#SBATCH --time=02:00:00
#SBATCH --mail-user=jmafoster1@sheffield.ac.uk

module load Java/11

echo "bash bessemer-run.sh "$@
export LD_LIBRARY_PATH=/home/acp17jmf/z3/build

java -jar target/scala-2.12/inference-tool-assembly-0.1.0-SNAPSHOT.jar -s naive_eq_bonus -p $5 -g $1 -o $2 -u $3 -h ws -d results/$4/$6/$5/$4-$5-$1-$2-$3 experimental-data/$4/$4-$6/$4-train.json experimental-data/$4/$4-$6/$4-test.json
