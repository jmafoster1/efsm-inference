#!/bin/bash
#SBATCH --nodes=1
#sBatch -c=4
#SBATCH --mem=8000
#SBATCH --time=24:00:00
#SBATCH --mail-user=jmafoster1@sheffield.ac.uk

module load Java/11

echo "sbatch bessemer-run.sh "$@
export LD_LIBRARY_PATH=/home/acp17jmf/z3/build

IFS='-' # hyphen (-) is set as delimiter
read -ra ADDR <<< "$4" # str is read into an array as tokens separated by IFS
top=${ADDR[0]}
# for i in "${ADDR[@]}"; do # access each element of array
#     echo "$i"
# done
IFS=' ' # reset to default value after usage

conf=${4//$top/''}
if [[ $conf == "-*" ]]
then conf="${conf:1}"
fi
if [[ $conf != "" ]]
then conf="${conf:1}-"
fi

rm -r results/$top/$6/$conf$5/$4-$5-$1-$2-$3
java -jar target/scala-2.12/inference-tool-assembly-0.1.0-SNAPSHOT.jar -s naive_eq_bonus -p $5 -g $1 -o $2 -u $3 -h ws -d results/$top/$6/$conf$5/$4-$5-$1-$2-$3 experimental-data/$top/$top-$6/$4-train.json experimental-data/$top/$top-$6/$4-test.json
