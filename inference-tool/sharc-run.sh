module load apps/java
cd Documents/efsm-inference/inference-tool
rm dotfiles/* salfiles/*
java -jar /home/michael/Documents/efsm-inference/inference-tool/target/scala-2.12/inference-tool-assembly-0.1.0-SNAPSHOT.jar -p 3 -u 45 -h same,ws --skip sample-traces/liftDoors2.json
