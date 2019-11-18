END=1
for i in $(seq 1 $END);
do
	dotdir="dotfiles-"$i
	mkdir $dotdir
	java -jar target/scala-2.12/inference-tool-assembly-0.1.0-SNAPSHOT.jar -h srh --skip --dotfiles $dotdir sample-traces/vend1a.json; make dot;
done
shutdown
