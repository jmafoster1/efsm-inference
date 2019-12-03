for i in $(seq 1 $1);
do
	for j in $(seq 1 $1);
	do
		for k in $(seq 1 $1);
		do
			dotdir="dotfiles-"$i"-"$j"-"$k
			mkdir "dotfiles/"$dotdir
			java -jar target/scala-2.12/inference-tool-assembly-0.1.0-SNAPSHOT.jar -h srh --skip -p $i -u $j -g $k --dotfiles "dotfiles/"$dotdir sample-traces/vend1a.json;
		done
	done
done
make dot
shutdown
