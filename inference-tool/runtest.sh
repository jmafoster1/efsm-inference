for VARIABLE in 1 .. 100
do
	rm salfiles/*; rm dotfiles/*; java -jar target/scala-2.12/inference-tool-assembly-0.1.0-SNAPSHOT.jar -h store,sru --skip sample-traces/vend3.json
done
