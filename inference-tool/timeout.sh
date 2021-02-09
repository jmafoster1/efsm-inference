for F in $(grep -l 'TIME LIMIT' *.out)
do
	echo "rm $F"
	head -n 1 $F;
done;
