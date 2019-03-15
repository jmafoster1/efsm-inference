DOT_FILES = $(shell find ./ -type f -name '*.dot')
DATE=`date +'%d/%m/%y'`


dot:
	@ for b in $(basename $(DOT_FILES)) ; do \
	  dot -T png -o $$b.png $$b.dot ; \
		mv $$b.png pngs/$$b.png ;\
	done

clean:
	@ for b in $(basename $(DOT_FILES)) ; do \
	  rm pngs/$$b.png ;\
		rm $$b.dot ;\
	done
