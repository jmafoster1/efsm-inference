DATE=`date +'%d/%m/%y'`
BRANCH=$(shell git branch | grep \* | cut -d ' ' -f2)

eod:
	git add -A ; \
	git commit -m "end of day $(DATE)" ; \
	git push origin $(BRANCH) ; \
