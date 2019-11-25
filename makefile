DATE=`date +'%d/%m/%y'`
BRANCH=$(shell git branch | grep \* | cut -d ' ' -f2)

help:
	@ echo "This file has the following tasks:-"
	@ echo "  eod - git commit with the message \"end of day \$Date\""

eod:
	cd inference-tool/src/main/java/mintframework; \
	git add -A ; \
	git commit -m "end of day $(DATE)" ; \
	git push origin master ; \
	cd ../../../..; \
	git add -A ; \
	git commit -m "end of day $(DATE)" ; \
	git push origin $(BRANCH) ; \
