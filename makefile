DATE=`date +'%d/%m/%y'`

eod:
	git add -A ; \
	git commit -m "end of day $(DATE)" ; \
	git push origin new-updates ; \
