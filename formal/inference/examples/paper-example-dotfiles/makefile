DOT_FILES = $(shell find ./ -type f -name '*.dot')
SVG_FILES = $(shell find ./ -type f -name '*.svg')
DATE=`date +'%d/%m/%y'`


dot:
	@ for b in $(basename $(DOT_FILES)) ; do \
	  dot -T pdf -o $$b.pdf $$b.dot ; \
	done

svg:
	@ for b in $(basename $(SVG_FILES)) ; do \
	  inkscape -D -z --file="$$b.svg" --export-pdf="$$b.pdf" --export-latex ; \
	done

images:
	@ make dot
	@ make svg

pdfclean:
	@ for f in $(find . -name '*.pdf')
	do
	  b="${f%.*}"
	  echo "$f"
	  pdf2ps "$b".pdf "$b".ps
		ps2pdf "$b".ps "$b".pdf
		rm "$b".ps
	done

eod:
	git add -A ; \
	git commit -m "end of day $(DATE)" ; \
	git push origin master ; \
