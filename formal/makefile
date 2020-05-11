jedit:
	isabelle jedit -d .
build:
	isabelle build -D .

snippets:
	isabelle build -d . EFSM
	sed -n '/\\snip{/,/endsnip/p' output/document/*.tex > snippets.tex
	mv snippets.tex ~/Documents/verifying-trace-properties/figures/efsm-snippets.tex

clean:
	@find . -name "*thy~*" -exec rm {} \;

commit:
	cd EFSM ; \
	git add -A ; \
	git commit -m "$m" ; \
	git push origin master ; \
	cd .. ; \
	git add -A ; \
	git commit -m "$m" ; \
	git push origin master
