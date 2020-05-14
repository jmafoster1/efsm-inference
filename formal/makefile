jedit:
	isabelle jedit -d .
build:
	isabelle build -D .

snippets:
	sed -n '/\\snip{/,/endsnip/p' EFSM/output/document/*.tex > snippets.tex; \
	sed -n '/\\snip{/,/endsnip/p' inference/output/document/*.tex >> snippets.tex; \

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
