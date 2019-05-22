build:
	isabelle build -d . michael-efsm

snippets:
	isabelle build -d . sal-snips
	sed -n '/\\snip{/,/endsnip/p' output/document/*.tex > snippets.tex
	mv snippets.tex ~/Documents/verifying-trace-properties/figures

clean:
	@find . -name "*thy~" -exec rm {} \;
