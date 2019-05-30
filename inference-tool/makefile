help:
	@ echo "This tool infers EFSMs from traces. For more information, see README.md"
	@ echo "Tasks in this makefile:"
	@ echo "    dot - compiles the dotfiles in ./dotfiles down to pngs for easy viewing"
	@ echo "  clean - removes everything in ./dotfiles and ./salfiles to clean the project"
	@ echo "    env - exports the lib directory to the sal context path"

env:
	@ echo "$$SALCONTEXTPATH"
	$(eval export SALCONTEXTPATH=$(PWD)/lib/:.:$(SALCONTEXTPATH))
	@ echo "$$SALCONTEXTPATH"

dot:
	DOT_FILES = $(shell find ./ -type f -name '*.dot')
	@ for b in $(basename $(DOT_FILES)) ; do \
	  dot -T png -o $$b.png $$b.dot ; \
	done

clean:
	@ rm dotfiles/*
	@	rm salfiles/*
