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
	@ for b in $(basename $(shell find ./ -type f -name '*.dot')) ; do \
	  dot -T pdf -o $$b.pdf $$b.dot ; \
	done

stepwise-dot:
	@ rm dotfiles/steps.pdf
	@ for b in $(basename $(shell find ./ -type f -name '*.dot')) ; do \
	  dot -T pdf -o $$b.pdf $$b.dot ; \
	done
	@ pdftk dotfiles/*.pdf cat output dotfiles/steps.pdf
	@ for b in $(basename $(shell find ./ -type f -name '*.dot')) ; do \
	  rm $$b.pdf ; \
	done

clean:
	@ rm dotfiles/*
	@	rm salfiles/*
