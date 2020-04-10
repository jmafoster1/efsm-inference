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
	@ for b in $(basename $(shell find . -path ./results -prune -o -name '*.dot' -print)) ; do \
	  dot -T pdf -o $$b.pdf $$b.dot & \
	done

stepwise-dot:
	@ if test -f "dotfiles/steps.pdf"; then \
		rm dotfiles/steps.pdf ; \
	fi
	@ for b in $(basename $(shell find . -path ./pdfs -prune -o -name '*.dot' -print)) ; do \
	  dot -T pdf -o $$b.pdf $$b.dot ; \
	done
	@ pdftk dotfiles/*.pdf cat output dotfiles/steps.pdf
	@ for b in $(basename $(shell find . -path ./pdfs -prune -o -name '*.dot' -print)) ; do \
	  rm $$b.pdf ; \
	done

clean:
	@ rm dotfiles/*
	@	rm salfiles/*

eod:
	cd ..; \
	make eod
