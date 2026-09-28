COQPROJECT := _CoqProject
COQMAKEFILE := CoqMakefile

.PHONY: all clean distclean check

all: $(COQMAKEFILE)
	+$(MAKE) -f $(COQMAKEFILE) all

$(COQMAKEFILE): $(COQPROJECT)
	opam exec -- rocq makefile -f $(COQPROJECT) -o $(COQMAKEFILE)

check: all
	opam exec -- rocq compile --version
	opam exec -- rocq repl -where

clean:
	@if [ -f $(COQMAKEFILE) ]; then $(MAKE) -f $(COQMAKEFILE) clean; fi

distclean: clean
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf
