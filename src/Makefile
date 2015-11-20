AGDAFILES := $(wildcard *.agda) $(wildcard **/*.agda)
AGDAIFILES := $(wildcard *.agdai) $(wildcard **/*.agdai)

# Typechecks the Agda development
.PHONY:build
build:
	agda CDGAI.agda 
	agda AGT.agda
	@echo "└[-∵-]┘ all theorem proved"

# Delete all .agdai files (reprove theorems)
.PHONY: clean
clean:
	rm -f $(AGDAIFILES)
