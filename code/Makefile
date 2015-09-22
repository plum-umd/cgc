.PHONY: build clean release

AGDAFILES := $(wildcard *.agda) $(wildcard **/*.agda)
AGDAIFILES := $(wildcard *.agdai) $(wildcard **/*.agdai)

# Typechecks the Agda development
build:
	agda CDGAI.agda
	@echo "└[-∵-]┘ all theorem proved"

# Delete all .agdai files (reprove theorems)
clean:
	rm -f $(AGDAIFILES)

release:
	./release.sh
