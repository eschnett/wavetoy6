DIRS = lib exe test bench
EXE = wavetoy6

all: indent lint build test coverage bench doc exec

setup:
#	TODO: Remove MacPorts (/opt/local) from PATH
	stack setup
	stack build hlint

indent:
#	find $(DIRS) -name '*.hs' -print0 | xargs -0 -P4 -n1 hindent
# 	find $(DIRS) -name '*.hs' -print0 | \
# 		xargs -0 -I '{}' -P4 -n1 brittany -i '{}' -o '{}'

lint: indent
	stack exec hlint -- lint --report --no-exit-code $(DIRS)
build: indent
	stack build
test: indent
#	stack test --coverage
	stack test
coverage: indent test
#	stack hpc report
bench: indent
	stack bench
doc: indent
	stack haddock
exec: indent
	stack exec $(EXE)

clean:
	stack clean
	rm -f $(EXE).cabal
	rm -f report.html

.PHONY: all setup indent lint build test coverage bench doc exec clean
