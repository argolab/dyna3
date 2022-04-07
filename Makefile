LEIN := $(shell which lein 2>/dev/null > /dev/null && echo lein || { if [ ! -f .lein.sh ]; then curl -o .lein.sh https://raw.githubusercontent.com/technomancy/leiningen/stable/bin/lein; chmod +x .lein.sh ; fi; echo './.lein.sh' ; })
JAVA ?= java

VERSION=0.1.0

SOURCE=$(wildcard src/*/*/*.clj) $(wildcard src/*/*/*.java)
JAR_TARGET=target/dyna-$(VERSION)-SNAPSHOT-standalone.jar
TARGET=dyna-standalone-$(VERSION)

PARSER_TARGET=target/classes/dyna/dyna_grammar2Parser.class

.PHONY: clean all repl test

all: $(TARGET)

clean:
	rm -rf target/ $(TARGET)

test:
	_JAVA_OPTIONS='-Ddyna.debug=false -Ddyna.trace_rexpr_construction=false' $(LEIN) test

test-debug:
	$(LEIN) test

# start the repl for dyna code from the source directory
repl: dyna-repl
dyna-repl: $(PARSER_TARGET)
	$(JAVA) -cp `$(LEIN) classpath` dyna.DynaMain


# start the repl for clojure code
clj-repl: clean
	$(LEIN) repl


# if we are building the uberjar, then run the clean first as some of the macroexpands might have changed
# and we don't want to have mixed the old and new versions of this
$(JAR_TARGET): $(SOURCE)
	rm -rf target/
#$(LEIN) do antlr, javac, compile, uberjar
	$(LEIN) uberjar

$(PARSER_TARGET): src/antlr/dyna/dyna_grammar2.g4
	$(LEIN) do antlr, javac, compile


$(TARGET): $(JAR_TARGET) standalone-header.sh
	cat standalone-header.sh $(JAR_TARGET) > $(TARGET)
	chmod +x $(TARGET)


# example to run a single test
# reset && rlwrap -a lein test :only dyna.core-test/basic-aggregator2
#
# reset b/c lein messes with teh terminal settings,
# rlwrap -a because lein does not echo what is input into the temrinal when running the tests
