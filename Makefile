LEIN := $(shell which lein 2>/dev/null > /dev/null && echo lein || { if [ ! -f .lein.sh ]; then curl -o .lein.sh https://raw.githubusercontent.com/technomancy/leiningen/stable/bin/lein; chmod +x .lein.sh ; fi; echo './.lein.sh' ; })
JAVA ?= java

# this version should match the version in project.clj as that is what is going to be built by lein
JVERSION:= 0.1.0
VERSION:= $(shell git describe --always --long --abbrev=12)-$(shell date '+%Y%m%d')

SOURCE=$(wildcard src/*/*/*.clj) $(wildcard src/*/*/*.java)
JAR_TARGET=target/dyna-$(JVERSION)-SNAPSHOT-standalone.jar
JAR_WITH_PYTHON_INSTALLER=target/dyna-combined-$(JVERSION)-SNAPSHOT-standalone.jar
TARGET=dyna-standalone-$(VERSION).run

PYTHON_MODULE=python_module

PARSER_TARGET=target/classes/dyna/dyna_grammar2Parser.class

.PHONY: clean all repl test

all: $(TARGET)

clean:
	rm -rf target/ dyna-standalone-* python_build/

test:
	_JAVA_OPTIONS='-Ddyna.debug=false -Ddyna.trace_rexpr_construction=false -Ddyna.debug_repl=false -Xss8m -ea' $(LEIN) test

test-debug:
	$(LEIN) test

# some of the tests are failing randomly or somehow failing depending on the order in which they run.  Trying to fix this, but annoying right now with github running of the tests failing
github-test:
	_JAVA_OPTIONS='-Ddyna.debug=false -Ddyna.trace_rexpr_construction=false -Ddyna.debug_repl=false -Xss8m -ea' $(LEIN) test || 	_JAVA_OPTIONS='-Ddyna.debug=false -Ddyna.trace_rexpr_construction=false -Ddyna.debug_repl=false -Xss8m -ea' $(LEIN) retest

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
	$(LEIN) uberjar

$(PARSER_TARGET): src/antlr/dyna/dyna_grammar2.g4
	$(LEIN) do antlr, javac, compile

$(JAR_WITH_PYTHON_INSTALLER): $(JAR_TARGET) $(wildcard dyna_python_module/**/*.py)
	cp $(JAR_TARGET) $(JAR_WITH_PYTHON_INSTALLER)
	find dyna_python_module/ -name '*.pyc' -delete
	jar -uf $(JAR_WITH_PYTHON_INSTALLER) dyna_python_module

$(TARGET): $(JAR_WITH_PYTHON_INSTALLER) standalone-header.sh
	cat standalone-header.sh | sed "s/VERSION_STRING/$(shell git describe --always --long --dirty --abbrev=12 ; date)/" > $(TARGET)
	cat $(JAR_WITH_PYTHON_INSTALLER) >> $(TARGET)
	chmod +x $(TARGET)

test-python: $(JAR_TARGET)
	python dyna_python_module/test/test_wrapper.py

run-class-path:
	@$(LEIN) classpath | awk '/\.jar/'

python-package: $(TARGET)
	@echo 'run "pip install build" first'
	rm -rf python_build/
	cp -r dyna_python_module python_build/
	cp $(TARGET) python_build/dyna/dyna.jar
	cd python_build && python -m build

# example to run a single test
# reset && rlwrap -a lein test :only dyna.core-test/basic-aggregator2
#
# reset b/c lein messes with teh terminal settings,
# rlwrap -a because lein does not echo what is input into the temrinal when running the tests
