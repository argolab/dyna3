LEIN := $(shell which lein 2>/dev/null > /dev/null && echo lein || { if [ ! -f .lein.sh ]; then curl -o .lein.sh https://raw.githubusercontent.com/technomancy/leiningen/stable/bin/lein; chmod +x .lein.sh ; fi; echo './.lein.sh' ; })

SOURCE=$(wildcard src/*/*/*.clj) $(wildcard src/*/*/*.java)
TARGET=target/dyna_backend-0.1.0-SNAPSHOT-standalone.jar

.PHONY: clean all repl test

all: $(TARGET)

clean:
	rm -rf target/

repl: clean
	$(LEIN) repl

test:
	$(LEIN) test



# if we are building the uberjar, then run the clean first as some of the macroexpands might have changed
# and we don't want to have mixed the old and new versions of this
$(TARGET): $(SOURCE)
	rm -rf target/
	$(LEIN) uberjar
