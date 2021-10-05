LEIN := $(shell which lein 2>/dev/null > /dev/null && echo lein || { if [ ! -f .lein.sh ]; then curl -o .lein.sh https://raw.githubusercontent.com/technomancy/leiningen/stable/bin/lein; chmod +x .lein.sh ; fi; echo './.lein.sh' ; })

VERSION=0.1.0

SOURCE=$(wildcard src/*/*/*.clj) $(wildcard src/*/*/*.java)
JAR_TARGET=target/dyna-$(VERSION)-SNAPSHOT-standalone.jar
TARGET=dyna-standalone-$(VERSION)

.PHONY: clean all repl test

all: $(TARGET)

clean:
	rm -rf target/ $(TARGET)

repl: clean
	$(LEIN) repl

test:
	$(LEIN) test



# if we are building the uberjar, then run the clean first as some of the macroexpands might have changed
# and we don't want to have mixed the old and new versions of this
$(JAR_TARGET): $(SOURCE)
	rm -rf target/
	$(LEIN) uberjar



$(TARGET): $(JAR_TARGET) standalone-header.sh
	cat standalone-header.sh $(JAR_TARGET) > $(TARGET)
	chmod +x $(TARGET)
