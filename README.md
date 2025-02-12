# Dyna v3

Dyna v3 is the latest implementation of the [Dyna](http://dyna.org) programming
language.

# Trying it out
```
./dyna
```
This will compile the dyna runtime and start the dyna REPL.

Alternatively, an online demo can be found at https://dyna.org/dyna3-demo/

# Building
```
make
```

A recent version of java is required.  Running `make` should automattically
download all dependencies.  The dyna runtime will be compiled into
`./dyna-standalone-*.run`.

## Running dyna
```
make
./dyna-standalone-*.run
```

## Running tests
```
rlwrap -a lein test
```
