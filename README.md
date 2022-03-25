# Dyna v3

Dyna v3 is the latest implementation of the [Dyna](http://dyna.org) programming
language.

# Building
```
make
```

A recent version of java is required.  Running `make` should automattically
download all dependencies.  The dyna runtime will be compiled into
`./dyna-standalone-0.1.0`.

## Running dyna
```
make
./dyna-standalone-0.1.0
```

## Running tests
```
rlwrap -a lein test
```
