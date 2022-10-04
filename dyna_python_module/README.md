# Python Module for Dyna

This is a Python wrapper for interacting with the Dyna runtime (which is written
in Clojure).  This library exposes the most commonly used functionallity and
should be sufficient for most users of Dyna.  Additional access to the Dyna
internals can be access by writing raw Clojure code.

## Installing

Either Download the prebuilt dyna binary or build the binary using the following steps:
```bash
git clone https://github.com/argolab/dyna3.git
cd dyna3
make
ls ./dyna-standalone-0.1.0  # the resulting prebuilt binary
```

To install Dyna into Python do:
```bash
source ~/path/to/python/virtual-env/bin/activate  # OPTIONAL activate your python virtual environment

./dyna-standalone-0.1.0 install-python   # Install Dyna into the current python environment
```

## Usage

```python
from dyna import Dyna

inst = Dyna()  # make a new Dyna runtime

inst.run('''
print "hello world from Dyna".
''')
```

### Defining Rules

Any rule can be defined by passing a string of Dyna code to the `Dyna.run()`
method.  Statements in Dyna in end with a period.  For example:

```python
inst.run('''
foo = 123.  % define the term foo to take the value 123

list_length([]) = 0.
list_length([X|Y]) = 1 + list_length(Y).
''')

inst.run_file('path_to_file.dyna')
```

### Queries

Dyna programs can be queried (much like a database) and have a result returned.
This is done by using the `Dyna.query()` method.  Queries end with a question
mark.  Multiple queries can be done at the same time and all of their results
will be returned in a list.  For example:

```python
result = inst.query('''
1 + 2?
list_length([1,2,3,4])?
''')

assert result[0] == 1 + 2
assert result[1] == len([1,2,3,4])
```

### Parameter Arguments

Both `Dyna.run()` and `Dyna.query()` can take "query parameters" which are
subsuited into the parsed code.  This is akin to writing a parameterized
statement when interacting with a SQL database.  The values are represented
using `$0`, `$1`, . . . `$n` where the number corresponds with the positional
argument.  For example:

```python
result = inst.query('''
1 + $0 ?
str("hello ", $1) ?
''', 3, "world")

assert result[0] == 4
assert result[1] == "hello world"
```

The values passed as parameters can either be primitive types which
can be interpreted by dyna (numbers, strings, dyna terms) or opaque types
(e.g. a pytorch tensor) which can be passed around without Dyna directly
interacting with the value.

```python
class OpaqueType: pass
opaque = OpaqueType()
inst.run('''
ref = $0.  % save a reference to the opaque value into the dyna database
''', opaque)

result = inst.query('''
ref ?  % get the reference back from dyna
''')

assert result[0] is opaque
```


### External Functions

The Python program can also export functions to the Dyna runtime.  These
functions can perform computation using python methods as well as interact with
any value which is opaque to Dyna.  These methods are defined using the
`Dyna.define_function()` decorator on a function.  For example:

```python
@inst.define_function()
def my_func(a, b):
    return a + 7*b

@inst.define_function('function_name')
def x(y): return y

inst.run('''
assert my_func(3, 6) == 3 + 6*7.
assert function_name(3) == 3.
''')
```

Note: Any function exposed to Dyna should be _functional_.  A function might get
called multiple times on the same arguments, or the order in which the function
is called may differ from what has been written in the program.









This will wrap the Dyna runtime and make calls into the runtime from Python.

Features that we should support:
* Loading a string of dyna code
* Loading a dyna file
* making queries against the dyna program and getting back a primitive value (float,int,string)
* Some structured Term representation for fully ground terms.  E.g. `&foo(1,2,3)` should get returned somehow
* Lists should automattically get converted into Python lists


* Passing opaque python values through the dyna runtime
* calling Python functions from dyna.  Though there will be no guarantee that
  those functions will get called once, or if they are not functional, then that
  could be an issue
