# Python Module for Dyna

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
