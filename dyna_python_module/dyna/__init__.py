"""
The Dyna programming language Python API.
"""

import io as _io
import inspect

# this will configure the JVM, and start loading the dyna runtime in the background concurrently
from . import java_configure_jvm


class Dyna:

    def __init__(self):
        self.__system_v = None

    @property
    def __system(self):
        v = self.__system_v
        if v is not None:
            return v
        # this will reference the python class which wrap the java class.  This will block until the dyna runtime is loaded
        from .java_wrapper import DynaInstance
        v = DynaInstance()
        self.__system_v = v
        return v

    def define_function(self, name=None, arity=None):
        """
        A decorator which allows for python functions to be callable from dyna
        """
        used = False
        def f(func):
            nonlocal name, arity, used
            assert used is False, "The function names & arity must be unique"
            used = True
            if name is None:
                name = func.__name__
            if arity is None:
                arity = len(inspect.getargspec(func).args)
            self.__system.define_function(name, arity, func)
            return func
        return f

    def execute(self, code: str, *value_args):
        """
        Run a string of code with additional arguments corresponding to values represented as $0,$1,...$n in the code
        Returns Nothing

        Any queries made under execute will be printed out only, nothing will be returned
        """
        self.__system.run_string(code, *value_args)

    def query(self, code, *value_args):
        """
        Return a string of code with additional arguments corresponding to values represented as $0,$1,....$n in the code
        Returns an array of queries made in the program.

        Queries will be returned and not printed out
        """
        return self.__system.run_query(code, *value_args)

    def run(self, code, *value_args):
        """
        Run a string or a file of code
        """
        if isinstance(code, (_io.TextIOBase, _io.BufferedIOBase, _io.RawIOBase, _io.IOBase)) and not value_args:
            return self.run_file(code)
        else:
            return self.execute(code, *value_args)

    def run_file(self, file):
        self.__system.run_file(file)


class _DynaTermMetaClass(type):

    def __instancecheck__(cls, obj):
        from .java_wrapper import DynaTerm
        return isinstance(obj, DynaTerm)

class DynaTerm(metaclass=_DynaTermMetaClass):

    def __new__(cls, *args, **kwargs):
        from .java_wrapper import DynaTerm
        return DynaTerm(*args, **kwargs)


__all__ = [
    'Dyna',
    'DynaTerm',
]


try:
    from . import dyna_ipython_magic
except (ImportError,NameError):
    # if ipython is not being used, then the import of this will fail
    pass
