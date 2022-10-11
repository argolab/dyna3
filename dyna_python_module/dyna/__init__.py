"""
The Dyna programming language Python API.
"""

import inspect
from .java_wrapper import DynaInstance, DynaTerm


class Dyna:

    def __init__(self):
        self.__system = DynaInstance()

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
        Run a string of code
        """
        return self.execute(code, *value_args)

    def run_file(self, file):
        self.__system.run_file(file)

__all__ = [
    'Dyna',
    'DynaTerm',
]
