"""
The Dyna programming language Python API.
"""

import inspect

class Dyna:

    def __init__(self):
        self.__system = None  # some pointer to dyna instance that we are running

    def define_function(self, function_name=None):
        """
        A decorator which allows for python functions to be callable from dyna
        """
        def f(func):
            pass
        return f

    def run(self, code):
        """
        If there is some response, then this is going to have to get the response back.  If it is something more complex than a value
        """

        pass
