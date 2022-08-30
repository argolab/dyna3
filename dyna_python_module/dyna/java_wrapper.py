import jpype as _jpype
import os as _os
import io as _io

__all__ = []

def _configure_jvm():
    import os

    d = os.path.join(os.path.dirname(__file__), '..')
    # build = os.popen(f'cd {d} && make all')
    # res = build.read()
    # if build.close() is not None:
    #     print("compile has failed")
    #     print(res)
    #     raise RuntimeError('compiling the backend has failed')

    # this is the current classes which represent which
    _jpype.addClassPath(os.path.join(d, 'target/dyna-0.1.0-SNAPSHOT-standalone.jar'))

    # the jar is compiled into the binary, so that might be something that it should include.  If there is something

    memory = os.environ.get('DYNA_MEMORY', '2g')  # the amount of memory that the backend should allocate

    # this should pass other property flags which configure the dyna runtime
    _jpype.startJVM(None, '-Xmx'+memory)

_configure_jvm()

_jpype.JClass('java.lang.Object').__repr__ = lambda self: f'Backend<{str(self)}>'

_interface = _jpype.JClass('dyna.DynaInterface').getInstance()

_term_class = _jpype.JClass('dyna.DynaTerm')


def _construct_make_method(name):
    def f(*args):
        return _interface.make_rexpr(name, args)
    f.__name__ = f'make_{name.replace("-", "_")}'
    return f

make_variable = _interface.make_variable
make_constant = _interface.make_constant

__all__ += ['make_variable', 'make_constant']

for _name in {'unify', 'conjunct', 'disjunct', 'multiplicity', 'proj',
              'aggregator', 'if', 'add', 'times', 'min', 'max', 'pow', 'exp',
              'log', 'lessthan', 'lessthan-eq', 'greaterthan', 'greaterthan-eq',
              'equals', 'not-equals', 'land', 'lor', 'not', 'sin', 'cos', 'tan',
              'sinh', 'cosh', 'tanh', 'range', 'random'}:
    globals()[f'make_{_name.replace("-", "_")}'] = _construct_make_method(_name)
    __all__.append(f'make_{_name.replace("-", "_")}')

def run(x):
    if isinstance(x, str):
        if _os.path.exists(x):
            return _interface.run_file(x)
        else:
            return _interface.run_string(x)
    elif isinstance(x, (_io.TextIOBase, _io.BufferedIOBase, _io.RawIOBase, _io.IOBase)):
        return _interface.run_file(x.name)  # this is attempting to get the path to the file, but this might not work...
    else:
        # this should check if this is a file, and then get the file name or read the contents of the file
        assert False

__all__.append('run')


def _term_len(self):
    return _interface.get_term_arity(self)

def _term_argument(self, i):
    return _interface.get_term_argument(self, i)

def _term_name(self):
    return _interface.get_term_name(self)

_term_class.__len__ = _term_len
_term_class.__getitem__ = _term_argument
#_term_class.term_name = property(_term_name)  # there should be some way to set a method on these classes???
_term_class.__repr__ = lambda self: str(self)
