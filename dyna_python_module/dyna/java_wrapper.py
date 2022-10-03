import jpype as _jpype
import os as _os
import io as _io

__all__ = []

def _configure_jvm():
    import importlib.resources
    jar = importlib.resources.path('dyna', 'dyna.jar')
    if not _os.path.exists(jar):
        d = _os.path.join(_os.path.dirname(__file__), '../..')
        jar = _os.path.join(d, 'target/dyna-0.1.0-SNAPSHOT-standalone.jar')


    if not _os.path.exists(jar):
        import ipdb; ipdb.set_trace()
        raise ImportError('Unable to find the dyna implmentation "dyna.jar"')

    # add the dyna jar to the classpath
    _jpype.addClassPath(jar)

    memory = _os.environ.get('DYNA_MEMORY', '2g')  # the amount of memory that the backend should allocate

    # start the JVM and pass configuration flags
    _jpype.startJVM(None, *f'-Xmx{memory} -Dclojure.compiler.direct-linking=true -Ddyna.print_rewrites_performed=false -Ddyna.debug=false -Ddyna.trace_rexpr_construction=false'.split())

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

# probably not going to construct an R-expr from python, so there is probably no reason to do this...
for _name in {'unify', 'conjunct', 'disjunct', 'multiplicity', 'proj',
              'aggregator', 'if', 'add', 'times', 'min', 'max', 'pow', 'exp',
              'log', 'lessthan', 'lessthan-eq', 'greaterthan', 'greaterthan-eq',
              'equals', 'not-equals', 'land', 'lor', 'not', 'sin', 'cos', 'tan',
              'sinh', 'cosh', 'tanh', 'range', 'random'}:
    globals()[f'make_{_name.replace("-", "_")}'] = _construct_make_method(_name)
    __all__.append(f'make_{_name.replace("-", "_")}')

@_jpype.JImplementationFor('dyna.DynaTerm')
class DynaTerm:
    def __len__(self):
        return _interface.get_term_arity(self)
    @property
    def name(self):
        return _interface.get_term_name(self)
    def __getitem__(self, i: int):
        assert isinstance(i, int)
        return _interface.get_term_argument(self, i)
    def __repr__(self):
        return str(self)

def term(name, *args):
    args = _jpype.JObject[:](args)
    return _term_class(name, args)

__all__.append('term')

@_jpype.JImplements('dyna.ExternalFunction')
class _ExternalFunctionWrapper:
    def __init__(self, wrapped):
        self.__wrapped = wrapped
    @_jpype.JOverride
    def call(self, args):
        return self.__wrapped(*list(args))

class DynaInstance:
    def __init__(self):
        self.__system = _interface.create_dyna_system()

    def run_string(self, x, *query_args):
        if not query_args:
            _interface.run_string(self.__system, x)
        else:
            args = _jpype.JObject[:](query_args)
            _interface.run_string(self.__system, x, args)

    def run_file(self, f):
        if isinstance(f, str):
            a = _os.path.abspath(f)
            assert _os.path.exists(a), "File not found"
            _interface.run_file(self.__system, 'file://' + a)
        elif isinstance(f, (_io.TextIOBase, _io.BufferedIOBase, _io.RawIOBase, _io.IOBase)):
            a = _os.path.abspath(f.name)
            _interface.run_file(self.__system, 'file://' + a)
        else:
            raise TypeError(f"Dyna does not know how to run type {type(f)}")

    def run_query(self, x, *query_args):
        if not query_args:
            return _interface.run_query(self.__system, x)
        else:
            args = _jpype.JObject[:](query_args)
            return _interface.run_query(self.__system, x, args)

    def define_function(self, name, arity, function):
        func = _ExternalFunctionWrapper(function)
        _interface.define_external_function(self.__system, name, arity, func)

__all__.append('DynaInstance')
