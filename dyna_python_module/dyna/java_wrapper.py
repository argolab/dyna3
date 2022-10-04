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
        #import ipdb; ipdb.set_trace()
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
        return cast_from_dyna(_interface.get_term_argument(self, i))
    def __repr__(self):
        return str(self)

def term(name, *args):
    args = _jpype.JObject[:](args)
    return _term_class(name, args)

__all__.append('term')

@_jpype.JImplements('dyna.OpaqueValue')
class _OpaqueValue:
    def __init__(self, wrapped):
        self._wrapped = wrapped
    def __eq__(self, other):
        if isinstance(other, _OpaqueValue):
            return self._wrapped == other._wrapped
        return False
    def __hash__(self):
        return hash(self._wrapped)

@_jpype.JImplements('dyna.ExternalFunction')
class _ExternalFunctionWrapper:
    def __init__(self, wrapped):
        self.__wrapped = wrapped
    @_jpype.JOverride
    def call(self, args):
        return cast_to_dyna(self.__wrapped(*[cast_from_dyna(x) for x in args]))

def cast_to_dyna(x):
    if isinstance(x, (str, int, float, bool, _term_class, _jpype.JObject)):
        return x
    elif isinstance(x, (list, tuple)):
        a = _jpype.JObject[:]([cast_to_dyna(v) for v in x])
        v = _term_class.make_list(a)
        return v
    else:
        return _OpaqueValue(x)

_cast_map = {
    _jpype.JClass('java.lang.Integer'): int,
    _jpype.JClass('java.lang.Long'): int,
    _jpype.JClass('java.lang.Short'): int,
    _jpype.JClass('java.lang.Byte'): int,
    _jpype.JClass('java.lang.Float'): float,
    _jpype.JClass('java.lang.Double'): float,
    _jpype.JClass('java.lang.Boolean'): bool,
    _jpype.JClass('java.lang.Character'): str,
    _jpype.JClass('java.lang.String'): str,
}

def cast_from_dyna(x):
    if isinstance(x, _term_class):
        l = x.list_to_array()
        if l is not None:
            return [cast_from_dyna(v) for v in l]
        return x
    elif isinstance(x, _OpaqueValue):
        return x._wrapped
    t = type(x)
    if t in _cast_map:
        return _cast_map[t](x)
    return x

class DynaInstance:
    def __init__(self):
        self.__system = _interface.create_dyna_system()

    def run_string(self, x, *query_args):
        if not query_args:
            _interface.run_string(self.__system, x)
        else:
            args = _jpype.JObject[:]([cast_to_dyna(v) for v in query_args])
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
            res = _interface.run_query(self.__system, x)
            return [cast_from_dyna(v) for v in res]
        else:
            args = _jpype.JObject[:]([cast_to_dyna(v) for v in query_args])
            res = _interface.run_query(self.__system, x, args)
            return [cast_from_dyna(v) for v in res]

    def define_function(self, name, arity, function):
        func = _ExternalFunctionWrapper(function)
        _interface.define_external_function(self.__system, name, arity, func)

__all__.append('DynaInstance')
