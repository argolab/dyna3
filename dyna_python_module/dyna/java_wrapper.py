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
    _jpype.startJVM(None, *f'-Xmx{memory} -Dclojure.compiler.direct-linking=true -Ddyna.print_rewrites_performed=false -Ddyna.debug=false -Ddyna.trace_rexpr_construction=false -Ddyna.debug_repl=false'.split())

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

# @_jpype.JImplementationFor('dyna.DynaTerm')
# class DynaTermJavaClass:
#     def __len__(self):
#         return _interface.get_term_arity(self)
#     @property
#     def name(self):
#         return _interface.get_term_name(self)
#     # def __getitem__(self, i: int):
#     #     assert isinstance(i, int)
#     #     return cast_from_dyna(_interface.get_term_argument(self, i))
#     def __repr__(self):
#         return str(self)

class DynaTerm:
    __slots__ = ('_system', '_term')
    def __init__(self, name, *args):
        if name is not None:
            # make term with no reference instance
            self._system = DynaInstance
            args = _jpype.JObject[:](args)
            self._term = _term_class(name, args)

    @property
    def name(self):
        return str(_interface.get_term_name(self._term))

    def __str__(self):
        return str(self._term)
    def __repr__(self):
        return str(self)

    def __len__(self):
        return _interface.get_term_arity(self._term)

    def __getitem__(self, i: int):
        val = _interface.get_term_argument(self._term, i)
        return DynaInstance.cast_from_dyna(self._system, val)


def _cast_term_from_dyna(system, term):
    t = DynaTerm(None)
    t._system = system
    t._term = term
    return t

__all__.append('DynaTerm')

class Dynabase:
    __slots__ = ('_system', '_dynabase')
    def __init__(self, system, dynabase):
        self._system = system
        self._dynabase = dynabase

    def __getattr__(self, name):
        def func(*args):
            query_str = '$0.'+name+'(' + ','.join([f'${i+1}' for i in range(len(args))]) +') ?'
            q = self._system.run_query(
                query_str, self._dynabase, *args)
            if q:
                return q[0]
        func.__name__ = name
        return func

    def __str__(self):
        return f'Dynabase@{hash(self._dynabase)}'  # the internal representation of these is gross
    def __repr__(self):
        return str(self)

__all__.append('Dynabase')

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
    def __init__(self, system, wrapped):
        self.__system = system
        self.__wrapped = wrapped
    @_jpype.JOverride
    def call(self, args):
        return self.__system.cast_to_dyna(self.__wrapped(*[self.__system.cast_from_dyna(x) for x in args]))


def _wrap(f):
    return lambda _,b: f(b)
_cast_map = {
    _jpype.JClass('java.lang.Integer'): _wrap(int),
    _jpype.JClass('java.lang.Long'): _wrap(int),
    _jpype.JClass('java.lang.Short'): _wrap(int),
    _jpype.JClass('java.lang.Byte'): _wrap(int),
    _jpype.JClass('java.lang.Float'): _wrap(float),
    _jpype.JClass('java.lang.Double'): _wrap(float),
    _jpype.JClass('java.lang.Boolean'): _wrap(bool),
    _jpype.JClass('java.lang.Character'): _wrap(str),
    _jpype.JClass('java.lang.String'): _wrap(str),

    _jpype.JClass('dyna.Dynabase'): Dynabase,
    _jpype.JClass('dyna.DynaTerm'): _cast_term_from_dyna,
}


class DynaInstance:
    def __init__(self):
        self.__system = _interface.create_dyna_system()

    def run_string(self, x, *query_args):
        if not query_args:
            _interface.run_string(self.__system, x)
        else:
            args = _jpype.JObject[:]([self.cast_to_dyna(v) for v in query_args])
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
            return [self.cast_from_dyna(v) for v in res]
        else:
            args = _jpype.JObject[:]([self.cast_to_dyna(v) for v in query_args])
            res = _interface.run_query(self.__system, x, args)
            return [self.cast_from_dyna(v) for v in res]

    def define_function(self, name, arity, function):
        func = _ExternalFunctionWrapper(self, function)
        _interface.define_external_function(self.__system, name, arity, func)

    def cast_to_dyna(self, x):
        if isinstance(x, (str, int, float, bool, _term_class, _jpype.JObject)):
            return x
        elif isinstance(x, (list, tuple)):
            a = _jpype.JObject[:]([DynaInstance.cast_to_dyna(self, v) for v in x])
            v = _term_class.make_list(a)
            return v
        elif isinstance(x, Dynabase):
            assert x._system is self
            return x._dynabase
        elif isinstance(x, DynaTerm):
            assert x._system is self or x._system is DynaInstance
            return x._term
        else:
            return _OpaqueValue(x)

    def cast_from_dyna(self, x):
        if isinstance(x, _term_class):
            l = x.list_to_array()
            if l is not None:
                return [DynaInstance.cast_from_dyna(self, v) for v in l]
            return x
        elif isinstance(x, _OpaqueValue):
            return x._wrapped
        t = type(x)
        if t in _cast_map:
            return _cast_map[t](self, x)
        return x


__all__.append('DynaInstance')
