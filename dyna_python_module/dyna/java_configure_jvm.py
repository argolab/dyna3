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

    _jpype.JClass('dyna.DynaMain').backgroundInit()

_configure_jvm()
