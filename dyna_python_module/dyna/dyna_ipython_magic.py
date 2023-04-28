import html
from IPython.core.magic import register_cell_magic, needs_local_scope

from dyna import Dyna as _Dyna_runtime

class _HTML_results(list):

    def __init__(self, a):
        super().__init__(a)

    def _repr_html_(self):
        r = ['<table>']
        for x in self:
            r.append('<tr><td>')
            r.append(html.escape(repr(x)))
            r.append('</td></tr>')
        r.append('</table>')
        return ''.join(r)


class _Error:

    def __init__(self, msg):
        self._message = msg

    def __str__(self):
        return f'ERROR: {self._message}'

    def __repr__(self):
        return f'ERROR: {self._message}'

    def _repr_html_(self):
        return '<span style="color:red">'+self._message.replace('\n', '<br>')+'</span>'


@register_cell_magic
@needs_local_scope
def dyna(line, cell, local_ns):
    dyna_runtimes = set(x for x in local_ns.values() if isinstance(x, _Dyna_runtime))
    if len(dyna_runtimes) == 0:
        return _Error('first create a dyna runtime using something like `from dyna import Dyna; dyna = Dyna()`')
    elif len(dyna_runtimes) > 1:
        return _Error('More than 1 dyna runtime in scope, unable to automattically figure out which one to use')

    # wonder if should make `#` work as a comment for the ipython cells.  This
    # is not something that is currently in dyna, but it might make the code
    # look more python like when writing it in a notebook.  The problem with
    # that would be that it would be inconsistent in different places....

    r = next(iter(dyna_runtimes))
    result = r.query(cell or line)  # can this throw an exception?

    if len(result) == 0:
        return None
    elif len(result) == 1:
        return result[0]
    else:
        return _HTML_results(result)
