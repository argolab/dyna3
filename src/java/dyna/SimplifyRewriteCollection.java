package dyna;

import clojure.lang.AFn;
import clojure.lang.IFn;

public final class SimplifyRewriteCollection extends AFn {

    private static class RewriteList {
        final IFn rewrite_func;
        final RewriteList next;
    }

    RewriteList head = null;

    public Rexpr doRewrite(Rexpr r, IFn simplify_method) {
        RewriteList h = head;
        if(h == null)
            return makeNewRewrites(r, simplify_method);
        while(h != null) {
            Rexpr result = h.rewrite_func.invoke(r, simplify_method);
            if(r != result && !r.equals(result)) {
                return result;
            }
            h = h.next;
        }
        return r;
    }

    public Rexpr makeNewRewrites(Rexpr r, IFn simplify_method) {

    }

    @Override
    Rexpr invoke(Rexpr r, IFn simplify_method) {
        return doRewrite(r, simplify_method);
    }
}
