package dyna;

import clojure.lang.AFn;
import clojure.lang.IFn;
import clojure.lang.Var;
import clojure.lang.RT;

public final class SimplifyRewriteCollection extends AFn {

    private static class RewriteList {
        final IFn rewrite_func;
        final RewriteList next;
        private RewriteList(IFn rewrite_func, RewriteList next) {
            this.rewrite_func = rewrite_func;
            this.next = next;
        }
    }

    private RewriteList head = null;

    public Rexpr doRewrite(Rexpr r, IFn simplify_method) {
        RewriteList h = head;
        if(h == null)
            return makeNewRewrites(r, simplify_method);
        while(h != null) {
            Rexpr result = (Rexpr)h.rewrite_func.invoke(r, simplify_method);
            if(result != null && r != result && !r.equals(result)) {
                return result;
            }
            h = h.next;
        }
        return r;
    }

    public Rexpr makeNewRewrites(Rexpr r, IFn simplify_method) {
        return (Rexpr)jit_create_rewrite.invoke(r);
    }

    public synchronized void addRewrite(IFn rewrite_func) {
        head = new RewriteList(rewrite_func, head);
    }

    @Override
    public Rexpr invoke(Object r, Object simplify_method) {
        return doRewrite((Rexpr)r, (IFn)simplify_method);
    }

    private static Var jit_create_rewrite = RT.var("dyna.rexpr", "simplify-jit-create-rewrite");
}
