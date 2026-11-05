"""Skip zero/positive finite dual entries before the unchanged scalar rounding."""
def install(module):
    import numpy as np
    old=module.terms
    if getattr(old,'sparse_dual_fast_path',False):return old
    def terms(dual):
        # All actual HiGHS dual vectors have this shape/type. Preserve the
        # original behavior, including errors, for every other input.
        if not isinstance(dual,np.ndarray)or dual.ndim!=1 or dual.dtype!=np.dtype('float64')or not np.isfinite(dual).all():
            return old(dual)
        if np.any(np.abs(dual)>np.finfo('float64').max/module.SCALE):
            return old(dual)
        answer=[]
        for index in np.flatnonzero(dual<0):
            value=int(round(-float(dual[index])*module.SCALE))
            if value>0:answer.append([int(index),value])
        return answer
    terms.sparse_dual_fast_path=True
    module.terms=terms
    return old
