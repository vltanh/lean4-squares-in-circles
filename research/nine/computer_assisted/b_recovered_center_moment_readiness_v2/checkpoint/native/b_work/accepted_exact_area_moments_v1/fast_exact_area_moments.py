"""Exact memoized assembly of the unchanged square-area moment rows.

Only numerical discovery installs this optimization. The independent checker
continues to decode the original literal rows. No rows or predicates change.
"""
from fractions import Fraction as F
from itertools import combinations
from functools import lru_cache


def install(module):
    original=module.generate_linear
    if getattr(original,'exact_moment_optimized',False):return original
    zero=F(0);pair_order=tuple(combinations(range(9),2))
    @lru_cache(maxsize=4)
    def build(frozen,counts,matrices):
        diffs=dict(frozen);answer=[]
        for k in counts:
            for matrix in matrices:
                lower=module.lower_bound(k,matrix)
                if lower<=0:continue
                # This per-matrix cache is shared across every subset size.
                terms=pair_terms(frozen,matrix)
                for selected in combinations(range(9),k):
                    co=[zero]*18;rhs=-lower
                    for i,j in combinations(selected,2):
                        ax,ay,c=terms[i,j]
                        co[2*i]+=ax;co[2*j]-=ax
                        co[2*i+1]+=ay;co[2*j+1]-=ay
                        rhs+=c
                    answer.append((tuple((v,c)for v,c in enumerate(co)if c),rhs,
                                   module.name(selected,matrix,'square_area_moment_secant')))
        return tuple(answer)
    @lru_cache(maxsize=48)
    def pair_terms(frozen,matrix):
        answer={}
        for pair,box in frozen:
            ax=ay=constant=zero
            for p,q in matrix:
                lo=sum(min(v*l,v*u)for v,(l,u)in zip((p,q),box))
                hi=sum(max(v*l,v*u)for v,(l,u)in zip((p,q),box))
                ax+=(lo+hi)*p;ay+=(lo+hi)*q;constant-=lo*hi
            answer[pair]=(ax,ay,constant)
        return answer
    def generate(differences,counts=(5,6,7,8,9),matrices=None):
        frozen=tuple((pair,tuple(tuple(v)for v in differences[pair]))for pair in pair_order)
        matrices=module.axes_matrices()if matrices is None else matrices
        matrices=tuple(tuple(tuple(row)for row in matrix)for matrix in matrices)
        return list(build(frozen,tuple(counts),matrices))
    generate.exact_moment_optimized=True
    generate.original=original
    module.generate_linear=generate
    return original
