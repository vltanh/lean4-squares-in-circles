"""Bounded caches for pure exact coupled-energy generator functions only."""
from functools import lru_cache
from copy import deepcopy
from fractions import Fraction as F

def install(module):
    if getattr(module.rows,'exact_energy_cached',False):return
    original_energy=module.energy
    module.energy=lru_cache(maxsize=8192)(original_energy)
    original_projection=module.projected_interval
    @lru_cache(maxsize=4096)
    def projection(ds,direction,diagonal):
        return original_projection(ds,direction,diagonal)
    def projected_interval(ds,direction,diagonal=None):
        return projection(tuple(tuple(v)for v in ds),tuple(direction),None if diagonal is None else tuple(tuple(v)for v in diagonal))
    module.projected_interval=projected_interval
    original_rows=module.rows
    @lru_cache(maxsize=2)
    def cached_rows(differences,diagonal,directions):
        rows,guards=original_rows(dict(differences),dict(diagonal),directions)
        return tuple(rows),guards
    def rows(differences,diagonal=None,directions=((F(1),F(0)),(F(1),F(1)))):
        ds=tuple((p,tuple(tuple(v)for v in box))for p,box in sorted(differences.items()))
        dg=tuple((p,tuple(tuple(v)for v in box))for p,box in sorted((diagonal or {}).items()))
        answer,guards=cached_rows(ds,dg,tuple(tuple(v)for v in directions))
        return list(answer),deepcopy(guards)
    rows.exact_energy_cached=True
    module.rows=rows
