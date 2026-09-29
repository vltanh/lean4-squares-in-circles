"""Branch-and-bound from the supplied normalization certificate package.

A predicate returns a nonempty reason only when the claim is proved on the
whole input box (or its feasible portion). Closed dyadic children cover the
parent exactly. Acceptance requires that unresolved is empty. A depth/node
limit or an unsplittable floating-point interval never counts as success.
"""
import math
import time
from collections import Counter


def bnb(root, evaluate, weights, max_depth=64, max_boxes=20_000_000,
        record=None, verbose=True, name=''):
    if len(root) != len(weights) or not root:
        raise ValueError('root/weight dimensions must agree and be nonempty')
    if any(not math.isfinite(a) or not math.isfinite(b) or a>b for a,b in root):
        raise ValueError('invalid root box')
    if any(not math.isfinite(w) or w<=0 for w in weights):
        raise ValueError('positive finite search weights required')
    if max_depth<0 or max_boxes<1:
        raise ValueError('invalid traversal limit')
    t0 = time.time()
    stack = [(tuple(root),0)]
    stats = Counter()
    unresolved = []
    nboxes = 0
    maxd = 0
    while stack:
        box,d = stack.pop()
        nboxes += 1
        reason = evaluate(box)
        if reason is not None:
            if not isinstance(reason,str) or not reason:
                raise TypeError('a closure reason must be a nonempty string')
            stats[reason] += 1
            if record is not None: record(box,reason)
            continue
        if d>=max_depth or nboxes>=max_boxes:
            unresolved.append(box)
            continue
        i = max(range(len(box)),key=lambda k:(box[k][1]-box[k][0])*weights[k])
        lo,hi = box[i]
        mid = (lo+hi)/2
        if not lo<mid<hi:
            unresolved.append(box)
            continue
        b1,b2 = list(box),list(box)
        b1[i],b2[i] = (lo,mid),(mid,hi)
        maxd = max(maxd,d+1)
        stack.extend(((tuple(b2),d+1),(tuple(b1),d+1)))
    if verbose:
        print(f'[{name}] boxes={nboxes} leaves={sum(stats.values())} '
              f'unresolved={len(unresolved)} maxdepth={maxd} time={time.time()-t0:.1f}s')
        for k,v in sorted(stats.items(),key=lambda kv:-kv[1]):
            print(f'    {k:28s} {v}')
    return stats,unresolved,nboxes
