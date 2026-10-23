"""Exact cyclic occupancy enumeration; no geometric realizability claim."""
from math import comb
import json

def weak_compositions(total, length):
    if length == 1:
        yield (total,)
        return
    for first in range(total+1):
        for rest in weak_compositions(total-first,length-1):
            yield (first,)+rest

def canonical(values):
    reverse=values[::-1]
    return min([values[i:]+values[:i] for i in range(len(values))]
               +[reverse[i:]+reverse[:i] for i in range(len(values))])

def cover(core, ring):
    cases=[]
    for length in range(1,core+1):
        raw=list(weak_compositions(ring,length))
        if len(raw) != comb(ring+length-1,length-1):
            raise RuntimeError('incomplete composition enumeration')
        representatives=sorted({canonical(x) for x in raw})
        for x in raw:
            if sum(x) != ring or len(x) != length or canonical(x) not in representatives:
                raise RuntimeError('invalid orbit coverage')
        cases.extend(representatives)
    return cases

def main():
    for core,ring,expected in ((3,8,16),(4,7,33)):
        cases=cover(core,ring)
        if len(cases) != expected:
            raise RuntimeError('unexpected orbit count')
        print(json.dumps({'core':core,'ring':ring,'count':len(cases),'cases':cases}))

if __name__=='__main__':main()
