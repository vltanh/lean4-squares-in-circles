#!/usr/bin/env python3
"""Exact regressions; the covering proof is in GATE3B_M5_TWO_FOLDED_TYPES.md."""
from fractions import Fraction as F
from itertools import combinations
from random import Random

WORDS = ('LHLHLHLL','LHLHLLHL','LHLLHHLL','LHLLHLHL',
         'LLHHLHLL','LLHHLLHL','LLHLHHLL','LLHLHLHL')
REPS = ('LHLHLHLL','LHLLHHLL')
ANCHORS = (0,6,0,4,4,6,2,2)


def complement(w):
    return ''.join('H' if c=='L' else 'L' for c in w)


def reanchor(w,k):
    new=w[k:]+complement(w[:k])
    return complement(new) if w[k]=='H' else new


def quarter_rep(x,y):
    for _ in range(4):
        if x>0 and y>=0:
            return x,y
        x,y=-y,x
    raise ValueError('Zero direction')


def relative(a,b):
    return quarter_rep(a[0]*b[0]+a[1]*b[1],a[0]*b[1]-a[1]*b[0])


def count(a,dirs):
    return sum(x>=y for x,y in (relative(a,b) for b in dirs))


def folded_word(dirs,anchor):
    entries=[]
    for j,b in enumerate(dirs):
        x,y=relative(dirs[anchor],b)
        label='L' if x>=y else 'H'
        if label=='H':
            x,y=x+y,y-x
        entries.append((F(y,x),label,j))
    entries.sort()
    return ''.join(e[1] for e in entries),entries


def generic(dirs):
    return all(x!=y and y!=0 for i,j in combinations(range(8),2)
               for x,y in [relative(dirs[i],dirs[j])])


def main():
    generated=[]
    for hpos in combinations(range(8),3):
        w=''.join('H' if j in hpos else 'L' for j in range(8))
        heights=[5]
        for ch in w:
            heights.append(heights[-1]+(1 if ch=='H' else -1))
        if min(heights)>=3 and max(heights)<=5:
            generated.append(w)
    assert tuple(generated)==WORDS
    for w,k in zip(WORDS,ANCHORS):
        assert reanchor(w,k) in REPS
    rng=Random(20261013)
    tested=0
    observed=set()
    for _ in range(4000):
        dirs=[(rng.randrange(1,100),rng.randrange(0,100)) for _ in range(8)]
        if not generic(dirs):
            continue
        counts=[count(a,dirs) for a in dirs]
        if max(counts)!=5:
            continue
        for a,ct in enumerate(counts):
            if ct!=5:
                continue
            w,ent=folded_word(dirs,a)
            assert w in WORDS
            idx=ANCHORS[WORDS.index(w)]
            newanchor=ent[idx][2]
            assert count(dirs[newanchor],dirs)==5
            nw,_=folded_word(dirs,newanchor)
            assert nw==reanchor(w,idx)
            assert nw in REPS
            tested+=1
            observed.add(w)
    assert observed==set(WORDS)
    # A boundary instance with four exact antipodal orientation pairs.
    tied=[(1,0),(5,1),(5,2),(5,3),(1,1),(4,6),(3,7),(2,8)]
    assert max(count(a,tied) for a in tied)==5
    print('Eight bounded-walk words and their two re-anchoring orbits: PASS')
    print(f'{tested} exact generic maximizing-anchor regressions; all eight words observed: PASS')
    print('Closed-window antipodal-direction boundary control: PASS')
    print('The finite tests do not prove M5 packing infeasibility or a sharp radius bound.')


if __name__=='__main__':
    main()
