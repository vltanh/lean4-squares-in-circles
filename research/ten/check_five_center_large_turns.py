#!/usr/bin/env python3
"""Verify the complete printed large-turn fan certificate using exact rationals.

No floating arithmetic, numerical optimizer, or third-party library is used.
The companion manuscript proves why the checked inequalities imply the result.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd, factorial
from functools import lru_cache
from pathlib import Path
import json

SOURCE = Path(__file__).with_name("five_center_large_turns_certificate.json")
data = json.loads(SOURCE.read_text())
SCALE = 2  # Every box bound is an integer or half-integer degree.
assert data["scale"] == SCALE

def det3(m):
 a,b,c=m[0];d,e,f=m[1];g,h,i=m[2]
 return a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)
def det4(m):
 return sum((1 if j%2==0 else -1)*m[0][j]*det3([[m[r][c] for c in range(4) if c!=j] for r in range(1,4)]) for j in range(4))
def adj4(m):
 return tuple(tuple((1 if (i+j)%2==0 else -1)*det3([[m[r][c] for c in range(4) if c!=i] for r in range(4) if r!=j]) for j in range(4)) for i in range(4))

def constraints(lo,hi,minj):
 A=[];b=[];e=[tuple(int(i==j) for j in range(5)) for i in range(5)]
 def row(v,q):A.append(v);b.append(F(q))
 for i in range(5):row(e[i],hi[i]);row(tuple(-x for x in e[i]),-lo[i])
 for i in range(1,5):row(tuple(e[i][j]-e[0][j] for j in range(5)),0)
 for i in range(5):
  if i!=minj:row(tuple(e[minj][j]-e[i][j] for j in range(5)),0)
 for i in range(5):
  v=tuple(e[i][j]+e[(i+1)%5][j] for j in range(5));row(v,240);row(tuple(-x for x in v),-60)
 AA=tuple(tuple(v[j]-v[4] for j in range(4)) for v in A)
 bb=tuple(int((q-360*v[4])*SCALE) for q,v in zip(b,A))
 assert all((q-360*v[4])*SCALE==z for q,v,z in zip(b,A,bb))
 return AA,bb
bases={}
for minj in [1,2]:
 A,_=constraints([F(0)]*5,[F(180)]*5,minj);out=[]
 for ids in combinations(range(len(A)),4):
  m=[A[i] for i in ids];d=det4(m)
  if not d:continue
  adj=adj4(m)
  if d<0:d=-d;adj=tuple(tuple(-v for v in r) for r in adj)
  out.append((ids,d,adj))
 bases[minj]=out

@lru_cache(maxsize=None)
def vertices(lo,hi,minj):
 A,b=constraints(lo,hi,minj);out=set()
 for ids,d,adj in bases[minj]:
  bb=[b[i] for i in ids];nums=tuple(sum(row[j]*bb[j] for j in range(4)) for row in adj)
  if any(sum(row[j]*nums[j] for j in range(4))>q*d for row,q in zip(A,b)):continue
  gg=d
  for v in nums:gg=gcd(gg,abs(v))
  key=tuple(v//gg for v in nums)+(d//gg,);out.add(key)
 ans=[]
 for z in out:
  vals=tuple(F(v,z[4]*SCALE) for v in z[:4]);ans.append(vals+(360-sum(vals),))
 return tuple(sorted(ans))

def rank(rows):
 a=[list(map(F,r)) for r in rows];r=0
 for c in range(4):
  k=next((k for k in range(r,len(a)) if a[k][c]),None)
  if k is None:continue
  a[r],a[k]=a[k],a[r];q=a[r][c];a[r]=[x/q for x in a[r]]
  for k in range(r+1,len(a)):
   q=a[k][c]
   if q:a[k]=[x-q*y for x,y in zip(a[k],a[r])]
  r+=1
 return r

def atan_iv(q,N=24):
 total=sum(F((-1)**k,(2*k+1)*q**(2*k+1)) for k in range(N))
 rem=F(1,(2*N+1)*q**(2*N+1))
 return (total,total+rem) if N%2==0 else (total-rem,total)
a=atan_iv(5);b=atan_iv(239);PI=(16*a[0]-4*b[1],16*a[1]-4*b[0]);assert PI[0]>F(314159,100000) and PI[1]<F(314160,100000)
def add(a,b):return(a[0]+b[0],a[1]+b[1])
def neg(a):return(-a[1],-a[0])
def mul(a,b):
 q=[a[i]*b[j] for i in range(2) for j in range(2)];return(min(q),max(q))
def scale(q,a):return(q*a[0],q*a[1]) if q>=0 else(q*a[1],q*a[0])
def radians(deg):return scale(deg/F(180),PI)
@lru_cache(maxsize=None)
def trig(deg,cosine):
 x=radians(deg);assert x[0]>=0 and x[1]<=PI[1]
 out=(F(0),F(0));last=0
 for k in range(13):
  power=2*k if cosine else 2*k+1;last=power
  iv=(x[0]**power/F(factorial(power)),x[1]**power/F(factorial(power)))
  out=add(out,iv if k%2==0 else neg(iv))
 rem=x[1]**(last+1)/factorial(last+1)
 return(out[0]-rem,out[1]+rem)

def bound(v,lo,mid,lam,d):
 out=(F(0),F(0))
 for i,g in enumerate(v):
  p=lam[i-1];q=lam[i];A=min(p,q)/2;B=p*q/(2*d[i]);C=max(p,q)/2-(p*p+q*q)/(4*d[i])-d[i]+1
  term=add((C,C),scale(A,trig(g,False)))
  if lo[i]<90:term=add(term,scale(A+B,trig(g,True)))
  else:
   K=B-A
   if K<=0:term=add(term,scale(K,trig(g,True)))
   else:
    tangent=add(trig(mid[i],True),neg(mul(trig(mid[i],False),radians(g-mid[i]))))
    term=add(term,scale(K,tangent))
  out=add(out,term)
 return out[0]


def fractions(values):
    return tuple(map(F, values))


records = {r["id"]: r for r in data["cases"]}
assert len(records) == 78 and set(records) == set(range(1, 79))
assert F(data["pi_lower"]) == PI[0]
assert F(data["pi_upper"]) == PI[1]
uniform = F(data["uniform_lower"])
assert uniform == F(200007133, 50000000) and uniform > 4
vertex_count = 0

# The bounded polytope's vertices occur among intersections of four
# independent active constraints after eliminating the fifth angle.
for case_id, record in sorted(records.items()):
    lo, hi = fractions(record["lo"]), fractions(record["hi"])
    minj = record["minj"]
    assert minj in (1, 2)
    assert all(0 <= a <= b <= 180 for a, b in zip(lo, hi))
    assert all(b <= 90 or a >= 90 for a, b in zip(lo, hi))
    lam, d = fractions(record["lambda"]), fractions(record["d"])
    assert len(lam) == len(d) == 5 and min(lam) >= 0 and min(d) >= 1
    actual = vertices(lo, hi, minj)
    printed = tuple(fractions(v["angles"]) for v in record["vertices"])
    assert actual == printed and actual
    effective_lo = tuple(min(v[i] for v in actual) for i in range(5))
    effective_hi = tuple(max(v[i] for v in actual) for i in range(5))
    midpoint = tuple((a+b)/2 for a, b in zip(effective_lo, effective_hi))
    assert effective_lo == fractions(record["effective_lo"])
    assert effective_hi == fractions(record["effective_hi"])
    assert midpoint == fractions(record["tangent_mid"])
    lower = F(record["lower"])
    assert lower >= uniform
    for vertex, entry in zip(actual, record["vertices"]):
        claimed = F(entry["lower"])
        assert bound(vertex, lo, midpoint, lam, d) >= claimed >= lower
    assert min(F(v["lower"]) for v in record["vertices"]) == lower
    vertex_count += len(actual)
assert vertex_count == 1193

# Each root is partitioned by explicitly checked midpoint cuts. The only
# singleton leaves are cross-referenced to other accepted closed cells.
seen = set()
singletons = 0


def check_cover(node, lo, hi, minj, high):
    global singletons
    if "case" in node:
        case_id = node["case"]
        record = records[case_id]
        assert record["minj"] == minj
        assert tuple(record["high"]) == high
        assert fractions(record["lo"]) == lo
        assert fractions(record["hi"]) == hi
        seen.add(case_id)
        return
    if "singleton" in node:
        v = fractions(node["singleton"])
        assert vertices(lo, hi, minj) == (v,)
        record = records[node["covered_by"]]
        assert record["minj"] == minj
        assert v in vertices(fractions(record["lo"]),
                             fractions(record["hi"]), minj)
        singletons += 1
        return
    i = node["cut_index"]
    midpoint = F(node["cut_value"])
    assert 0 <= i < 5 and midpoint == (lo[i]+hi[i])/2
    assert lo[i] < midpoint < hi[i]
    left_hi, right_lo = list(hi), list(lo)
    left_hi[i], right_lo[i] = midpoint, midpoint
    check_cover(node["left"], lo, tuple(left_hi), minj, high)
    check_cover(node["right"], tuple(right_lo), hi, minj, high)


roots = iter(data["cover"])
root_count = 0
for minj in (1, 2):
    others = [i for i in range(1, 5) if i != minj]
    for n in (0, 1, 2):
        for high in combinations(others, n):
            for ml, mh in ((F(0), F(45, 2)), (F(45, 2), F(36)),
                           (F(36), F(72))):
                root = next(roots)
                assert root["minj"] == minj
                assert tuple(root["high"]) == high
                assert fractions(root["min_range"]) == (ml, mh)
                highs = {0, *high}
                lo = tuple(ml if i == minj else F(90 if i in highs else 0)
                           for i in range(5))
                hi = tuple(mh if i == minj else F(180 if i in highs else 90)
                           for i in range(5))
                check_cover(root["tree"], lo, hi, minj, high)
                root_count += 1
assert next(roots, None) is None
assert root_count == 42 and singletons == 2
assert seen == set(records)
print(f"PASS: {len(records)} cases, {vertex_count} exact vertices, "
      f"{root_count} covering roots, 2 explicitly covered singleton leaves.")
print(f"Uniform lower bound: {uniform} > 4.")
