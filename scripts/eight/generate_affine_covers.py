#!/usr/bin/env python3
"""Generate closed state/angle chain witnesses and uncompiled Lean proofs.

The traversal merely writes witnesses from the supplied closed intervals.
All coverage claims, including absent/empty groups, are finite propositions
proved by the emitted Lean source. No checker, Lean process, or CI is run.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from collections import defaultdict
from math import isqrt
import argparse,json

def f(x):return F(str(x))
def q(x):
    x=f(x);return str(x.numerator) if x.denominator==1 else f'({x.numerator}/{x.denominator})'
def iv(x):return '⟨'+','.join(q(v) for v in x)+'⟩'
def add(a,b):return a[0]+b[0],a[1]+b[1]
def neg(a):return -a[1],-a[0]
def sub(a,b):return add(a,neg(b))
def mul(a,b):
    p=[x*y for x in a for y in b];return min(p),max(p)
def scale(a,b):return mul(a,(b,b))
def inter(a,b):return max(a[0],b[0]),min(a[1],b[1])
def sqroot(a):
    n=isqrt(a.numerator*10**28//a.denominator)
    return F(n,10**14),F(n+1,10**14)
def down(a):return F(a.numerator*10**20//a.denominator,10**20)
def up(a):return -down(-a)
@lru_cache(None)
def atan_data(x):
    rt=sqroot(1+x*x)
    y=(x/(1+rt[1]),x/(1+rt[0]))
    total=(F(0),F(0));upper=None
    for j in range(26):
        p=(y[0]**(2*j+1),y[1]**(2*j+1))
        total=add(total,scale(p,F((-1)**j,2*j+1)))
        if j==24:upper=total[1]
    return rt,(down(2*total[0]),up(2*upper))
def alpha(a):
    lo=atan_data(f(a['lo']))[1][0];hi=atan_data(f(a['hi']))[1][1]
    return (lo,hi) if a['sign']==1 else (-hi,-lo)
PI=(F(3141592653589793238,10**18),F(3141592653589793239,10**18))
def required(d,s,t,r):
    edge=s['role'];k=d.get('word',[0,1,0,1,0,1,1])[edge]
    ph=add(sub((F(19,25),F(710,113)-F(114,25)),alpha(s)),alpha(t))
    base=scale(PI,F(k,2))
    raw=sub(ph,base) if r==1 else sub(base,ph)
    diff=tuple(map(f,d.get('difference_ranges',{}).get(str(edge),['-7/10','7/10'])))
    if r==-1:diff=neg(diff)
    return inter(inter(raw,diff),(F(0),F(7,10)))
def chain(items,lo,hi):
    if hi<lo:return []
    cursor=lo;out=[]
    for idx,a,b in sorted(items,key=lambda v:(v[1],v[2])):
        if b<cursor:continue
        out.append(idx);cursor=max(cursor,b)
        if hi<=cursor:break
    return out
def axis(i):return ['.one','.two','.three','.four'][i-1]
def nsname(src):return ''.join(x.title() for x in src.stem.removesuffix('_HAND_DATA').lower().split('_'))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[2]);args=ap.parse_args()
    base=args.root/'research/eight';out=args.root/'SquaresInCircles/Eight/Generated/Affine';records=[]
    for src in sorted(base.glob('*HAND_DATA.json')):
        d=json.loads(src.read_text())
        if not isinstance(d,dict) or not isinstance(d.get('arcs'),list) or not isinstance(d.get('rows'),list):continue
        name=nsname(src);dest=out/name;ns='SquaresInCircles.Eight.Generated.Affine.'+name
        arcs=d['arcs'];indices={a['id']:i for i,a in enumerate(arcs)}
        lines=['module','',f'public import {ns}.Claims',
            'public import SquaresInCircles.Eight.Arithmetic.AffineCoverage','',
            '/-! Complete closed state/angle witnesses. Uncompiled; no replay or audit. -/','',
            '@[expose] public section',f'namespace {ns}','open Arithmetic','',
            'def angleEndpoints : List (ArctanEndpoint × ArctanEndpoint) := [']
        for a in arcs:
            ends=[]
            for side in ('lo','hi'):
                x=f(a[side]);rt,bounds=atan_data(x)
                ends.append('⟨'+q(x)+','+iv(rt)+','+iv(bounds)+'⟩')
            lines.append('  ('+','.join(ends)+'),')
        lines[-1]=lines[-1].removesuffix(',')+']'
        lines += ['','def stateChains : StateChains := fun i outer =>','  match i.val,outer with']
        for role in range(7):
            lo,hi=map(f,d.get('cuts',{}).get(str(role),[-1,1]))
            for outer in (False,True):
                selected=[]
                for idx,a in enumerate(arcs):
                    if a['role']!=role or (a['kind']=='O')!=outer:continue
                    I=tuple(map(f,[a['lo'],a['hi']]))
                    if a['sign']==-1:I=neg(I)
                    selected.append((idx,*I))
                ids=chain(selected,lo,hi)
                lines.append(f'  | {role},{str(outer).lower()} => ['+','.join(map(str,ids))+']')
        lines += ['  | _,_ => []','']
        groups=defaultdict(list)
        for idx,row in enumerate(d['rows']):
            key=(indices[row['source']],indices[row['target']],row['axis'],row['r'])
            groups[key].append((idx,f(row['lo']),f(row['hi'])))
        bysource=defaultdict(list)
        for (s,t,ax,r),items in sorted(groups.items()):
            lo,hi=required(d,arcs[s],arcs[t],r)
            ids=chain(items,lo,hi)
            if ids:bysource[s].append((t,ax,r,ids))
        for s,items in sorted(bysource.items()):
            lines += [f'def angleRows{s:03d} (t : ℕ) (axis : ForwardAxis) (r : Bool) : List ℕ :=',
                '  match t,axis,r with']
            for t,ax,r,ids in items:
                lines.append(f'  | {t},{axis(ax)},{str(r==1).lower()} => ['+','.join(map(str,ids))+']')
            lines += ['  | _,_,_ => []','']
        lines += ['def angleRows (s t : ℕ) (axis : ForwardAxis) (r : Bool) : List ℕ :=','  match s with']
        lines += [f'  | {s} => angleRows{s:03d} t axis r' for s in sorted(bysource)]
        lines += ['  | _ => []','',
            'def cover : AffineCover := ⟨angleEndpoints,stateChains,angleRows⟩','',
            'set_option maxRecDepth 1000000 in','set_option maxHeartbeats 0 in',
            'theorem cover_numeric : cover.NumericValid meta rows := by','  decide','',
            'theorem word_matches : ∀ i, (meta.word i:ℝ)=(Candidate.word i:ℝ) := by',
            '  intro i; fin_cases i <;> norm_num [meta,Candidate.word]','',
            'noncomputable def charged_bound (C : BoundaryCycle (meta.radius:ℝ))',
            '    (F : Candidate.Frame C) (β : ℝ)',
            '    (hcharge : ∀ i, (meta.charge i:ℝ)=Candidate.charge β i)',
            '    (hcuts : ∀ i, (meta.cuts i).Mem (C.tangent i))',
            '    (hdiff : ∀ i, (meta.differenceRange i).Mem (Candidate.delta F.theta i))',
            '    (haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →',
            '      ForwardAxis.ofIndex j∈meta.allowedAxes i) :',
            '    Candidate.ChargedBound C F β (fun i => (meta.target i:ℝ)) :=',
            '  cover.chargedBound cover_numeric all_row_claims C F β word_matches hcharge hcuts hdiff haxes','',
            f'end {ns}','']
        (dest/'Cover.lean').write_text('\n'.join(lines))
        records.append({'module':name,'angle_groups':sum(len(x) for x in bysource.values()),'arcs':len(arcs)})
        print(f'Generated {name}: closed state and angle witnesses',flush=True)
    (out.parent/'AffineCovers.lean').write_text('module\n\n'+'\n'.join(
        f'public import SquaresInCircles.Eight.Generated.Affine.{r["module"]}.Cover' for r in records)+'\n')
    (out/'cover_generation_index.json').write_text(json.dumps({'status':'closed-cover-proof-scripts-uncompiled',
        'verification':'not run','tables':records},indent=2)+'\n')

if __name__=='__main__':main()
