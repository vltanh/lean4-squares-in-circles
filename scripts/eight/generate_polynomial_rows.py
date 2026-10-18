#!/usr/bin/env python3
"""Emit exact Lean polynomial identities from PR9's fixed arithmetic inputs.

This is a source generator, not a verifier.  It neither runs Lean nor calls
any research replay.  The emitted kernel-checkable expansion and rational
comparison proofs are the proof obligations.  A source PASS/hash is never
used to construct a Lean proposition.
"""
from __future__ import annotations
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import argparse
import json
import re


def rat(x):
    return Q(str(x))


def leanq(x):
    x=rat(x)
    return str(x.numerator) if x.denominator==1 else f"({x.numerator}/{x.denominator})"


def bernstein(p,lo,hi,n):
    p=list(map(rat,p))+[Q(0)]*(n+1-len(p))
    lo,hi=rat(lo),rat(hi)
    translated=[sum((p[j]*comb(j,k)*lo**(j-k)*(hi-lo)**k for j in range(k,n+1)),Q(0)) for k in range(n+1)]
    return [sum((translated[j]*Q(comb(k,j),comb(n,j)) for j in range(k+1)),Q(0)) for k in range(n+1)]


def ident(s):
    return re.sub(r'[^a-zA-Z0-9_]', '_', s)


def padd(a,b):
    return [(a[i] if i<len(a) else Q(0))+(b[i] if i<len(b) else Q(0)) for i in range(max(len(a),len(b)))]


def pmul(a,b):
    out=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out


def pscale(c,a):return [rat(c)*x for x in a]


def central_band_rows():
    z=[Q(1),Q(0),Q(1)];c=[Q(1),Q(0),Q(-1)];s=[Q(0),Q(2)]
    specs=[('segment',Q(1,2),Q(11,12),Q(11,12),Q(7,20),['0','1/4','1/2','1'],['0','3/14','3/7']),
           ('bandA',Q(5007,10000),Q(10007,10000)*Q(9308368,10**7),Q(10007,10000)*Q(9308369,10**7),Q(10007,10000)*Q(365435,10**6),['0','1/4','3/8','7/16','1/2','1'],['0','3/14','9/28','3/7']),
           ('bandB',Q(107,200),Q(41,40)*Q(9286,10000),Q(41,40)*Q(9287,10000),Q(41,40)*Q(371,1000),['0','1/2','1'],['0','3/14','15/56','9/28','3/7'])]
    out=[]
    for name,A,Cm,Cp,D,pcuts,vcuts in specs:
        H=padd(padd(pscale(Q(1,2),z),pscale(Cm,c)),pscale(-D,s))
        P=padd(padd(pmul(pmul(H,H),z),pmul(pmul(H,c),padd(c,s))),pscale(Q(1,2)-Q(9789,2500),pmul(pmul(c,c),z)))
        V=padd(padd(pscale(Q(1,2),pmul(c,z)),pscale(A,pmul(s,z))),padd(pscale(-Cp,pmul(s,c)),pscale(-D,pmul(c,c))))
        for letter,poly,cuts in [('P',P,pcuts),('V',V,vcuts)]:
            for i,(lo,hi) in enumerate(zip(cuts,cuts[1:])):
                out.append((f'central_{name}_{letter}{i}','CENTRAL_BAND_COMMON_POINT_LEMMAS.md',f'{name} {letter}, row {i}',poly,[lo,hi],len(poly)-1))
    return out


def extract(path):
    data=json.loads(path.read_text())
    out=[]
    if isinstance(data,dict) and isinstance(data.get('polynomials'),dict):
        keyed=data['polynomials']
        for row in data.get('rows',[]):
            if not isinstance(row,dict): continue
            name=row.get('name')
            if name in keyed and isinstance(keyed[name],list) and 'interval' in row:
                out.append((name,keyed[name],row['interval'],row.get('degree',len(keyed[name])-1)))
    def walk(obj,key):
        if isinstance(obj,dict):
            coefficients=obj.get('coefficients')
            interval=obj.get('interval')
            if isinstance(coefficients,list) and coefficients and isinstance(interval,list) and len(interval)==2:
                try: list(map(rat,coefficients)); list(map(rat,interval))
                except (ValueError,TypeError,ZeroDivisionError): pass
                else: out.append((key,coefficients,interval,obj.get('degree',len(coefficients)-1)))
            for k,v in obj.items(): walk(v,f'{key}_{k}')
        elif isinstance(obj,list):
            for i,v in enumerate(obj):
                if isinstance(v,(list,dict)):walk(v,f'{key}_{i}')
    walk(data,'poly')
    return out


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[2])
    args=ap.parse_args()
    research=args.root/'research/eight'
    output=args.root/'SquaresInCircles/Eight/Generated'
    output.mkdir(parents=True,exist_ok=True)
    entries=[]
    for source in sorted(research.glob('*arithmetic.json')):
        for name,p,bounds,n in extract(source):
            full=ident(source.stem.removesuffix('_hand_arithmetic')+'_'+name)
            entries.append((full,source.name,name,p,bounds,n))
    entries.extend(central_band_rows())
    chunks=[]
    for group in range((len(entries)+23)//24):
        rows=entries[24*group:24*(group+1)]
        module=f'WholePairPolynomials{group:03d}'
        text=['module','', 'public import SquaresInCircles.Eight.Arithmetic.Bernstein','',
              '/-! Generated source, schema eight-polynomial-v1. Uncompiled.','Exact polynomial data and full algebraic expansions; no report status is a premise. -/',
              '', '@[expose] public section','open scoped BigOperators','namespace SquaresInCircles.Eight.Generated','']
        for full,source,name,p,bounds,n in rows:
            lo,hi=map(rat,bounds);p=list(map(rat,p));b=bernstein(p,lo,hi,n)
            margin=min(b)/2
            text += [f'/-- Source: {source}, polynomial {name}. -/',
                     f'def {full} : Arithmetic.BernsteinRow :=',
                     f'  {{ interval := ⟨{leanq(lo)},{leanq(hi)}⟩',
                     '    polynomial := ['+', '.join(map(leanq,p))+']',
                     f'    degree := {n}',
                     '    coefficients := ['+', '.join(map(leanq,b))+'] }','',
                     f'theorem {full}_valid : {full}.Valid {leanq(margin)} := by',
                     '  constructor',f'  · norm_num [{full}]',f'  · rfl',
                     '  · intro t',
                     f'    norm_num [{full}, Arithmetic.QPoly.eval, Arithmetic.bernsteinEval,',
                     '      Arithmetic.bernsteinBasis, Arithmetic.BernsteinRow.coefficient,',
                     '      Finset.sum_range_succ]',
                     '    ring',
                     '  · intro i hi',f'    have hi\' : i ≤ {n} := hi',
                     f'    interval_cases i <;> norm_num [{full},Arithmetic.BernsteinRow.coefficient]','',
                     f'theorem {full}_positive {{x : ℝ}} (hx : ({leanq(lo)} : ℝ) ≤ x ∧ x ≤ {leanq(hi)}) :',
                     f'    0 < {full}.polynomial.eval x :=',
                     f'  {full}_valid.positive (by norm_num) hx','']
        text += ['end SquaresInCircles.Eight.Generated','']
        (output/f'{module}.lean').write_text('\n'.join(text))
        chunks.append(module)
    (output/'WholePairPolynomials.lean').write_text('module\n\n'+'\n'.join(f'public import SquaresInCircles.Eight.Generated.{x}' for x in chunks)+'\n')
    (output/'polynomial_generation_index.json').write_text(json.dumps({'schema':'eight-polynomial-v1','status':'uncompiled-source','rows':len(entries),'chunks':chunks,'sources':[{'declaration':x[0],'source':x[1],'polynomial':x[2]} for x in entries]},indent=2)+'\n')
    print(json.dumps({'generated_polynomial_rows':len(entries),'chunks':len(chunks),'verification':'not run'}))


if __name__=='__main__':main()
