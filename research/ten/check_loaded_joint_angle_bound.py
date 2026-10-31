#!/usr/bin/env python3
"""Exact verifier for the coupled loaded-ray angle certificate.

Only rational arithmetic and integer square brackets are used. The TSV
contains every leaf inequality; missing binary branches fail validation.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import isqrt
from pathlib import Path
import json
import argparse
import re

ROOT = Path(__file__).resolve().parent
META = ROOT / 'loaded_joint_angle_certificate.json'
LEAVES = ROOT / 'loaded_joint_angle_leaves.tsv'
RADICAL_SCALE = 10**10
MARGIN_SCALE = 10**9
FRAME_COUNT = 332
FRAME_DEN = 800
BETA_LO, BETA_HI = F(-2,7), F(1)

@lru_cache(maxsize=30000)
def trig(t):
    return 2*t/(1+t*t), (1-t*t)/(1+t*t)

@lru_cache(maxsize=30000)
def radius_bounds(sn, cs):
    w = abs(sn)+abs(cs)
    v = w*w+16
    scaled = v*RADICAL_SCALE**2
    k = isqrt(scaled.numerator//scaled.denominator)
    lo, hi = F(k,RADICAL_SCALE), F(k+1,RADICAL_SCALE)
    assert lo*lo <= v < hi*hi
    return (lo-w)/2, (hi-w)/2

SQ2_SCALED = isqrt(2*RADICAL_SCALE**2)
SQ2_LO = F(SQ2_SCALED,RADICAL_SCALE)
assert SQ2_LO**2 < 2 < F(SQ2_SCALED+1,RADICAL_SCALE)**2


def point_upper(alpha, beta, delta):
    sb, cb = trig(beta)
    if alpha is None:  # A frame-side kink: halfwidth is exactly 1/2.
        rl, rh = radius_bounds(sb,cb)
        a = (rh if sb>=0 else rl)*sb-F(1,2)
    else:
        sa,ca = trig(alpha)
        rl,rh = radius_bounds(sa,ca)
        h = (abs(sb*ca+cb*sa)+abs(cb*ca-sb*sa))/2
        a = (rh if sb>=0 else rl)*sb-h
    sd,cd = trig(delta)
    if beta <= delta:
        sg,cg = sd*cb-cd*sb,cd*cb+sd*sb
        assert sg>=0 and cg>0
        _,rh = radius_bounds(sg,cg)
        return a+rh*sg-F(1,2)
    sg = sb*cd-cb*sd
    assert sg>=0
    return a-SQ2_LO*sg-F(1,2)


def tasks(i,side):
    a,b=F(i,FRAME_DEN),F(i+1,FRAME_DEN)
    lo,hi=(-b,-a) if side=='G' else (a,b)
    out=[(lo,BETA_LO,BETA_HI),(hi,BETA_LO,BETA_HI)]
    for l,r in [(-hi,-lo),((1-hi)/(1+hi),(1-lo)/(1+lo))]:
        l,r=max(l,BETA_LO),min(r,BETA_HI)
        if l<r:out.append((None,l,r))
    return out


def segments(alpha,lo,hi,delta):
    points={lo,hi}
    candidates=[F(0),delta]
    if alpha is not None:
        candidates.extend([-alpha,(1-alpha)/(1+alpha)])
    points.update(p for p in candidates if lo<p<hi)
    points=sorted(points)
    return list(zip(points,points[1:]))


class CannotCertify(Exception):pass


def build_pair(i,side,delta):
    """Construct finite exact leaf bounds for one proposed pair threshold."""
    assert 0<delta<=F(1,2)
    leaves=[]
    for task,(alpha,lo,hi) in enumerate(tasks(i,side)):
        for seg,(l,r) in enumerate(segments(alpha,lo,hi,delta)):
            def visit(path,l,r,fl,fr):
                upper=max(fl,fr)+4*(r-l)**2
                margin=((-upper)*MARGIN_SCALE).__floor__()
                if margin>0:
                    leaves.append((i,side,task,seg,path or '-',margin))
                    return
                if fl>=0 or fr>=0 or len(path)>=22:
                    raise CannotCertify((i,side,str(delta),task,seg,path))
                mid=(l+r)/2;fm=point_upper(alpha,mid,delta)
                visit(path+'0',l,mid,fl,fm)
                visit(path+'1',mid,r,fm,fr)
            visit('',l,r,point_upper(alpha,l,delta),point_upper(alpha,r,delta))
    return leaves


def gap_margin(good,bad):
    tg=2*good/(1-good*good);tb=2*bad/(1-bad*bad)
    return tg+tb-45*(1-tg*tb)


def validate(meta,leaf_rows):
    assert meta['schema_version']==1
    assert meta['frame_count']==FRAME_COUNT and meta['frame_denominator']==FRAME_DEN
    assert meta['radical_scale']==RADICAL_SCALE and meta['margin_scale']==MARGIN_SCALE
    rows=meta['rows'];assert [r['i'] for r in rows]==list(range(FRAME_COUNT))
    groups={}
    for i,side,task,seg,path,margin in leaf_rows:
        key=(i,side,task,seg);path='' if path=='-' else path
        assert margin>0 and all(bit in '01' for bit in path)
        group=groups.setdefault(key,{})
        assert path not in group;group[path]=margin
    wanted=set();total=0
    for row in rows:
        i=row['i'];good,bad=F(row['good']),F(row['bad'])
        assert 0<good<=F(1,2) and 0<bad<=F(1,2)
        assert gap_margin(good,bad)>0
        count=0;minimum=None
        for side,delta in [('G',good),('B',bad)]:
            for task,(alpha,lo,hi) in enumerate(tasks(i,side)):
                for seg,(l,r) in enumerate(segments(alpha,lo,hi,delta)):
                    key=(i,side,task,seg);wanted.add(key);frontier=groups[key];seen=set()
                    def visit(path,l,r,fl,fr):
                        nonlocal count,minimum
                        if path in frontier:
                            seen.add(path)
                            upper=max(fl,fr)+4*(r-l)**2
                            margin=((-upper)*MARGIN_SCALE).__floor__()
                            assert margin==frontier[path]>0
                            count+=1;minimum=margin if minimum is None else min(minimum,margin)
                            return
                        assert any(p.startswith(path) for p in frontier),'Uncovered binary branch'
                        mid=(l+r)/2;fm=point_upper(alpha,mid,delta)
                        visit(path+'0',l,mid,fl,fm);visit(path+'1',mid,r,fm,fr)
                    visit('',l,r,point_upper(alpha,l,delta),point_upper(alpha,r,delta))
                    assert seen==set(frontier),'Prefix-overlapping or unreachable leaf'
                    assert sum((F(1,2**len(p)) for p in frontier),F(0))==1
        assert count==row['leaves'] and minimum==row['minimum_margin']
        total+=count
    assert wanted==set(groups),'Unexpected or missing smooth-segment root'
    assert total==meta['leaf_count']
    assert F(283,200)**2>2  # sqrt(2)-1 < 83/200 = 332/800.
    c=F(6291,10000);a=11-2*c-3*c*c;b=4+2*c+2*c*c
    assert a>0 and b>0 and 2*b*b-a*a>0
    t4=4*c*(1-c*c)/(1-6*c*c+c**4)
    assert -F(573,460)-t4>0
    assert F(14)>F(56,15)**2
    return total


def read_leaves():
    rows=[]
    for line in LEAVES.read_text().splitlines():
        if not line or line.startswith('#'):continue
        i,side,task,seg,path,margin=line.split('\t')
        rows.append((int(i),side,int(task),int(seg),path,int(margin)))
    return rows


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--print-summary',action='store_true');args=parser.parse_args()
    meta=json.loads(META.read_text());rows=read_leaves();total=validate(meta,rows)
    if args.print_summary:
        print('| Frame row | Good half-angle tangent | Bad half-angle tangent | Leaves | Minimum margin / 10^9 |')
        print('| ---: | --- | --- | ---: | ---: |')
        for r in meta['rows']:
            print(f"| {r['i']} | {r['good']} | {r['bad']} | {r['leaves']} | {r['minimum_margin']} |")
    else:
        note=(ROOT/'LOADED_JOINT_ANGLE_BOUND.md').read_text()
        pattern=re.compile(r'^\| (\d+) \| ([0-9/]+) \| ([0-9/]+) \| (\d+) \| (\d+) \|$')
        printed=[(int(m[1]),m[2],m[3],int(m[4]),int(m[5])) for line in note.splitlines() if (m:=pattern.fullmatch(line))]
        expected=[(r['i'],r['good'],r['bad'],r['leaves'],r['minimum_margin']) for r in meta['rows']]
        assert printed==expected,'Printed frame summary differs from exact certificate'
        print(f'PASS: {FRAME_COUNT} frame intervals, {total} exact leaf bounds; all smooth branches and kinks covered.')
        print('Smallest certified scaled leaf margin:',min(r['minimum_margin'] for r in meta['rows']))
        print('All coupled-angle and two-D whole-cycle comparisons pass exactly.')

if __name__=='__main__':main()
