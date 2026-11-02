#!/usr/bin/env python3
"""Independent Fraction reconstruction of the low-side/lower-central cover.

Only the independently accepted Fraction interval class is reused.  Neither
the producer evaluator nor the producer dyadic kernel is imported.
"""
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import hashlib
import itertools
import json
import sys
import time
from verify_ownhalf_above_side import Interval as I, minimum as low, maximum as high

ROOT=((F(0),F(1)),(F(0),F(1)),(F(0),F(1129,3000)),
      (F(7,10),F(13,12)),(F(1,2),F(57,100)))
Q=F(1105,256)
DELTA=F(331,20000)
J=F(29927,30000)


@lru_cache(maxsize=None)
def orientation(bounds):
    left,right=bounds
    vals=[]
    for t in (left,right):
        norm=I(1+t*t).sqrt()
        vals.append((1/norm,t/norm,(1+t)/(2*norm),(1-t)/(2*norm)))
    L,R=vals
    return I(R[0].lo,L[0].hi),I(L[1].lo,R[1].hi),I(L[2].lo,R[2].hi),I(R[3].lo,L[3].hi)


def signed_upper(x,h,k,sign):
    # All four original corners are retained, rather than selecting two.
    offsets=((k,h),(h,-k),(-k,-h),(-h,k)) if sign>0 else ((h,k),(k,-h),(-h,-k),(-k,h))
    return low((I(Q)-(x+dx).square()).sqrt()-dy for dx,dy in offsets)


def expressions(box,signs):
    tP,tR,x,X,h=(I(*bounds)for bounds in box)
    sP,sR=signs
    aP,bP,p,kP=orientation(box[0])
    aR,bR,r,kR=orientation(box[1])
    g=1/(4*h)
    eta=h+g-1
    tau=high((2*bR,6*bR-F(27,2)*(1-aR)))
    adjusted_left=eta+high((I(F(59,60)),F(157,184)+F(27,92)*(X-r)+tau/46))
    adjusted_right=F(59,60)+eta

    delta_width=(p-h).absolute()
    unweighted=[]
    weighted=[]
    for z in (F(29,60),F(121,200)):
        for w in (g-DELTA,1+DELTA-h):
            dMS=z-w
            dSP=x+z
            for increment_first in (False,True):
                first_radius=1+delta_width if increment_first else I(1)
                second_radius=I(1) if increment_first else 1+delta_width
                total=(first_radius.square()-dMS.square()).sqrt()+(second_radius.square()-dSP.square()).sqrt()
                unweighted.append(total)
                weighted.append(w+total)
    edge=low((adjusted_left,I(F(61,60))))
    endpoint_cone=edge+(I(Q)-(edge+J).square()).sqrt()
    Pmin=high((-F(61,60)+low(unweighted),low(weighted)-endpoint_cone))
    own_inset=F(25,57)+low((p,(F(1,2)+(x-DELTA)*bP)/aP,
                           (F(1,2)+(x-DELTA)*aP)/high((bP,I(F(1,40))))))
    Pmin=high((Pmin,-F(61,60)+high((I(F(909,1000)),own_inset))))
    Pmax=low((p+F(1,10),signed_upper(x,p,kP,sP)))
    edgeR=low((adjusted_right,I(F(61,60))))
    inset_height=high((F(4421,12000)+F(32,9)*eta,
                       1-(I(Q)-(edgeR+J).square()).sqrt()))
    q=F(503,480)-X
    if sR>0:
        loss=high((I(0),tR*(kR+q)))
    else:
        loss=high((I(0),(q-kR)/high((tR,I(F(1,4))))))
    Rmin=high((I(F(3,5)),inset_height+r-loss))
    Rmax=signed_upper(X,r,kR,sR)
    D=X-x
    Pmin=high((Pmin,Rmin-D))
    Pmax=low((Pmax,Rmax+D))
    Rmin=high((Rmin,Pmin-D))
    Rmax=low((Rmax,Pmax+D))
    lower=high((Rmin-Pmax,-D))
    upper=low((Rmax-Pmin,D))
    scalar_product=aP*aR+sP*sR*bP*bR
    determinant=sR*aP*bR-sP*bP*aR
    support=(1+scalar_product.absolute()+determinant.absolute())/2
    signed_axes=((aP,sP*bP),(-sP*bP,aP),(aR,sR*bR),(-sR*bR,aR))
    largest_projection=high((nx*D+ny*y).absolute()for nx,ny in signed_axes for y in (lower,upper))
    return (Pmax-Pmin,Rmax-Rmin,F(1,30)-eta,
            F(61,60)-adjusted_left,F(61,60)-adjusted_right,
            r+F(451,810)-X-F(92,27)*eta-F(2,27)*tau,
            upper-lower,D-F(707,1000),p+r-D,D-1/(4*p)-1/(4*r),
            largest_projection-support,
            D.square()+high((lower.square(),upper.square()))-support.square())


def integer(x):
    return type(x)is int


def verify(data):
    assert data['schema']=='low_side_with_lower_central_v1'
    assert data['status']=='COMPLETE_PENDING_INDEPENDENT_REPLAY'
    assert data['root']==[[str(a),str(b)]for a,b in ROOT]
    assert integer(data['remaining'])and data['remaining']==0 and data['pending']==[]
    roots,nodes=data['roots'],data['nodes']
    assert type(roots)is list and len(roots)==4
    assert type(nodes)is list
    assert integer(data['leaves'])and len(nodes)==2*data['leaves']-4
    assert integer(data['maximum_depth'])and 0<=data['maximum_depth']<=70
    assert type(data['counts'])is list and len(data['counts'])==12
    assert all(integer(n)and n>=0 for n in data['counts'])
    assert sum(data['counts'])==data['leaves']
    wanted=list(itertools.product((-1,1),repeat=2))
    assert [tuple(r['signs'])for r in roots]==wanted
    assert all(type(r)is dict and set(r)=={'index','signs'}for r in roots)
    assert all(integer(r['index'])and type(r['signs'])is list and all(integer(s)for s in r['signs'])for r in roots)
    seen=set();counts=[0]*12;depthmax=0;largest=None;per_root=[]
    for root in roots:
        before=sum(counts)
        todo=[(root['index'],ROOT,0)]
        while todo:
            index,box,depth=todo.pop()
            assert integer(index)and 0<=index<len(nodes)and index not in seen
            assert depth<=70
            seen.add(index);depthmax=max(depthmax,depth)
            node=nodes[index]
            assert type(node)is dict
            if 'rule'in node:
                assert set(node)=={'rule','upper'}
                rule=node['rule']
                assert integer(rule)and 0<=rule<12 and type(node['upper'])is str
                bound=expressions(box,tuple(root['signs']))[rule].hi
                assert bound<0,('non-strict leaf',index,rule,box,root['signs'],bound)
                largest=bound if largest is None else max(largest,bound)
                counts[rule]+=1
            else:
                assert set(node)=={'axis','children'}
                axis,children=node['axis'],node['children']
                assert integer(axis)and 0<=axis<5
                assert type(children)is list and len(children)==2
                lo,hi=box[axis];mid=(lo+hi)/2
                left,right=list(box),list(box)
                left[axis]=(lo,mid);right[axis]=(mid,hi)
                todo.extend(((children[1],tuple(right),depth+1),(children[0],tuple(left),depth+1)))
        per_root.append(sum(counts)-before)
    assert len(seen)==len(nodes)
    assert counts==data['counts']and depthmax==data['maximum_depth']
    return {'result':'PASS','complete':True,'roots':4,'nodes':len(nodes),
            'strict_leaves':sum(counts),'leaves_per_root':per_root,'counts':counts,
            'maximum_depth':depthmax,'largest_replayed_upper':str(largest),
            'arithmetic':'independent Fraction intervals; outward 90-bit radical bounds',
            'scope':'low opposite side with lower central; no whole-mask assertion'}


def main():
    path=Path(sys.argv[1])if len(sys.argv)>1 else Path(__file__).with_name('low_side_with_lower_central_cover.json')
    started=time.monotonic();raw=path.read_bytes();data=json.loads(raw)
    report=verify(data)
    kernel=Path(__file__).with_name('verify_ownhalf_above_side.py')
    report.update(certificate_file=path.name,certificate_sha256=hashlib.sha256(raw).hexdigest(),
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  independent_fraction_kernel_sha256=hashlib.sha256(kernel.read_bytes()).hexdigest(),
                  producer_imports=False,seconds=time.monotonic()-started)
    path.with_name(path.stem+'_independent_replay.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
