#!/usr/bin/env python3
"""Exact direct interval replay of the opposite-side 131 finite cover.

Imports no producer. The optional import flag only wraps an untrusted split
tree in the fixed exact root domain; every terminal is then recomputed.
"""
from pathlib import Path
from fractions import Fraction as F
import gzip,hashlib,json,sys,time

HERE=Path(__file__).resolve().parent
BASE=HERE if(HERE/'verify_joint_five_dyadic.py').is_file()else HERE.parent/'pr11/research/nine/computer_assisted'
sys.path.insert(0,str(BASE))
import verify_joint_five_dyadic as ar

ROOT=((F(-29,60),F(29,60)),(F(29,60),F(13,12)),
      (F(1,6),F(1)),(F(0),F(1)),(F(0),F(1)))

def packed(lo,hi):
    return ar.I.raw(lo,hi)if hasattr(ar,'SCALE')else ar.I(lo,hi)

def low(values):
    return packed(min(v.lo for v in values),min(v.hi for v in values))

def high(values):
    return packed(max(v.lo for v in values),max(v.hi for v in values))

def shape(bounds):
    left,right=map(ar.I,bounds)
    dl=(1+left.sq()).sqrt();dr=(1+right.sq()).sqrt()
    # a,k decrease and b,h,d increase on the whole folded slope interval.
    a=ar.span([1/dl,1/dr]);b=ar.span([left/dl,right/dr])
    h=ar.span([(1+left)/(2*dl),(1+right)/(2*dr)])
    k=ar.span([(1-left)/(2*dl),(1-right)/(2*dr)])
    den=ar.span([dl,dr]);g=1/(4*h)
    return a,b,h,k,g,den

def loss(s,t,frame):
    a,b,h,k,g,d=frame
    return high([ar.I(0),t*(k+s),(s-k)/high([t,ar.I(F(1,10000))])])

def circle(x,frame):
    a,b,h,k,g,d=frame;x=x.abs();q=F(1105,256)
    side=(q-(x+h).sq()).sqrt()
    one=low([(q-(x+k).sq()).sqrt()-h,side+k])
    two=low([(q-(x-k).sq()).sqrt()-h,side-k])
    radius=(ar.I(q-F(1,4))).sqrt()-F(1,2)
    return low([radius,high([one,two])])

def margins(box):
    x,z,s,t,u=[ar.I(a,b)for a,b in box]
    fp,fh,fb=shape(box[2]),shape(box[3]),shape(box[4])
    ap,bp,hp,kp,gp,dp=fp;ah,bh,hh,kh,gh,dh=fh;ab,bb,hb,kb,gb,db=fb
    delta=F(331,20000);g0=F(15,31)
    near=high([ar.I(0),s*(kp+delta+F(2,15)-gp)])
    far=loss(delta+F(11,15)-gp,s,fp)
    hleft=loss(x+delta,t,fh);hright=loss(delta-x,t,fh)
    bmargin=high([z-F(59,60),delta-z])
    bloss=high([ar.I(0),u*(kb+bmargin)])
    hlo=high([2*g0+hp+hh-F(3,5)-low([near+hleft,far+hright]),ar.I(g0+F(23,60))])
    blo=high([2*g0+hp+hb-F(3,5)-far-bloss,ar.I(g0+F(11,30))])
    hhi=circle(x,fh);bhi=circle(z,fb)
    dx=z-x;dy=high([ar.I(0),bhi-hlo,hhi-blo])
    support=high([ar.I(1),(1+(1+t*u+(t-u).abs())/(dh*db))/2])
    pair=high([ah*dx+bh*dy,bh*dx+ah*dy,ab*dx+bb*dy,bb*dx+ab*dy])-support
    ex=F(3,2)-z-F(217,480);ey=bhi-F(221,600)
    endpoint=high([ex-hb,ey-hb,ab*ex+bb*ey-F(1,2),bb*ex+ab*ey-F(1,2)])
    return [F(13,30)-gp,hhi-hlo,bhi-blo,pair,endpoint,F(19,20)-g0-hp+far]

def rational_upper(value):
    return F(value.hi,ar.SCALE)if hasattr(ar,'SCALE')else value.hi

def verify(data,progress=False):
    assert data['type']=='131_opposite_low_middle_direct_cover_v1'
    assert data['proof_status']=='complete_untrusted_tree_pending_exact_replay'
    assert tuple(tuple(map(F,b))for b in data['root'])==ROOT
    assert F(15,26)**2-F(49,148)==F(11,6253)>0
    assert F(7,60000)-F(1,20000)-F(1,400000000)==F(79997,1200000000)>0
    assert F(1105,256)-(F(13,12)+F(17,24))**2>0
    events=data['events'];stack=[(ROOT,0)];seen=leaves=depthmax=0;counts=[0]*6;largest=None
    start=last=time.monotonic()
    for event in events:
        assert stack,'event after the exact root has been exhausted'
        box,depth=stack.pop();seen+=1;depthmax=max(depthmax,depth)
        assert isinstance(event,int)and not isinstance(event,bool)
        if event>=0:
            assert event<5
            a,b=box[event];middle=(a+b)/2
            lo,hi=list(box),list(box);lo[event]=(a,middle);hi[event]=(middle,b)
            stack.extend([(tuple(hi),depth+1),(tuple(lo),depth+1)])
        else:
            rule=-event-1;assert 0<=rule<6
            bound=rational_upper(margins(box)[rule]);assert bound<0,(seen,rule,box,str(bound))
            leaves+=1;counts[rule]+=1;largest=bound if largest is None else max(largest,bound)
        now=time.monotonic()
        if progress and now-last>=25:
            print('OPPOSITE131 DIRECT REPLAY',leaves,'seconds',round(now-start,1),flush=True);last=now
    assert not stack,'uncovered exact midpoint boxes remain'
    assert seen==data['nodes']and leaves==data['leaves']and depthmax==data['maxdepth']
    return {'nodes':seen,'strict_interval_leaves':leaves,'rule_leaves':counts,
            'maximum_depth':depthmax,'largest_replayed_upper':str(largest),
            'complete':True,'seconds':time.monotonic()-start}

def main():
    if sys.argv[1]=='--import-discovery':
        raw=json.loads(Path(sys.argv[2]).read_text());assert raw['status']=='COMPLETE_UNTRUSTED_DISCOVERY'
        data={'type':'131_opposite_low_middle_direct_cover_v1',
              'proof_status':'complete_untrusted_tree_pending_exact_replay',
              'root':[[str(a),str(b)]for a,b in ROOT],
              **{k:raw[k]for k in ['nodes','leaves','maxdepth','events']}}
        path=Path(sys.argv[3]);path.write_bytes(gzip.compress((json.dumps(data,separators=(',',':'))+'\n').encode(),mtime=0))
    else:path=Path(sys.argv[1])
    raw=path.read_bytes();data=json.loads(gzip.decompress(raw));report=verify(data,True)
    report.update(proof_status='independent_131_opposite_low_middle_direct_replay_passed',
        certificate_sha256=hashlib.sha256(raw).hexdigest(),
        checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        arithmetic_sha256=hashlib.sha256(Path(ar.__file__).read_bytes()).hexdigest())
    (HERE/'131_opposite_low_middle_direct_replay.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report),flush=True)

if __name__=='__main__':main()
