#!/usr/bin/env python3
"""Independent directed-integer replay of the one-low-main cover."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,sys

HERE=Path(__file__).resolve().parent
BASE=HERE if(HERE/'verify_joint_five_dyadic.py').exists()else HERE.parent/'pr11/research/nine/computer_assisted'
sys.path.insert(0,str(BASE))
from verify_joint_five_dyadic import I,SCALE,span
ROOT=((F(1,3),F(29,60)),(F(0),F(1)))
PRINTED_NUMERATORS=[-15611,-105722,-8192,-12442,-14803,-5190,-6632,
                    -16548,-873,-8507,-6588,-188,-3317,-4279,-4074,
                    -3004,-29561,-3638,-9636,-783,-3568,-2739,-912,
                    -12663,-42408]

def evaluate(box):
    frames=[]
    for tangent in box[1]:
        t=I(tangent);root=(1+t.sq()).sqrt()
        frames.append((1/root,t/root,(1+t)/(2*root),(1-t)/(2*root)))
    a,b,h,k=[span([f[j]for f in frames])for j in range(4)]
    x=I(*box[0]);q=F(1105,256)
    upper1=(q-(x+h).sq()).sqrt()-k
    upper2=(q-(x-k).sq()).sqrt()-h
    cap=I.raw(min(upper1.lo,upper2.lo,I(F(91,60)).lo),min(upper1.hi,upper2.hi,I(F(91,60)).hi))
    vertical=cap-F(9,10)-F(15,31);horizontal=x+F(1,60)
    first=a*horizontal+b*vertical-F(1,2)
    second=b*horizontal+a*vertical-F(1,2)
    return F(vertical.hi,SCALE),F(max(first.hi,second.hi),SCALE)

def verify(data):
    assert data['type']=='one_low_main_nine_tenths_cover_v1'
    assert data['proof_status']=='complete_pending_independent_replay'
    assert tuple(tuple(map(F,r))for r in data['root'])==ROOT
    assert F(91,60)-F(9,10)-F(15,31)<F(1,2)
    todo=[(ROOT,0)];counts=[0,0];depthmax=0;largest=[None,None]
    for event in data['events']:
        assert todo and isinstance(event,int)and not isinstance(event,bool)
        box,depth=todo.pop();depthmax=max(depthmax,depth)
        if event>=0:
            assert event<2;a,b=box[event];m=(a+b)/2
            lo,hi=list(box),list(box);lo[event]=(a,m);hi[event]=(m,b)
            todo.extend([(tuple(hi),depth+1),(tuple(lo),depth+1)])
        else:
            assert event in(-1,-2)
            v,w=evaluate(box);idx=-event-1;bound=[v,w][idx]
            assert bound<=0 if idx==0 else bound<0,(event,box,bound)
            assert bound<=F(PRINTED_NUMERATORS[sum(counts)],1000000)
            counts[idx]+=1;largest[idx]=bound if largest[idx]is None else max(largest[idx],bound)
    assert not todo and sum(counts)==data['leaves']and counts==data['leaf_counts']
    assert len(data['events'])==data['nodes']and depthmax==data['maximum_depth']
    assert sum(counts)==len(PRINTED_NUMERATORS)
    return {'nodes':len(data['events']),'leaves':sum(counts),'leaf_counts':counts,
            'maximum_depth':depthmax,'largest_replayed_uppers':[str(v)for v in largest],
            'all_printed_rational_bounds_verified':True,
            'proof_status':'independent_one_low_main_nine_tenths_replay_passed'}

def main():
    p=Path(sys.argv[1]);raw=p.read_bytes();report=verify(json.loads(raw))
    report.update(certificate_sha256=hashlib.sha256(raw).hexdigest(),
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (HERE/'one_low_main_nine_tenths_replay.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))

if __name__=='__main__':main()
