#!/usr/bin/env python3
"""Exact complete low-side floor cover; imports no numerical producer."""
from fractions import Fraction as F
from pathlib import Path
import copy,hashlib,json,sys,time

HERE=Path(__file__).resolve().parent
HELPERS=HERE if (HERE/'verify_wide_central_pair.py').exists() else HERE.parents[1]/'root_wide_pair'
sys.path.insert(0,str(HELPERS))
from verify_wide_central_pair import I,SCALE,mainshape,free_shape,clearance

ROOT=((F(1,2),F(13,20)),(F(0),F(1)),(F(0),F(1)),(F(29,60),F(49,80)))

def values(box):
    c=mainshape(*box[0]);s=free_shape(*box[1]);f=free_shape(*box[2]);x=I(*box[3])
    def low(z):return F(z.lo,SCALE)
    def high(z):return F(z.hi,SCALE)
    eta=c.eta;edge=c.g-F(1,60)
    lower=max(-F(129,80),-F(197,120)+F(32,9)*low(eta))+low(edge)+clearance(c,s,high(x-edge))
    upper=min(F(3,5),F(1,10)+high(f.h)-clearance(s,f,high(x)))
    E=I(F(503,480))-x
    vertical=max(abs(lower),abs(upper))-(F(4421,12000)+F(32,9)*low(eta))
    ep=max(high(E-s.h),vertical-low(s.h),
           high(s.a*E+s.b*I(vertical))-F(1,2),
           high(s.b*E+s.a*I(vertical))-F(1,2))
    return low(eta)-F(1,30),lower-upper,-ep

def verify(data):
    assert data['type']=='wide_main_low_side_floor_v1'
    assert tuple(tuple(map(F,row))for row in data['root'])==ROOT
    assert type(data['events'])is list
    pending=1
    for tag in data['events']:
        assert pending>0 and type(tag)is int and -3<=tag<=3
        pending+=1 if tag>=0 else -1
    assert pending==0
    todo=[(ROOT,0)];leaves=0;depthmax=0;least=None;counts=[0,0,0]
    for position,tag in enumerate(data['events']):
        box,depth=todo.pop();depthmax=max(depthmax,depth)
        if tag>=0:
            lo,hi=box[tag];mid=(lo+hi)/2;assert lo<mid<hi
            a=list(box);b=list(box);a[tag]=(lo,mid);b[tag]=(mid,hi)
            todo.extend([(tuple(b),depth+1),(tuple(a),depth+1)])
        else:
            rule=-tag-1;reserve=values(box)[rule]
            assert reserve>0,(position,rule,str(reserve),box)
            least=reserve if least is None else min(least,reserve)
            leaves+=1;counts[rule]+=1
    assert not todo and leaves==data['leaves']
    assert len(data['events'])==data['nodes']==2*leaves-1
    assert depthmax==data['maximum_depth']
    return {'status':'EXACT_REPLAY_PASSED','nodes':len(data['events']),'leaves':leaves,
            'maximum_depth':depthmax,'minimum_exact_reserve':str(least),'leaf_rules':counts,
            'root':[[str(a),str(b)]for a,b in ROOT],
            'scope':'Outer-actual original cone-four mains, right-side original S above C with yS<3/5, and original upper right-central F imply F whole floor >1/10 in closed Q. Uses the separately certified upper-central center bound >-7/40; no mask closure.',
            'arithmetic':'64-bit directed integer intervals, exact rational tree endpoints'}

def controls(data):
    cases=[]
    q=copy.deepcopy(data);q['root'][3][0]='1/2';cases.append(('omitted_root_face',q))
    q=copy.deepcopy(data);q['events'][0]=4;cases.append(('unknown_split_axis',q))
    q=copy.deepcopy(data);q['events']=q['events'][:-1];cases.append(('missing_child',q))
    q=copy.deepcopy(data);q.update(events=[-3],nodes=1,leaves=1,maximum_depth=0);cases.append(('false_unsplit_terminal',q))
    report=[]
    for name,q in cases:
        try:verify(q)
        except (AssertionError,ValueError,ZeroDivisionError)as e:
            report.append({'control':name,'status':'REJECTED','reason':str(e)[:250]})
        else:raise AssertionError('False control accepted: '+name)
    return {'status':'ALL_DAMAGED_CONTROLS_REJECTED','controls':report}

def main():
    path=Path(sys.argv[1])if len(sys.argv)>1 else HERE/'low_side_floor_candidate.json'
    raw=path.read_bytes();data=json.loads(raw);start=time.monotonic();report=verify(data)
    report.update(certificate_sha256=hashlib.sha256(raw).hexdigest(),checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),clearance_checker_sha256=hashlib.sha256((HELPERS/'verify_wide_central_pair.py').read_bytes()).hexdigest(),seconds=time.monotonic()-start)
    (HERE/'low_side_floor_exact_replay.json').write_text(json.dumps(report,indent=2)+'\n')
    (HERE/'low_side_floor_negative_controls.json').write_text(json.dumps(controls(data),indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
