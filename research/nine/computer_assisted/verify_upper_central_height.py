#!/usr/bin/env python3
"""Exact upper-central height cover, importing only accepted exact helpers."""
from fractions import Fraction as F
from pathlib import Path
import copy,hashlib,json,sys,time

HERE=Path(__file__).resolve().parent
HELPERS=HERE if (HERE/'verify_wide_central_pair.py').exists() else HERE.parents[1]/'root_wide_pair'
sys.path.insert(0,str(HELPERS))
from verify_wide_central_pair import I,SCALE,mainshape,free_shape,clearance

ROOT=((F(1,2),F(13,20)),(F(1,2),F(13,20)),(F(0),F(1)),(F(0),F(29,60)))

def values(box):
    b=mainshape(*box[0]);c=mainshape(*box[1]);f=free_shape(*box[2]);x=I(*box[3])
    V=b.eta+c.eta
    bl=b.h-F(61,60);br=I(F(1,60))-b.g-c.eta
    cl=c.g+b.eta-F(1,60);cr=I(F(61,60))-c.h
    def low(z):return F(z.lo,SCALE)
    def high(z):return F(z.hi,SCALE)
    def distance(z):return high((x-z).abs())
    left=min(-high(bl)+clearance(b,f,distance(bl)),
             -high(br)+clearance(b,f,distance(br)))
    right=min(low(cl)+clearance(c,f,distance(cl)),
              low(cr)+clearance(c,f,distance(cr)))
    cb=clearance(b,f,max(distance(bl),distance(br)))
    cc=clearance(c,f,max(distance(cl),distance(cr)))
    middle=clearance(b,c,high(cr-bl))
    middle_y=middle-F(129,80)+min(-high(br)+cc,low(cl)+cb)
    y=max(F(-3,10),-F(129,80)+left,-F(129,80)+right,
          -F(379,240)+F(16,9)*low(V)+(left+right)/2,middle_y)
    return low(V)-F(1,30),y+F(7,40)

def verify(data):
    assert data['type']=='wide_main_upper_central_height_v1'
    assert tuple(tuple(map(F,row))for row in data['root'])==ROOT
    assert type(data['events'])is list
    pending=1
    for tag in data['events']:
        assert pending>0 and type(tag)is int and -2<=tag<=3
        pending+=1 if tag>=0 else -1
    assert pending==0
    todo=[(ROOT,0)];leaves=0;depthmax=0;least=None;counts=[0,0]
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
            'scope':'Outer-actual original cone-four mains and one original central unit above both inner mains in closed Q imply its center height > -7/40. Middle link arbitrary; no full mask closure.',
            'arithmetic':'64-bit directed integer intervals, exact rational tree endpoints'}

def controls(data):
    cases=[]
    q=copy.deepcopy(data);q['root'][3][0]='1/100';cases.append(('omitted_root_face',q))
    q=copy.deepcopy(data);q['events'][0]=4;cases.append(('unknown_split_axis',q))
    q=copy.deepcopy(data);q['events']=q['events'][:-1];cases.append(('missing_child',q))
    q=copy.deepcopy(data);q.update(events=[-2],nodes=1,leaves=1,maximum_depth=0);cases.append(('false_unsplit_terminal',q))
    report=[]
    for name,q in cases:
        try:verify(q)
        except (AssertionError,ValueError,ZeroDivisionError)as e:
            report.append({'control':name,'status':'REJECTED','reason':str(e)[:250]})
        else:raise AssertionError('False control accepted: '+name)
    return {'status':'ALL_DAMAGED_CONTROLS_REJECTED','controls':report}

def main():
    path=Path(sys.argv[1])if len(sys.argv)>1 else HERE/'upper_central_height_candidate.json'
    raw=path.read_bytes();data=json.loads(raw);start=time.monotonic();report=verify(data)
    report.update(certificate_sha256=hashlib.sha256(raw).hexdigest(),checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),clearance_checker_sha256=hashlib.sha256((HELPERS/'verify_wide_central_pair.py').read_bytes()).hexdigest(),seconds=time.monotonic()-start)
    (HERE/'upper_central_height_exact_replay.json').write_text(json.dumps(report,indent=2)+'\n')
    (HERE/'upper_central_height_negative_controls.json').write_text(json.dumps(controls(data),indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
