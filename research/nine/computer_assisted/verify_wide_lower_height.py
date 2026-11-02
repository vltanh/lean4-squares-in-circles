#!/usr/bin/env python3
"""Exact replay of two wide-main low-floor opposite-height lemmas.

Imports only the separately reviewed exact physical-clearance evaluator;
neither numerical producer nor numerical discovery is imported.
"""
from fractions import Fraction as F
from pathlib import Path
import copy,hashlib,json,sys,time
from verify_wide_central_pair import I,SCALE,mainshape,free_shape,clearance

HERE=Path(__file__).resolve().parent
L=F(29,60);DELTA=F(331,20000);EDGE=1+DELTA

def root(own):
    return ((F(1,2),F(13,20)),(F(1,2),F(13,20)),(F(0),F(1)),
            (F(0),F(1)),(F(0),L),(F(0)if own else -L,L))

def values(box,own):
    b=mainshape(*box[0]);c=mainshape(*box[1])
    f=free_shape(*box[2]);g=free_shape(*box[3]);xf=I(*box[4]);xg=I(*box[5])
    V=b.eta+c.eta
    bl=b.h-EDGE;br=I(DELTA)-b.g-c.eta
    cl=c.g+b.eta-DELTA;cr=I(EDGE)-c.h
    def low(z):return F(z.lo,SCALE)
    def high(z):return F(z.hi,SCALE)
    def dist(x,y):return high((x-y).abs())
    bf=clearance(b,f,max(dist(xf,bl),dist(xf,br)))
    cf=clearance(c,f,max(dist(xf,cl),dist(xf,cr)))
    bg=clearance(b,g,max(dist(xg,bl),dist(xg,br)))
    cg=clearance(c,g,max(dist(xg,cl),dist(xg,cr)))
    middle=clearance(b,c,high(cr-bl))
    left=min(clearance(b,f,dist(xf,bl))+clearance(b,g,dist(xg,bl)),
             clearance(b,f,dist(xf,br))+clearance(b,g,dist(xg,br)))
    right=min(clearance(c,f,dist(xf,cl))+clearance(c,g,dist(xg,cl)),
              clearance(c,f,dist(xf,cr))+clearance(c,g,dist(xg,cr)))
    lower=max(left,right,middle+min(cf+bg,bf+cg))-high(f.h)-F(1,10)
    target=high(g.h)+F(9,20)if own else F(3,5)
    return low(V)-F(1,30),lower-target

def verify(data):
    assert data['type']=='wide_main_low_floor_lower_height_v1'
    own=data['own_half_floor'];assert type(own)is bool
    ROOT=root(own)
    assert tuple(tuple(map(F,row))for row in data['root'])==ROOT
    assert (2+DELTA)**2-(F(1105,256)-F(1,4))==F(27061,400000000)>0
    assert 1-(L+EDGE-F(1,2))==F(7,60000)>0
    pending=1
    for tag in data['events']:
        assert pending>0 and type(tag)is int and -2<=tag<=5
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
            rule=-tag-1;reserve=values(box,own)[rule]
            assert reserve>0,(position,rule,str(reserve),box)
            least=reserve if least is None else min(least,reserve)
            leaves+=1;counts[rule]+=1
    assert not todo and leaves==data['leaves']
    assert len(data['events'])==data['nodes']==2*leaves-1
    assert depthmax==data['maximum_depth']
    return {'status':'EXACT_REPLAY_PASSED','own_half_floor':own,
            'leaves':leaves,'nodes':len(data['events']),'maximum_depth':depthmax,
            'minimum_exact_reserve':str(least),'leaf_rules':counts,
            'root':[[str(a),str(b)]for a,b in ROOT],
            'strict_center_gap_reserve':'7/60000',
            'arithmetic':'64-bit directed integer enclosures and exact rational tree endpoints',
            'scope':('A low-floor upper central original forces every same-half lower central original to have whole ceiling below -9/20.'if own else 'A low-floor upper central original forces every lower central original to have center below -3/5.')+' Outer main links actual; middle arbitrary; closed Q-disk; not a whole-mask closure.'}

def controls(data):
    damaged=[]
    q=copy.deepcopy(data);q['root'][4][1]='2/5';damaged.append(('omitted_root_face',q))
    q=copy.deepcopy(data);q['events'][0]=6;damaged.append(('unknown_split_axis',q))
    q=copy.deepcopy(data);q['events']=q['events'][:-1];damaged.append(('missing_child',q))
    q=copy.deepcopy(data);q.update(events=[-2],nodes=1,leaves=1,maximum_depth=0);damaged.append(('false_unsplit_terminal',q))
    rows=[]
    for name,q in damaged:
        try:verify(q)
        except (AssertionError,ValueError,ZeroDivisionError) as e:
            rows.append({'control':name,'status':'REJECTED','reason':str(e)[:250]})
        else:raise AssertionError('False control accepted: '+name)
    return {'status':'ALL_DAMAGED_CONTROLS_REJECTED','controls':rows}

def main():
    path=Path(sys.argv[1])if len(sys.argv)>1 else HERE/'wide_lower_height_candidate.json'
    raw=path.read_bytes();data=json.loads(raw);start=time.monotonic();report=verify(data)
    report.update(certificate_sha256=hashlib.sha256(raw).hexdigest(),
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  clearance_checker_sha256=hashlib.sha256((HERE/'verify_wide_central_pair.py').read_bytes()).hexdigest(),
                  seconds=time.monotonic()-start)
    prefix='wide_own_lower_floor'if data['own_half_floor']else'wide_lower_height'
    (HERE/(prefix+'_exact_replay.json')).write_text(json.dumps(report,indent=2)+'\n')
    (HERE/(prefix+'_negative_controls.json')).write_text(json.dumps(controls(data),indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
