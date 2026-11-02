#!/usr/bin/env python3
"""Independent integer replay of every MAIN endpoint tilt-toll scalar cell.

The producer's piecewise expressions are not imported.  Each penalty is
reconstructed directly from its absolute support expression.  The shared
directed-integer interval kernel is an already independently checked file.
"""
from fractions import Fraction as F
from pathlib import Path
import copy
import hashlib
import json
import sys
import time

HERE=Path(__file__).resolve().parent
BASE=HERE if (HERE/'verify_joint_five_dyadic.py').exists() else HERE.parents[1]/'pr11/research/nine/computer_assisted'
sys.path.insert(0,str(BASE))
from verify_joint_five_dyadic import I,SCALE

A=F(46);B=F(27,2);K=F(207,16);T=F(211,4);Q=F(1105,256)
ROOTS=((0,F(-1),F(-1,32)),(0,F(1,32),F(1)),
       (1,F(-1),F(-1,32)),(1,F(1,32),F(1)),
       (2,F(-1),F(1)),(3,F(-1),F(1)),(4,F(-1),F(1)))
def mini(*xs):return I.raw(min(x.lo for x in xs),min(x.hi for x in xs))
def maxi(*xs):return I.raw(max(x.lo for x in xs),max(x.hi for x in xs))
def norm(w,c):return (w*w+K*K+2*w*K*c).sqrt()
def owned(w,c,s):return (w*c.abs()+2*w*s+(w*c+K).abs()+K)/2
def diagonal(w,c,s,ell):return (ell.sq()+w*w+w*K*c+2*w*K*s+K*(w*c+K).abs())/(2*ell)
def toll(alpha,beta):return maxi(4*beta,10*beta-A*(1-alpha))

def evaluate(channel,lo,hi):
    c=I(lo,hi);s=(1-c.sq()).sqrt();la=norm(A,c);lb=norm(B,-c)
    H=I(Q).sqrt()*(la+lb);na=owned(A,c,s);nb=owned(B,-c,s)
    tn=toll(maxi(c.abs(),s),mini(c.abs(),s))
    if channel==0:answer=T-H+na+B+K*(s+maxi(-c,I(0)))-tn
    elif channel==1:answer=T-H+na+nb-tn
    elif channel==2:answer=T-H+na+diagonal(B,-c,s,lb)-tn
    elif channel==3:
        td=toll(maxi(A+K*c,K*s)/la,mini(A+K*c,K*s)/la)
        answer=T-H+diagonal(A,c,s,la)+nb-td
    else:
        assert channel==4
        r2=I(2).sqrt()
        pm=(A+maxi(A+K*c,K*s)+K*maxi(c.abs(),s))/r2
        answer=T-H+pm+nb-toll(1/r2,1/r2)
    return F(answer.lo,SCALE)

def verify(data):
    assert data['type']=='universal_main_endpoint_tilt_toll_v1'
    assert data['toll']=='max(4*beta,10*beta-46*(1-alpha))'
    assert len(data['trees'])==len(ROOTS)
    collar=(A-K/2-10-(A+K)/32,3*K/2-10-(A+K)/32,
            A-K/2-10-(A+B)/32,B+K/2-10-(A+B)/32)
    assert min(collar)>0 and F(1,32)<K/A and F(1,32)<K/B
    rows=[];nodes=0;largestdepth=0;least=None
    for tree,(channel,a,b) in zip(data['trees'],ROOTS):
        assert tree['channel']==channel and tuple(map(F,tree['root']))==(a,b)
        todo=[(a,b,0)];leaves=0;depthmax=0;rowleast=None
        for tag in tree['events']:
            assert todo and type(tag)is int and tag in(-1,0)
            lo,hi,depth=todo.pop();depthmax=max(depthmax,depth);nodes+=1
            if tag==0:
                mid=(lo+hi)/2;assert lo<mid<hi
                todo.extend([(mid,hi,depth+1),(lo,mid,depth+1)])
            else:
                reserve=evaluate(channel,lo,hi)
                assert reserve>0,(channel,str(lo),str(hi),str(reserve))
                rowleast=reserve if rowleast is None else min(rowleast,reserve)
                least=reserve if least is None else min(least,reserve)
                leaves+=1
        assert not todo
        assert leaves==tree['leaves'] and len(tree['events'])==2*leaves-1==tree['nodes']
        assert depthmax==tree['maximum_depth']
        largestdepth=max(largestdepth,depthmax)
        rounded=(rowleast*1000000).__floor__()
        assert rounded>0
        rows.append({'channel':channel,'root':[str(a),str(b)],'leaves':leaves,
                     'minimum_exact_reserve':str(rowleast),'lower_numerator_over_million':rounded})
    return {'status':'EXACT_REPLAY_PASSED','leaves':sum(r['leaves'] for r in rows),
            'nodes':nodes,'maximum_depth':largestdepth,'minimum_exact_reserve':str(least),
            'rows':rows,'analytic_collar_coefficients':[str(x) for x in collar],
            'arithmetic':'64-bit outward integer dyadics; direct support formulas; no producer import',
            'scope':'Five complete scalar rows for the universal original-main-square tilt toll; owner/frame reduction is a separate hand proof.'}

def controls(data):
    damaged=[]
    x=copy.deepcopy(data);x['trees'][0]['root'][0]='-9/10';damaged.append(('missing_root_interval',x))
    x=copy.deepcopy(data);x['trees'][0]['events'][0]=99;damaged.append(('unknown_split_rule',x))
    x=copy.deepcopy(data);x['trees'][0]['events']=x['trees'][0]['events'][:-1];damaged.append(('missing_child',x))
    x=copy.deepcopy(data);r=x['trees'][0];r.update(events=[-1],leaves=1,nodes=1,maximum_depth=0);damaged.append(('false_whole_root_leaf',x))
    answers=[]
    for label,x in damaged:
        try:verify(x)
        except (AssertionError,ValueError,ZeroDivisionError) as e:
            answers.append({'control':label,'status':'REJECTED','reason':str(e)[:300]})
        else:raise AssertionError('damaged control accepted: '+label)
    return {'status':'ALL_DAMAGED_CONTROLS_REJECTED','controls':answers}

def main():
    source=Path(sys.argv[1]) if len(sys.argv)>1 else HERE/'main_endpoint_tilt_toll_cover.json'
    blob=source.read_bytes();data=json.loads(blob);begin=time.monotonic();report=verify(data)
    report.update(certificate_sha256=hashlib.sha256(blob).hexdigest(),
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  seconds=time.monotonic()-begin)
    (HERE/'main_endpoint_tilt_toll_replay.json').write_text(json.dumps(report,indent=2)+'\n')
    neg=controls(data);neg['certificate_sha256']=report['certificate_sha256']
    (HERE/'main_endpoint_tilt_toll_negative_controls.json').write_text(json.dumps(neg,indent=2)+'\n')
    print(json.dumps(report,indent=2));print(neg['status'])
if __name__=='__main__':main()
