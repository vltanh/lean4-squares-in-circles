#!/usr/bin/env python3
"""Independent exact replay of the sharp small-main-tilt scalar cover.

Uses direct absolute-support penalties and a directed64-bit integer
interval kernel. No producer or producer interval expression is imported.
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
ROOTS=((0,((F(-1),F(-1,32)),)),(0,((F(1,32),F(1)),)),
       (1,((F(-1),F(-1,32)),)),(1,((F(1,32),F(1)),)),
       (2,((F(-1),F(1)),)),
       (3,((F(-1),F(-1,32)),(F(0),F(1,3)))),
       (3,((F(1,32),F(1)),(F(0),F(1,3)))),
       (4,((F(-1),F(-1,32)),(F(0),F(1,3)))),
       (4,((F(1,32),F(1)),(F(0),F(1,3)))))

def mini(*xs):return I.raw(min(x.lo for x in xs),min(x.hi for x in xs))
def maxi(*xs):return I.raw(max(x.lo for x in xs),max(x.hi for x in xs))
def norm(w,c):return (w*w+K*K+2*w*K*c).sqrt()
def owned(w,c,s):return (w*c.abs()+2*w*s+(w*c+K).abs()+K)/2
def diagonal(w,c,s,ell):return (ell.sq()+w*w+w*K*c+2*w*K*s+K*(w*c+K).abs())/(2*ell)
def sharp(alpha,beta):return K*beta-(A+K)*(1-alpha)

def evaluate(channel,box):
    c=I(*box[0]);s=(1-c.sq()).sqrt();la=norm(A,c);lb=norm(B,-c)
    H=I(Q).sqrt()*(la+lb)
    if channel<=2:
        tau=sharp(maxi(c.abs(),s),mini(c.abs(),s))
        other=(B+K*(s+maxi(-c,I(0))) if channel==0 else
               owned(B,-c,s) if channel==1 else diagonal(B,-c,s,lb))
        answer=T-H+owned(A,c,s)+other-tau
    else:
        t=I(*box[1]);alpha=1/(1+t.sq()).sqrt();beta=t*alpha;eps=1 if channel==3 else -1
        def support(x,y):return ((x*alpha+eps*y*beta).abs()+(-eps*x*beta+y*alpha).abs())/2
        pm=A*(alpha+beta)/2+support(A+K*c,K*s)+K*support(c,s)
        answer=T-H+pm+owned(B,-c,s)-sharp(alpha,beta)
    return F(answer.lo,SCALE)

def analytic_checks():
    collar=(A-3*K/2-(A+K)/32,K/2-(A+K)/32,
            A-3*K/2-(A+B)/32,B-K/2-(A+B)/32,
            K/8-(F(13,10)*K+B)/32,B-K/2-(F(13,10)*K+B)/32,
            K/2-(K+B)/32,B+K/2-(K+B)/32)
    expected=(F(12673,512),F(2369,512),F(1583,64),F(331,64),
              F(3429,5120),F(31149,5120),F(2889,512),F(9801,512))
    assert collar==expected and min(collar)>0
    assert F(1,32)<K/A and F(1,32)<K/B
    # t<=1/3 gives alpha-beta>=2/sqrt10>5/8 and alpha+beta<=4/sqrt10<13/10.
    assert F(4,10)>F(25,64) and F(16,10)<F(169,100)
    assert A-2*K==F(161,8)>0 and A-K-K/32==F(16721,512)>0
    # t>=1/3 implies (1-alpha)/beta>=sqrt10-3>143/943=(k-4)/(a+k).
    assert (K-4)/(A+K)==F(143,943)
    assert 10*943**2-2972**2==59706>0
    return [str(x)for x in collar]

def verify(data):
    assert data['type']=='sharp_small_main_endpoint_tilt_toll_v1'
    assert data['toll']=='(207/16)*beta-(943/16)*(1-alpha)'
    assert data['status']=='complete_pending_independent_replay'
    assert len(data['trees'])==len(ROOTS)
    collars=analytic_checks();nodes=0;rows=[];least=None;deepest=0
    for tree,(channel,rootbox) in zip(data['trees'],ROOTS):
        assert tree['channel']==channel
        assert tuple(tuple(map(F,p))for p in tree['root'])==rootbox
        todo=[(rootbox,0)];leaves=0;depthmax=0;rowleast=None
        for tag in tree['events']:
            assert todo and type(tag)is int and -1<=tag<len(rootbox)
            box,depth=todo.pop();depthmax=max(depthmax,depth);nodes+=1
            if tag>=0:
                lo,hi=box[tag];mid=(lo+hi)/2;assert lo<mid<hi
                left=list(box);right=list(box);left[tag]=(lo,mid);right[tag]=(mid,hi)
                todo.extend([(tuple(right),depth+1),(tuple(left),depth+1)])
            else:
                reserve=evaluate(channel,box)
                assert reserve>0,(channel,[[str(x)for x in p]for p in box],str(reserve))
                rowleast=reserve if rowleast is None else min(rowleast,reserve)
                least=reserve if least is None else min(least,reserve);leaves+=1
        assert not todo and leaves==tree['leaves']
        assert len(tree['events'])==2*leaves-1==tree['nodes'] and depthmax==tree['maximum_depth']
        deepest=max(deepest,depthmax)
        rounded=(rowleast*1000000000).__floor__();assert rounded>0
        rows.append({'channel':channel,'root':tree['root'],'leaves':leaves,'maximum_depth':depthmax,
                     'minimum_exact_reserve':str(rowleast),'lower_numerator_over_billion':rounded})
    return {'status':'EXACT_REPLAY_PASSED','leaves':sum(x['leaves']for x in rows),'nodes':nodes,
            'maximum_depth':deepest,'minimum_exact_reserve':str(least),'rows':rows,
            'analytic_collar_coefficients':collars,'large_angle_four_beta_comparison_checked':True,
            'arithmetic':'64-bit outward integer dyadics; all N/D rows reconstructed from direct supports; no producer import',
            'scope':'Complete scalar and original-main-angle cover for the sharp curved main tilt toll; no full mask closure claimed.'}

def controls(data):
    tests=[]
    d=copy.deepcopy(data);d['trees'][5]['root'][1][1]='1/4';tests.append(('missing_main_tilt_interval',d))
    d=copy.deepcopy(data);d['trees'][5]['events'][0]=2;tests.append(('unknown_split_axis',d))
    d=copy.deepcopy(data);d['trees'][5]['events']=d['trees'][5]['events'][:-1];tests.append(('missing_child',d))
    d=copy.deepcopy(data);d['trees'][5].update(events=[-1],leaves=1,nodes=1,maximum_depth=0);tests.append(('false_whole_root_leaf',d))
    out=[]
    for name,d in tests:
        try:verify(d)
        except (AssertionError,ValueError,ZeroDivisionError) as e:out.append({'control':name,'status':'REJECTED','reason':str(e)[:300]})
        else:raise AssertionError('damaged control accepted: '+name)
    return {'status':'ALL_DAMAGED_CONTROLS_REJECTED','controls':out}

def main():
    source=Path(sys.argv[1])if len(sys.argv)>1 else HERE/'sharp_small_main_tilt_toll_cover.json'
    blob=source.read_bytes();data=json.loads(blob);begin=time.monotonic();report=verify(data)
    report.update(certificate_sha256=hashlib.sha256(blob).hexdigest(),
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-begin)
    (HERE/'sharp_small_main_tilt_toll_replay.json').write_text(json.dumps(report,indent=2)+'\n')
    neg=controls(data);neg['certificate_sha256']=report['certificate_sha256']
    (HERE/'sharp_small_main_tilt_toll_negative_controls.json').write_text(json.dumps(neg,indent=2)+'\n')
    print(json.dumps(report,indent=2));print(neg['status'])
if __name__=='__main__':main()
