#!/usr/bin/env python3
"""Independent directed-integer replay of the five scalar tilt-toll rows.

The N and D penalties are recomputed from the owned-normal support formula,
not the producer's piecewise scalar expressions. No producer is imported.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,sys,time

HERE=Path(__file__).resolve().parent
BASE=HERE if(HERE/'verify_joint_five_dyadic.py').exists()else HERE.parent/'pr11/research/nine/computer_assisted'
sys.path.insert(0,str(BASE))
from verify_joint_five_dyadic import I,SCALE

Q=F(1105,256);W=F(46);V=F(27,2);K=F(207,16);T=F(211,4)
ROOTS=((0,F(-1),F(-1,8)),(0,F(1,8),F(1)),
       (1,F(-1),F(-1,8)),(1,F(1,8),F(1)),
       (2,F(-1),F(1)),(3,F(-1),F(1)),(4,F(-1),F(1)))
PRINTED_LOWER_NUMERATORS=(546970,13295,496498,535035,162,19648,55676)

def mini(*xs):return I.raw(min(x.lo for x in xs),min(x.hi for x in xs))
def maxi(*xs):return I.raw(max(x.lo for x in xs),max(x.hi for x in xs))
def norm(w,c):return (w*w+K*K+2*w*K*c).sqrt()

def owned(w,c,s):
    return (w*c.abs()+2*w*s+(w*c+K).abs()+K)/2

def diagonal(w,c,s,ell):
    return (ell.sq()+w*w+w*K*c+2*w*K*s+K*(w*c+K).abs())/(2*ell)

def evaluate(channel,lo,hi):
    c=I(lo,hi);s=(1-c.sq()).sqrt();la=norm(W,c);lb=norm(V,-c)
    hh=I(Q).sqrt()*(la+lb);nleft=owned(W,c,s);nright=owned(V,-c,s)
    toll=2*mini(c.abs(),s)
    if channel==0:answer=T-hh+W+K*(s+maxi(c,I(0)))+nright-toll
    elif channel==1:answer=T-hh+nleft+nright-toll
    elif channel==2:answer=T-hh+diagonal(W,c,s,la)+nright-toll
    elif channel==3:
        sd=mini(V-K*c,K*s)/lb
        answer=T-hh+nleft+diagonal(V,-c,s,lb)-2*sd
    else:
        assert channel==4
        # Fold boundary is the one square frame at 45 degrees modulo 90.
        adjusted=(V-2+maxi(V-K*c,K*s)+K*maxi(c.abs(),s))/I(2).sqrt()
        answer=T-hh+nleft+adjusted
    return F(answer.lo,SCALE)

def verify(data):
    assert data['type']=='universal_pair_shoulder_tilt_toll_v1'
    assert data['toll']=='2*sin(folded_shoulder_angle)'
    assert len(data['trees'])==len(ROOTS)
    # Independently reconstruct the hand collars of channels EN and NN.
    collars=(K/2-2-(K+V)/8,K/2+V-2-(K+V)/8,
             W-K/2-2-(W+V)/8,K/2+V-2-(W+V)/8)
    assert collars==(F(149,128),F(1877,128),F(963,32),F(337,32))
    assert min(collars)>0 and F(1,8)<K/W and F(1,8)<K/V
    counts=[];largestdepth=0;least=None;nodes=0
    for tree,(channel,a,b),printed in zip(data['trees'],ROOTS,PRINTED_LOWER_NUMERATORS):
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
        assert not todo and leaves==tree['leaves'] and len(tree['events'])==2*leaves-1==tree['nodes']
        assert depthmax==tree['maximum_depth'];largestdepth=max(largestdepth,depthmax)
        assert rowleast>=F(printed,1000000)
        counts.append({'channel':channel,'root':[str(a),str(b)],'leaves':leaves,'minimum_exact_reserve':str(rowleast)})
    return {'status':'EXACT_REPLAY_PASSED','nodes':nodes,'leaves':sum(x['leaves']for x in counts),
            'maximum_depth':largestdepth,'minimum_exact_reserve':str(least),'rows':counts,
            'analytic_collar_coefficients':[str(x)for x in collars],
            'all_printed_table_bounds_verified':True,
            'arithmetic':'64-bit directed integer dyadics; support-derived N and D, no producer import',
            'scope':'Five complete scalar inequalities for the universal original-square weighted pair shoulder-tilt toll; augmented-angle reduction is a separate hand proof.'}

def main():
    source=Path(sys.argv[1])if len(sys.argv)>1 else HERE/'universal_pair_tilt_toll_cover.json'
    blob=source.read_bytes();start=time.monotonic();report=verify(json.loads(blob))
    report.update(certificate_sha256=hashlib.sha256(blob).hexdigest(),checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-start)
    (HERE/'universal_pair_tilt_toll_replay.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
