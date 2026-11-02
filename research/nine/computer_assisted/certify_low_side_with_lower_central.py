#!/usr/bin/env python3
"""Discovery: complete outward-integer cover of the low-side/lower-central system.

The physical reduction and independent replay are separate artifacts.  No
floating result, producer-claimed bound or incomplete frontier is proof evidence.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import itertools
import json
import time
from ownhalf_interval_kernel import I, SCALE, frame, mn, mx

ROOT = ((F(0), F(1)), (F(0), F(1)), (F(0), F(1129,3000)),
        (F(7,10), F(13,12)), (F(1,2), F(57,100)))
Q = F(1105,256)
DELTA = F(331,20000)
J = F(29927,30000)


def expressions(box, signs):
    tp, tr, x, X, h = (I(*pair) for pair in box)
    sp, sr = signs
    ap, bp, p, kp = frame(tp)
    ar, br, r, kr = frame(tr)
    g = 1/(4*h)
    eta = h+g-1
    toll = mx(2*br, 6*br-F(27,2)*(1-ar))
    AL = mx(I(F(59,60)), F(157,184)+F(27,92)*(X-r)+toll/46)+eta
    AR = F(59,60)+eta

    width_difference = (p-h).abs()
    loose, coupled = [], []
    for z in (F(29,60), F(121,200)):
        d2 = x+z
        for w in (g-DELTA, 1+DELTA-h):
            d1 = (z-w).abs()
            first = (1-d1.sq()).sqrt() + ((1+width_difference).sq()-d2.sq()).sqrt()
            second = ((1+width_difference).sq()-d1.sq()).sqrt() + (1-d2.sq()).sqrt()
            loose.extend((first,second))
            coupled.extend((w+first,w+second))
    adjusted = mn(AL, I(F(61,60)))
    endpoint_cone = adjusted+(I(Q)-(adjusted+J).sq()).sqrt()
    lowerP = mx(-F(61,60)+mn(*loose), mn(*coupled)-endpoint_cone)
    own_clearance = F(25,57)+mn(p, (F(1,2)+(x-DELTA)*bp)/ap,
                                  (F(1,2)+(x-DELTA)*ap)/mx(bp,I(F(1,40))))
    lowerP = mx(lowerP, -F(61,60)+mx(I(F(909,1000)),own_clearance))

    if sp > 0:
        upperP = mn(p+F(1,10),(I(Q)-(x+kp).sq()).sqrt()-p,
                               (I(Q)-(x+p).sq()).sqrt()+kp)
    else:
        upperP = mn(p+F(1,10),(I(Q)-(x+p).sq()).sqrt()-kp,
                               (I(Q)-(x-kp).sq()).sqrt()-p)
    endpoint_margin = mx(F(4421,12000)+F(32,9)*eta,
                         1-(I(Q)-(mn(AR,I(F(61,60)))+J).sq()).sqrt())
    q = F(503,480)-X
    loss = mx(I(0), tr*(kr+q)) if sr>0 else mx(I(0),(q-kr)/mx(tr,I(F(1,4))))
    lowerR = mx(I(F(3,5)),endpoint_margin+r-loss)
    if sr > 0:
        upperR = mn((I(Q)-(X+kr).sq()).sqrt()-r,
                    (I(Q)-(X+r).sq()).sqrt()+kr)
    else:
        upperR = mn((I(Q)-(X+r).sq()).sqrt()-kr,
                    (I(Q)-(X-kr).sq()).sqrt()-r)

    D = X-x
    # Finite interval contractions retain the same original two heights.
    lowerP = mx(lowerP,lowerR-D)
    upperP = mn(upperP,upperR+D)
    lowerR = mx(lowerR,lowerP-D)
    upperR = mn(upperR,upperP+D)
    lo = mx(lowerR-upperP,-D)
    hi = mn(upperR-lowerP,D)
    support = (1+(ap*ar+sp*sr*bp*br).abs()+(sr*ap*br-sp*bp*ar).abs())/2
    axes = ((ap,sp*bp),(-sp*bp,ap),(ar,sr*br),(-sr*br,ar))
    projection = mx(*((a*D+b*y).abs() for a,b in axes for y in (lo,hi)))
    return (upperP-lowerP, upperR-lowerR, F(1,30)-eta,
            F(61,60)-AL, F(61,60)-AR,
            r+F(451,810)-X-F(92,27)*eta-F(2,27)*toll,
            hi-lo, D-F(707,1000), p+r-D, D-1/(4*p)-1/(4*r),
            projection-support, D.sq()+mx(lo.sq(),hi.sq())-support.sq())


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--max-nodes',type=int,default=2000000)
    parser.add_argument('--output',default='low_side_with_lower_central_cover.json')
    args=parser.parse_args()
    started=time.monotonic()
    signs=list(itertools.product((-1,1),repeat=2))
    nodes=[{} for _ in signs]
    todo=[(i,ROOT,s,0)for i,s in reversed(list(enumerate(signs)))]
    counts=[0]*12; maximum_depth=0; seen=0
    while todo:
        index,box,s,depth=todo.pop()
        maximum_depth=max(maximum_depth,depth)
        vals=expressions(box,s)
        rule=min(range(len(vals)),key=lambda j:vals[j].hi)
        if vals[rule].hi < -SCALE//10000000:
            nodes[index]={'rule':rule,'upper':str(F(vals[rule].hi,SCALE))}
            counts[rule]+=1
        else:
            if depth>=70 or len(nodes)+2>args.max_nodes:
                todo.append((index,box,s,depth));break
            axis=max(range(5),key=lambda j:(box[j][1]-box[j][0])/(ROOT[j][1]-ROOT[j][0]))
            lo,hi=box[axis];mid=(lo+hi)/2
            left,right=list(box),list(box);left[axis]=(lo,mid);right[axis]=(mid,hi)
            children=[len(nodes),len(nodes)+1]
            nodes[index]={'axis':axis,'children':children}
            nodes.extend(({},{}))
            todo.extend(((children[1],tuple(right),s,depth+1),(children[0],tuple(left),s,depth+1)))
        seen+=1
        if seen%20000==0:
            print('visited',seen,'leaves',sum(counts),'remaining',len(todo),'seconds',round(time.monotonic()-started,2),flush=True)
    output={'schema':'low_side_with_lower_central_v1',
            'status':'COMPLETE_PENDING_INDEPENDENT_REPLAY' if not todo else 'INCOMPLETE_DISCOVERY_ONLY',
            'root':[[str(a),str(b)]for a,b in ROOT],
            'roots':[{'index':i,'signs':list(s)}for i,s in enumerate(signs)],
            'nodes':nodes,'counts':counts,'leaves':sum(counts),'maximum_depth':maximum_depth,
            'remaining':len(todo),
            'pending':[{'index':i,'box':[[str(a),str(b)]for a,b in bx],'signs':list(s),'depth':d}for i,bx,s,d in todo],
            'seconds':time.monotonic()-started}
    Path(args.output).write_text(json.dumps(output,separators=(',',':'))+'\n')
    print(output['status'],len(nodes),'nodes',sum(counts),'leaves','depth',maximum_depth,'pending',len(todo),'seconds',round(time.monotonic()-started,2),flush=True)

if __name__=='__main__':
    main()
