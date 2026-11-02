"""Exact finite cone-event table for the rational limit pose of a frame family.

Only integers and Fraction are used.  This verifies the printed finite table
and its original physical pose.  The extension to all small positive parameters
is a compactness/continuity hand argument, not a numerical inference.
"""
from fractions import Fraction as F
from pathlib import Path
from itertools import combinations, product
from math import gcd
import hashlib,json

BASE=Path(__file__).resolve().parent
C=240
CENTERS=[(-360,15),(-120,15),(120,112),(360,15),(-240,-225),(0,-225),(240,-225),(-208,255),(32,352)]
QUADS=[(0,1,2,3),(0,1,5,6),(0,4,5,6),(0,7,2,3),(3,2,1,4),(3,6,5,4),(4,1,2,8),(4,1,7,8),(6,5,1,7)]

def primitive(x,y):
    g=gcd(x,y);assert g
    x,y=x//g,y//g
    return (-x,-y) if x<0 or(x==0 and y<0) else(x,y)

def dot(e,c):return e[0]*c[0]+e[1]*c[1]

def main():
    radii=[F(x*x+y*y,C*C)+F(1,2)+F(abs(x)+abs(y),C) for x,y in CENTERS]
    assert max(radii)==F(1105,256)
    margins=[F(max(abs(CENTERS[j][0]-CENTERS[i][0]),abs(CENTERS[j][1]-CENTERS[i][1])),C)-1 for i,j in combinations(range(9),2)]
    assert min(margins)==0
    events=set()
    for i,j in combinations(range(9),2):
        x=CENTERS[j][0]-CENTERS[i][0];y=CENTERS[j][1]-CENTERS[i][1]
        events|={primitive(x-y,y+x),primitive(x+y,y-x)}
    seen=set();rows=[]
    for e in sorted(events):
        f=(-e[1],e[0]);xx=[dot(e,p) for p in CENTERS];yy=[dot(f,p) for p in CENTERS]
        order=sorted(range(9),key=lambda i:xx[i]);qs=[]
        for q in combinations(order,4):
            if all(xx[j]-xx[i]>=abs(yy[j]-yy[i]) for i,j in zip(q,q[1:])):
                z=min(q,q[::-1]);seen.add(z);qs.append(QUADS.index(z)+1)
        rows.append({'normal':list(e),'quad_ids':sorted(qs)})
    assert seen==set(QUADS) and len(events)==52
    # At aligned-frame contact d=(1,s), |s|<1, an actual comparison
    # forces the positive horizontal normal; vertical contacts similarly.
    outer_pair_constraints=[]
    for q in QUADS:
        tags=[]
        for i,j in ((q[0],q[1]),(q[2],q[3])):
            dx=F(CENTERS[j][0]-CENTERS[i][0],C);dy=F(CENTERS[j][1]-CENTERS[i][1],C)
            assert max(abs(dx),abs(dy))==1
            if abs(dx)==1 and abs(dy)<1:tags.append(('horizontal',int(dx)))
            elif abs(dy)==1 and abs(dx)<1:tags.append(('vertical',int(dy)))
            else:raise AssertionError('not a unique-normal contact')
        survives=tags[0]==tags[1]
        if survives:
            n=(tags[0][1],0) if tags[0][0]=='horizontal' else (0,tags[0][1]);f=(-n[1],n[0])
            for i,j in zip(q,q[1:]):
                delta=(CENTERS[j][0]-CENTERS[i][0],CENTERS[j][1]-CENTERS[i][1])
                if dot(n,delta)<abs(dot(f,delta)):survives=False
        outer_pair_constraints.append({'quad':list(q),'outer_normals':tags,'survives_all_cone_constraints':survives})
    assert [r['quad'] for r in outer_pair_constraints if r['survives_all_cone_constraints']]==[[0,1,2,3]]
    table={'scope':'exact limit pose cone-event table; hand continuity extends the family','center_denominator':C,'centers':CENTERS,'quad_ids':[list(q) for q in QUADS],'event_rows':rows,'outer_pair_constraints':outer_pair_constraints}
    path=BASE/'limit_frame_family_table.json';path.write_text(json.dumps(table,indent=2)+'\n')
    report={'status':'PASS','arithmetic':'exact integers and Fraction','event_count':len(events),'cone_quad_count':len(seen),'only_outer_actual_cone_quad':[0,1,2,3],'only_outer_actual_normal':[1,0],
            'max_corner_norm_squared':str(max(radii)),'physical_pair_count':len(margins),'minimum_pair_margin':str(min(margins)),
            'table_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (BASE/'limit_frame_family_replay.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
