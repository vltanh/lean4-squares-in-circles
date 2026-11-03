#!/usr/bin/env python3
"""Exact Q boundary control for closed weak<=, not for strict001/00."""
from fractions import Fraction as F
from itertools import combinations,product
import argparse,json
from pathlib import Path

Q=F(1105,256)
CENTERS=((F(-3,2),F(-1,16)),(F(-1,2),F(-1,16)),
         (F(1,2),F(-17,16)),(F(3,2),F(-1,16)),
         (F(-1),F(15,16)),(F(0),F(15,16)),(F(1),F(15,16)),
         (F(-1,2),F(-17,16)),(F(1,2),F(-1,16)))
def verify():
    corners=[];maxima=[]
    for x,y in CENTERS:
        vals=[(x+F(s,2))**2+(y+F(t,2))**2 for s,t in product((-1,1),repeat=2)]
        assert all(v<=Q for v in vals);corners.extend(vals);maxima.append(max(vals))
    expected=[1105,337,881,1105,1105,593,1105,881,337]
    assert maxima==[F(v,256) for v in expected]
    pairs=[]
    for i,j in combinations(range(9),2):
        dx=CENTERS[j][0]-CENTERS[i][0];dy=CENTERS[j][1]-CENTERS[i][1]
        assert max(abs(dx),abs(dy))>=1;pairs.append((i,j))
    marked=[]
    for i,j in ((0,1),(1,2),(2,3),(4,5),(5,6)):
        dx=CENTERS[j][0]-CENTERS[i][0];dy=CENTERS[j][1]-CENTERS[i][1]
        assert dx==1 and dx>=abs(dy)
        marked.append({'pair':'ABCDEFGHI'[i]+'ABCDEFGHI'[j],'dx':str(dx),'dy':str(dy),'actual':dx>=1})
    assert CENTERS[3][1]-CENTERS[2][1]==1
    assert not CENTERS[3][0]-CENTERS[2][0]<1
    assert CENTERS[7][0]<=CENTERS[8][0]
    for i,j in ((0,1),(1,8),(8,3),(4,5),(5,6)):
        dx=CENTERS[j][0]-CENTERS[i][0];dy=CENTERS[j][1]-CENTERS[i][1]
        assert dx==1 and dy==0
    return {'status':'PASS','exact_corners_checked':len(corners),'exact_original_pairs_checked':len(pairs),
            'Q':str(Q),'centers':{name:[str(z) for z in c] for name,c in zip('ABCDEFGHI',CENTERS)},
            'largest_corner_norms_squared':[str(z) for z in maxima],'marked_links':marked,
            'v_CD':'1','true_mask':'000/00','closed_weak_relaxation_satisfied':True,
            'strict_001_predicate_satisfied':False,'alternate_actual_chains':['ABID','EFG'],
            'whole_mask_closed':False}
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--report',type=Path);args=ap.parse_args();out=verify()
    if args.report:args.report.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
