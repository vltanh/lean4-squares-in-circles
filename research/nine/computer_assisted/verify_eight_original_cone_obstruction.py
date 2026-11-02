#!/usr/bin/env python3
"""Exact eight-original obstruction to a seven/eight-unit 100/00 terminal.

This is not a nine-unit counterexample and does not close a mask.
"""
from fractions import Fraction as F
import json
from pathlib import Path

Q=F(1105,256)
U=(F(99,101),-F(20,101)); V=(F(20,101),F(99,101))
ALIGN=((F(1),F(0)),(F(0),F(1)))
SQUARES=[
 ('A',(-F(73,50),F(17,50)),(U,V)),
 ('B',(-F(61,100),F(1,10)+F(110,101)),(U,V)),
 ('C',(F(4839,10100),F(1,10)),ALIGN),
 ('D',(F(14939,10100),F(1,10)),ALIGN),
 ('L',(-F(1),-F(9,10)),ALIGN),
 ('M',(F(0),-F(9,10)),ALIGN),
 ('R',(F(1),-F(9,10)),ALIGN),
 ('F',(F(3,5),F(6,5)),ALIGN),
]
dot=lambda a,b:sum(x*y for x,y in zip(a,b))
def support(frame,n):return sum(abs(dot(a,n)) for a in frame)/2

def main():
    corners=[]; pairs=[];chains=[]
    for name,c,frame in SQUARES:
        assert dot(frame[0],frame[0])==dot(frame[1],frame[1])==1
        assert dot(frame[0],frame[1])==0
        norms=[]
        for a in [-1,1]:
            for b in [-1,1]:
                p=tuple(c[k]+(a*frame[0][k]+b*frame[1][k])/2 for k in range(2))
                norms.append(dot(p,p))
        reserve=Q-max(norms);assert reserve>0
        corners.append({'name':name,'maximum_squared_corner':str(max(norms)),'reserve':str(reserve)})
    for i,(ni,ci,fi) in enumerate(SQUARES):
        for nj,cj,fj in SQUARES[i+1:]:
            d=tuple(cj[k]-ci[k] for k in range(2))
            reserves=[abs(dot(d,n))-support(fi,n)-support(fj,n) for n in fi+fj]
            reserve=max(reserves);assert reserve>=0
            pairs.append({'pair':ni+nj,'separator_reserve':str(reserve)})
    for i,j,weak in [(0,1,True),(1,2,False),(2,3,False),(4,5,False),(5,6,False)]:
        ni,ci,fi=SQUARES[i];nj,cj,fj=SQUARES[j]
        dx,dy=(cj[k]-ci[k] for k in range(2))
        actual=dx-support(fi,(1,0))-support(fj,(1,0))
        assert dx>=abs(dy)
        assert actual<0 if weak else actual>=0
        chains.append({'edge':ni+nj,'weak':weak,'cone_reserve':str(dx-abs(dy)),'actual_reserve':str(actual)})
    report={'status':'PASS','scope':'Eight original physical units in strict Q; not a nine-unit counterexample',
            'mask':'100/00; reverse both chains and x for 001/00','corners':corners,'pairs':pairs,'chains':chains}
    target=Path(__file__).with_name('eight_original_cone_obstruction_replay.json')
    target.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'PASS','original_units':len(SQUARES),'corners':32,'pairs':len(pairs),
                      'minimum_corner_reserve':str(min(F(x['reserve']) for x in corners)),'chains':chains},indent=2))

if __name__=='__main__':main()
