#!/usr/bin/env python3
"""Replay the rational seven-square low-floor control from exact coordinates."""
from fractions import Fraction as F
from itertools import combinations,product
from pathlib import Path
import hashlib,json
BASE=Path(__file__).parent

def dot(a,b):return sum(x*y for x,y in zip(a,b))
def main():
    src=BASE/'selected_seven_01011_exact_control.json';raw=src.read_bytes();data=json.loads(raw)
    centers=[tuple(map(F,r)) for r in data['centers']];first=[tuple(map(F,r)) for r in data['first_axes']]
    assert len(centers)==len(first)==7
    axes=[];widths=[];corner_reserves=[]
    for c,u in zip(centers,first):
        assert dot(u,u)==1;v=(-u[1],u[0]);axes.append((u,v));widths.append((abs(u[0])+abs(u[1]))/2)
        norms=[sum((c[j]+(s*u[j]+t*v[j])/2)**2 for j in range(2)) for s,t in product((-1,1),repeat=2)]
        margin=F(1105,256)-max(norms);assert margin>0;corner_reserves.append(margin)
    pair_reserves=[]
    for i,j in combinations(range(7),2):
        d=tuple(centers[j][k]-centers[i][k] for k in range(2))
        reserves=[abs(dot(d,n))-sum(abs(dot(n,w)) for z in (i,j) for w in axes[z])/2 for owner in (i,j) for n in axes[owner]]
        assert max(reserves)>0;pair_reserves.append(max(reserves))
    edges=[]
    for (i,j),bit in zip([(0,1),(1,2),(2,3),(4,5),(5,6)],'01011'):
        dx,dy=(centers[j][k]-centers[i][k] for k in range(2));w=widths[i]+widths[j]
        assert dx>=abs(dy)
        assert dx<w if bit=='1' else dx>=w
        edges.append({'i':i,'j':j,'bit':bit,'dx':str(dx),'abs_dy':str(abs(dy)),'width_sum':str(w)})
    excess=widths[1]-F(31,60);floor=centers[5][1]-widths[5]
    assert excess==F(239,72060) and floor<F(1,10)
    result={'status':'EXACT_REPLAY_PASSED','scope':'seven original physical units only; counterexample to importing hM<31/60, not to the nine-square theorem','physical_pairs':21,'corners':28,'minimum_corner_reserve':str(min(corner_reserves)),'minimum_pair_reserve':str(min(pair_reserves)),'inner_width_excess':str(excess),'P_whole_floor':str(floor),'selected_edges':edges,'source_sha256':hashlib.sha256(raw).hexdigest()}
    (BASE/'selected_seven_01011_exact_control_replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
