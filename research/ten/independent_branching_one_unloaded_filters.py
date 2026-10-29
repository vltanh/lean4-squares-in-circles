"""Independently verify the b=1 filter ledger by cuts, union-find and integer Floyd.

No primary classifier is used to make decisions. --compare-decoder also
checks its status on every code after making the independent decision.
"""
from pathlib import Path
from itertools import combinations
from functools import lru_cache
from collections import Counter
import argparse,hashlib,json,time
ROOT=Path(__file__).resolve().parent

@lru_cache(None)
def angle_rejected(k,llcode):
    # Angles are in 18-degree units. Every source inequality is strict.
    d=[[1000000]*k for _ in range(k)]
    for i in range(k):d[i][i]=0
    def edge(u,v,b): d[u][v]=min(d[u][v],(k+1)*b-1)
    for i in range(k-1):edge(i+1,i,-2)
    edge(0,k-1,18)
    for (u,v),t in zip(combinations(range(k),2),llcode):
        if t==1:
            if v==u+1:edge(u,v,4)
            else:
                assert(u,v)==(0,k-1)
                edge(v,u,-16)
        elif t>=2:
            lower=6 if t==4 else 9 if t in(5,6) else 5
            edge(v,u,-lower);edge(u,v,20-lower)
    for p in range(k):
        for u in range(k):
            up=d[u][p]
            for v in range(k):
                value=up+d[p][v]
                if value<d[u][v]:d[u][v]=value
        if any(d[i][i]<0 for i in range(k)):return True
    return False

def prepare(k):
    n=k+1;pairs=list(combinations(range(n),2));ll=[i for i,(u,v) in enumerate(pairs) if v<k]
    cuts=[]
    for mask in range(1,(1<<n)-1,2):
        crossed=0
        for i,(u,v) in enumerate(pairs):
            if bool(mask&(1<<u))!=bool(mask&(1<<v)):crossed|=1<<i
        cuts.append(crossed)
    return pairs,ll,cuts

def filters(k,pairs,ll,cuts,code):
    present=0;forbidden=0;ssmask=0;double_vertices=0
    ds=[]
    for i,((u,v),t) in enumerate(zip(pairs,code)):
        if t:present|=1<<i
        if t in(3,6):double_vertices|=(1<<u)|(1<<v)
        if t==4:ds.append((u,v))
        if v<k:
            if t in(1,2,4):forbidden|=1<<i
            if t==5:ssmask|=1<<i
    incident_ss=0
    for i,(u,v) in enumerate(pairs):
        if ssmask&(1<<i) and double_vertices&((1<<u)|(1<<v)):incident_ss|=1<<i
    forbidden_bridge=False;ss_bundle_bridge=False
    for cut in cuts:
        crossing=cut&present
        if crossing and not(crossing&(crossing-1)):
            if crossing&forbidden:forbidden_bridge=True
            if crossing&incident_ss:ss_bundle_bridge=True
    parent=list(range(k+1));degree=[0]*(k+1);d_forest=False
    def find(v):
        while parent[v]!=v:v=parent[v]
        return v
    for u,v in ds:
        degree[u]+=1;degree[v]+=1
        if degree[u]>2 or degree[v]>2:d_forest=True
        a,b=find(u),find(v)
        if a==b:d_forest=True
        else:parent[a]=b
    angle=angle_rejected(k,tuple(code[i] for i in ll))
    return forbidden_bridge,ss_bundle_bridge,d_forest,angle

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--catalog-dir',type=Path,required=True)
    parser.add_argument('--compare-decoder',action='store_true')
    args=parser.parse_args()
    if args.compare_decoder:
        from check_branching_one_unloaded_filters import first_witness
    manifest=json.loads((ROOT/'branching_one_unloaded_inventory.json').read_text())
    progress=json.loads((ROOT/'branching_one_unloaded_progress.json').read_text())
    metadata={r['loaded_vertices']:r for r in manifest['strata']}
    printed={r['loaded_vertices']:r for r in progress['by_loaded_count']}
    if (len(metadata)!=6 or len(printed)!=6 or set(metadata)!=set(range(2,8))
            or set(printed)!=set(range(2,8))):
        raise ValueError('Manifest and progress must cover exactly k=2,...,7')
    names=('two_loaded','loaded_bridge','ss_bundle','d_forest','loaded_angle')
    totals=Counter();all_kinds=Counter({name:0 for name in names})
    for k in range(2,8):
        started=time.monotonic();pairs,ll,cuts=prepare(k)
        data=(args.catalog_dir/f'b1_k{k}.txt').read_bytes()
        if (len(data)!=metadata[k]['catalog_bytes']
                or hashlib.sha256(data).hexdigest()!=metadata[k]['catalog_sha256']):
            raise ValueError(f'Raw catalog differs at k={k}')
        codes=data.decode().splitlines();counts=Counter()
        for raw in codes:
            code=tuple(map(int,raw))
            bits=(k==2,)+filters(k,pairs,ll,cuts,code)
            kind=next((name for name,yes in zip(names,bits) if yes),None)
            counts[kind or 'open']+=1
            if args.compare_decoder:
                witness=first_witness(k,raw)
                primary_kind=witness['kind'] if witness else None
                if kind!=primary_kind:
                    raise ValueError(f'Decoder differs from independent predicates: k={k}, code={raw}')
        row={'loaded_vertices':k,'raw_cases':len(codes),
             'hand_closed':len(codes)-counts['open'],'remaining':counts['open'],
             'closed_by_first_witness':{name:counts[name] for name in names if counts[name]}}
        if row!=printed[k]:raise ValueError(f'Printed progress differs at k={k}')
        totals.update({name:row[name] for name in ('raw_cases','hand_closed','remaining')})
        all_kinds.update({name:counts[name] for name in names})
        print(f"PASS independent k={k}: {row['hand_closed']} excluded, {row['remaining']} remain; "
              f"{time.monotonic()-started:.2f}s",flush=True)
    if (any(progress[name]!=value for name,value in totals.items())
            or dict(all_kinds)!=progress['closed_by_first_witness']):
        raise ValueError('Printed global progress differs')
    print(f"PASS independent total: {totals['hand_closed']}/{totals['raw_cases']} excluded; "
          f"{totals['remaining']} remain")
