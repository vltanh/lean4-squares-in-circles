from itertools import combinations, product
from pathlib import Path
from collections import Counter
import argparse, hashlib, json, time

ROOT=Path(__file__).resolve().parent
COST=(0,0,1,2,1,2,4)
MULT=(0,1,1,2,1,1,2)

def setup(k):
    pairs=list(combinations(range(k+1),2))
    index={p:i for i,p in enumerate(pairs)}
    sym=[]
    for reverse in (False,True):
        for start in range(k):
            p=[(start-i if reverse else start+i)%k for i in range(k)]+[k]
            sym.append([index[tuple(sorted((p[a],p[b])))] for a,b in pairs])
    return pairs,sym

def necessary(k,pairs,code):
    if k+1+sum(COST[t] for t in code)>10:return False
    degrees=[0]*(k+1); adjacency=[set() for _ in degrees]
    loaded_edges=[];u_types=[];u_neighbors=[];ldirect=0
    for (a,b),t in zip(pairs,code):
        if not t:continue
        degrees[a]+=MULT[t];degrees[b]+=MULT[t]
        adjacency[a].add(b);adjacency[b].add(a)
        if b==k:u_types.append(t);u_neighbors.append(a)
        else:
            loaded_edges.append((a,b))
            if t==1:
                ldirect+=1
                if k==2 or not (b-a==1 or (a,b)==(0,k-1)):return False
    if sum(degrees)<2*(k+1) or max(degrees)>8 or degrees[k]<3:return False
    if k==3 and ldirect>1:return False
    if len(u_types)<3 and sorted(u_types)!=[1,3]:return False
    for i,(a,b) in enumerate(loaded_edges):
        for c,d in loaded_edges[:i]:
            if a<c<b<d or c<a<d<b:return False
        inside=any(a<x<b for x in u_neighbors)
        outside=any(x<a or x>b for x in u_neighbors)
        if inside and outside:return False
    reached={0};frontier=[0]
    while frontier:
        u=frontier.pop()
        for v in adjacency[u]-reached:reached.add(v);frontier.append(v)
    return len(reached)==k+1

def canonical(code,sym):
    return min(tuple(code[i] for i in p) for p in sym)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--bruteforce',type=int,nargs='*',default=[2,3]);parser.add_argument('--verify',type=int,nargs='*',default=list(range(2,8)))
    parser.add_argument('--case', help='Decode a code-based stable ID without requiring catalog files')
    parser.add_argument('--catalog-dir', type=Path, default=ROOT)
    parser.add_argument('--manifest', type=Path, default=ROOT/'branching_one_unloaded_inventory.json')
    args=parser.parse_args()
    if args.case:
        parts=args.case.split('-')
        if len(parts)!=4 or parts[:2]!=['C05','B1'] or not parts[2].startswith('K'):
            parser.error('Case ID must have the form C05-B1-Kkk-code')
        try:
            k=int(parts[2][1:]); code=tuple(map(int,parts[3]))
        except ValueError:
            parser.error('Case ID contains a noninteger field')
        if not 2<=k<=7:parser.error('Loaded count must lie in 2,...,7')
        pairs,sym=setup(k)
        if len(code)!=len(pairs) or any(t not in range(7) for t in code):
            parser.error('Code has the wrong length or symbols')
        if not necessary(k,pairs,code) or canonical(code,sym)!=code:
            parser.error('Code is not a canonical record in the stated raw catalog')
        names=('absent','direct','S','double-S','D','SS','double-SS')
        print(json.dumps({'id':f'C05-B1-K{k:02d}-{parts[3]}','loaded_vertices':k,
                          'unloaded_retained_vertex':k,
                          'total_bodies':k+1+sum(COST[t] for t in code),
                          'edges':[{'endpoints':[a,b],'type':names[t]} for (a,b),t in zip(pairs,code) if t]},indent=2))
        return
    inventory=json.loads(args.manifest.read_text())
    metadata={r['loaded_vertices']:r for r in inventory['strata']}
    if len(inventory['strata'])!=6 or set(metadata)!=set(range(2,8)):
        raise ValueError('Manifest must contain exactly one stratum for each k=2,...,7')
    for k in sorted(set(args.verify)|set(args.bruteforce)):
        start=time.monotonic();pairs,sym=setup(k)
        raw=(args.catalog_dir/f'b1_k{k}.txt').read_text().splitlines()
        assert raw==sorted(set(raw))
        actual={tuple(map(int,c)) for c in raw}
        data=(args.catalog_dir/f'b1_k{k}.txt').read_bytes()
        counts=Counter(k+1+sum(COST[t] for t in code) for code in actual)
        row=metadata[k]
        if (len(actual)!=row['canonical_count'] or len(data)!=row['catalog_bytes']
                or hashlib.sha256(data).hexdigest()!=row['catalog_sha256']
                or {str(m):n for m,n in counts.items()}!=row['canonical_counts_by_total_bodies']):
            raise ValueError(f'Manifest differs from generated catalog at k={k}')
        if k in args.verify:
            for code in actual:
                assert len(code)==len(pairs) and all(0<=t<7 for t in code)
                assert necessary(k,pairs,code),(k,code)
                assert canonical(code,sym)==code,(k,code)
            print(f'PASS all {len(actual)} k={k} records satisfy predicates and canonicality',flush=True)
        if k in args.bruteforce:
            expected=set();labelled=0
            for code in product(range(7),repeat=len(pairs)):
                if necessary(k,pairs,code):expected.add(canonical(code,sym));labelled+=1
            assert actual==expected,(k,len(actual),len(expected),actual^expected)
            print(f'PASS exhaustive independent Cartesian product k={k}: {labelled} labeled; exact {len(expected)} canonical codes',flush=True)
        print(f'k={k} elapsed={time.monotonic()-start:.2f}s',flush=True)
if __name__=='__main__':main()
