"""Independent enumeration: all loaded-loaded pairs first, then U incidence."""
from check_branching_one_unloaded import *

def enumerate_k(k):
    pairs,sym=setup(k)
    ll=[e for e,(a,b) in enumerate(pairs) if b<k]
    uu=[e for e,(a,b) in enumerate(pairs) if b==k]
    sequence=ll+uu
    code=[0]*len(pairs);degree=[0]*(k+1)
    result=set();labeled=0
    budget=9-k
    def rec(pos,spent,direct):
        nonlocal labeled
        if pos==len(sequence):
            if necessary(k,pairs,code):
                labeled+=1;result.add(canonical(code,sym))
            return
        e=sequence[pos];a,b=pairs[e]
        for typ in range(7):
            c,d=COST[typ],MULT[typ]
            if spent+c>budget or degree[a]+d>8 or degree[b]+d>8:continue
            if b<k and typ:
                if typ==1 and (k==2 or not(b==a+1 or(a,b)==(0,k-1)) or(k==3 and direct==1)):continue
                if any(code[f] and (a<x<b<y or x<a<y<b) for f in ll[:pos] for x,y in [pairs[f]]):continue
            code[e]=typ;degree[a]+=d;degree[b]+=d
            rec(pos+1,spent+c,direct+int(b<k and typ==1))
            degree[a]-=d;degree[b]-=d
        code[e]=0
    rec(0,0,0)
    return result,labeled

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--k',type=int,nargs='+',default=list(range(2,8)))
    parser.add_argument('--catalog-dir',type=Path,default=ROOT)
    parser.add_argument('--manifest',type=Path,default=ROOT/'branching_one_unloaded_inventory.json')
    args=parser.parse_args()
    metadata={row['loaded_vertices']:row for row in json.loads(args.manifest.read_text())['strata']}
    for k in args.k:
        if k not in range(2,8):parser.error('k must lie in 2,...,7')
        start=time.monotonic();expected,labelled=enumerate_k(k)
        actual={tuple(map(int,c)) for c in (args.catalog_dir/f'b1_k{k}.txt').read_text().splitlines()}
        assert expected==actual,(k,len(expected),len(actual),expected^actual)
        assert labelled==metadata[k]['labeled_count'],(k,labelled,metadata[k]['labeled_count'])
        print(f'PASS independent LL-first k={k}: {labelled} labeled; exact {len(expected)} canonical codes; {time.monotonic()-start:.2f}s',flush=True)
