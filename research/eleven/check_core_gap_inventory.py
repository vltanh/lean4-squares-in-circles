"""Independent multiset replay of the coarse radial gap inventories."""
from itertools import combinations_with_replacement
from pathlib import Path
from math import comb
import json

ROOT=Path(__file__).resolve().parent

def require(test,message):
    if not test:raise RuntimeError(message)

def orbit(word):
    n=len(word)
    return {tuple(word[(offset+sign*i)%n] for i in range(n))
            for offset in range(n) for sign in (-1,1)}

def words(total,length):
    answer=set()
    for positions in combinations_with_replacement(range(length),total):
        word=tuple(positions.count(i) for i in range(length))
        answer.add(word)
    require(len(answer)==comb(total+length-1,length-1),'raw multiset count')
    return answer

def main():
    data=json.loads((ROOT/'CORE_GAP_COUNTS.json').read_text())
    require(data['schema']=='radial-core-gap-counts-v1','gap schema')
    require(len(data['rows'])==2,'two radial rows')
    for item,(core,ring,expected) in zip(data['rows'],[(3,8,16),(4,7,33)]):
        require((item['core'],item['ring'],item['count'])==(core,ring,expected),'row metadata')
        recovered=[]
        for length in range(1,core+1):
            recovered.extend(sorted({min(orbit(w)) for w in words(ring,length)}))
        require(len(recovered)==expected,'dihedral count')
        require([list(w) for w in recovered]==item['cases'],'complete serialized cases')
        print('PASS core/ring',core,ring,'gap rows',expected)
    data=json.loads((ROOT/'THREE_CORE_INTERLEAVINGS.json').read_text())
    require(data['schema']=='three-core-eight-ring-interleavings-v1','interleaving schema')
    raw=set().union(*(words(total,8) for total in range(4)))
    representatives=sorted({min(orbit(w)) for w in raw},key=lambda w:(sum(w),w))
    require(len(raw)==165 and len(representatives)==17,'interleaving counts')
    recovered=[{'word':list(w),'active_cores':sum(w),'inactive_cores':3-sum(w),
                'orbit_size':len(orbit(w))} for w in representatives]
    require(data['raw_count']==165 and data['orbit_count']==17 and data['rows']==recovered,
            'complete interleaving inventory')
    require(sum(row['orbit_size'] for row in recovered)==165,'orbit exhaustion')
    print('PASS three-core interleavings: 165 words, 17 dihedral rows')
    print('All rows retain their continuous poses and original physical constraints.')

if __name__=='__main__':main()
