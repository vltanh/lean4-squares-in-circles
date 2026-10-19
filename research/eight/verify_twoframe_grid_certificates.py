#!/usr/bin/env python3
"""Independent exact verifier for the complete 3+5 two-frame disk exclusion.
Standard library only. Does not import the generator, NumPy, SciPy or an LP solver.
Every used inequality is reconstructed from its geometric label. Every SAT
branch is covered and every leaf is checked with rational arithmetic.
"""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import argparse,gzip,json,hashlib,time

R=F(198869,100000)
SQRT2_LO=F(707106781,500000000)
B=F(3,2)
PAIRS=tuple(combinations(range(8),2))
CELLS=tuple((x,y) for x in (-1,0,1) for y in (-1,0,1))


def need(condition,message):
    if not condition:raise ValueError(message)


def transforms(mask):
    # Independent construction using the eight signed permutation matrices.
    return {tuple(sorted((a*x+b*y,c*x+d*y) for x,y in mask))
            for a,b,c,d in ((1,0,0,1),(0,-1,1,0),(-1,0,0,-1),(0,1,-1,0),
                            (-1,0,0,1),(1,0,0,-1),(0,1,1,0),(0,-1,-1,0))}


def patterns():
    masks={tuple(m) for m in combinations(CELLS,5)}
    reps=sorted({min(transforms(m)) for m in masks})
    need(len(reps)==23,'Wrong number of grid orbits')
    need(set().union(*(transforms(m) for m in reps))==masks,'Incomplete grid cover')
    need(sum(len(transforms(m)) for m in reps)==126,'Grid orbit overlap')
    return reps


def pair_options(i,j):
    need(0<=i<j<8,'Bad pair labels')
    if j<5:axes=((1,0),(-1,0),(0,1),(0,-1))
    elif i>=5:axes=((1,1),(1,-1))
    else:axes=((1,0),(-1,0),(0,1),(0,-1),(1,1),(1,-1),(-1,1),(-1,-1))
    return tuple(('pair',i,j,a,b) for a,b in axes)


def decode(label,mask):
    """Return a necessary rational inequality A dot p <= b and pair tag or None."""
    tag=label[0];v={};selected=None
    if tag=='bound':
        _,j,s=label;need(isinstance(j,int) and 0<=j<16 and s in (-1,1),'Bad center bound')
        v[j]=F(s);rhs=B
    elif tag=='cell':
        _,i,j,s=label;need(0<=i<5 and j in (0,1) and s in (-1,1),'Bad cell bound')
        v[2*i+j]=F(s);rhs=s*F(mask[i][j])+F(1,2)
    elif tag=='sort':
        _,i=label;need(i in (5,6),'Bad minority sort')
        v={2*i:F(1),2*i+2:F(-1)};rhs=F(0)
    elif tag=='forced':
        _,i,j,ax,s=label
        need(0<=i<j<5 and ax in (0,1) and s in (-1,1),'Bad forced row')
        need(mask[i][1-ax]==mask[j][1-ax],'Forced pair does not share a source strip')
        need(s*(mask[j][ax]-mask[i][ax])>0,'Wrong forced direction')
        v={2*i+ax:F(s),2*j+ax:F(-s)};rhs=F(-1)
    elif tag=='sym-y':
        need(len(label)==1,'Bad y-symmetry label')
        need(tuple(sorted((x,-y) for x,y in mask))==mask,'Unjustified y reflection')
        v={11:F(-1)};rhs=F(0)
    elif tag=='sym-x':
        need(len(label)==1,'Bad x-symmetry label')
        need(tuple(sorted((-x,y) for x,y in mask))==mask,'Unjustified x reflection')
        v={10:F(-1),12:F(-1),14:F(-1)};rhs=F(0)
    elif tag=='disk':
        _,i,a,b=label;a,b=F(a),F(b)
        need(isinstance(i,int) and 0<=i<8 and a*a+b*b==1,'Invalid rational disk normal')
        support=(abs(a)+abs(b))/2 if i<5 else SQRT2_LO*max(abs(a),abs(b))/2
        v={2*i:a,2*i+1:b};rhs=R-support
    elif tag=='pair':
        _,i,j,a,b=label;selected=tuple(label)
        need(selected in pair_options(i,j),'Axis not part of the full true SAT disjunction')
        if j<5:width=F(1)
        elif i>=5:width=SQRT2_LO
        elif a*b==0:width=(1+SQRT2_LO)/2
        else:width=1+SQRT2_LO/2
        v={2*i:F(a),2*i+1:F(b),2*j:F(-a),2*j+1:F(-b)};rhs=-width
    else:raise ValueError('Unknown geometric inequality label')
    return {k:a for k,a in v.items() if a},rhs,selected


def verify_object(data,expected_index=None):
    reps=patterns()
    need(data.get('schema')=='n8-twoframe-grid-rational-tree-v1','Wrong schema')
    index=data['pattern_index']
    need(isinstance(index,int) and 0<=index<23,'Bad grid pattern index')
    if expected_index is not None:need(index==expected_index,'Wrong file/root association')
    mask=tuple(tuple(x) for x in data['pattern'])
    need(mask==reps[index],'Unrecognized grid representative')
    need(F(data['R'])==R and F(data['sqrt2_lower'])==SQRT2_LO,'Changed theorem constants')
    need(SQRT2_LO>0 and SQRT2_LO**2<2,'Unsound radical lower bound')
    need(R**2>F(395485389,100000000) and R<2,'Insufficient radius coverage')
    # Never trust the generator's claimed complete flag or diagnostic counts.
    labels=data['row_labels'];decoded=[decode(x,mask) for x in labels]
    nodes=data['nodes'];root=data['root']
    need(isinstance(root,int) and 0<=root<len(nodes),'Missing proof root')
    leaf_cache={};seen=set();active_nodes=set();visits=0;maxdepth=0
    def leaf(nid):
        if nid in leaf_cache:return leaf_cache[nid]
        node=nodes[nid];need(set(node)=={'weights'},'Malformed certificate leaf')
        residual={};right=F(0);support=set();positive=False;used=set()
        for k,weight in node['weights']:
            need(isinstance(k,int) and 0<=k<len(decoded),'Unknown inequality row')
            need(k not in used,'Duplicate weighted row');used.add(k)
            need(isinstance(weight,int) and weight>=0,'Nonpositive/inexact multiplier')
            if weight==0:continue
            positive=True;coeff,b,tag=decoded[k];right+=weight*b
            for j,a in coeff.items():residual[j]=residual.get(j,F(0))+weight*a
            if tag is not None:support.add(tag)
        need(positive,'Empty weighted contradiction')
        margin=right+B*sum(map(abs,residual.values()))
        need(margin<0,'Rational Farkas residual bound does not contradict the center box')
        leaf_cache[nid]=(frozenset(support),-margin)
        return leaf_cache[nid]
    def visit(nid,selected,chosen):
        nonlocal visits,maxdepth
        need(isinstance(nid,int) and 0<=nid<len(nodes),'Missing child')
        need(nid not in active_nodes,'Cyclic proof graph')
        node=nodes[nid];visits+=1;maxdepth=max(maxdepth,len(chosen));seen.add(nid)
        if 'weights' in node:
            support,margin=leaf(nid)
            need(support<=selected,'Certificate uses an unselected SAT alternative')
            return
        need(set(node)=={'pair','children'},'Malformed branch node')
        pi=node['pair'];need(isinstance(pi,int) and 0<=pi<28,'Bad branch pair')
        need(pi not in chosen,'Repeated branch pair')
        options=pair_options(*PAIRS[pi]);children=node['children']
        need(len(children)==len(options),'A true SAT alternative was omitted')
        active_nodes.add(nid)
        for child,opt in zip(children,options):visit(child,selected|{opt},chosen|{pi})
        active_nodes.remove(nid)
    visit(root,frozenset(),frozenset())
    return {'pattern':index,'verified_nodes':len(seen),'leaves':len(leaf_cache),'visits':visits,'maxdepth':maxdepth,'smallest_unscaled_margin':str(min(v[1] for v in leaf_cache.values()))}


def mutation_controls(data):
    import copy
    tests=[]
    a=copy.deepcopy(data);root=a['root']
    if 'children' in a['nodes'][root]:a['nodes'][root]['children'].pop();tests.append(a)
    a=copy.deepcopy(data);a['R']='2';tests.append(a)
    a=copy.deepcopy(data)
    # Replace every leaf multiplier by zero; no phantom positivity can pass.
    for n in a['nodes']:
        if 'weights' in n:n['weights']=[[k,0] for k,w in n['weights']]
    tests.append(a)
    for a in tests:
        try:verify_object(a)
        except (ValueError,KeyError,TypeError):pass
        else:raise ValueError('An invalid proof mutation was accepted')
    return len(tests)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory',type=Path)
    parser.add_argument('--partial',action='store_true',help='audit available roots but NEVER report full exclusion')
    parser.add_argument('--mutations',action='store_true')
    args=parser.parse_args();summary=[];start=time.time();first=None
    for k in range(23):
        f=args.directory/f'pattern_{k:02d}.json.gz'
        if args.partial and not f.exists():continue
        need(f.exists(),f'Missing root {k}; global two-frame exclusion is not verified')
        with gzip.open(f,'rt') as src:data=json.load(src)
        if first is None:first=data
        stats=verify_object(data,k);stats['sha256']=hashlib.sha256(f.read_bytes()).hexdigest();summary.append(stats)
        print(json.dumps(stats),flush=True)
    if args.mutations:print('Rejected mutation controls:',mutation_controls(first),flush=True)
    if args.partial:
        print('PARTIAL ROOT AUDIT ONLY: full two-frame exclusion is not asserted.',flush=True)
    else:
        need(len(summary)==23,'Incomplete root coverage')
        print('ALL 23 ROOTS AND ALL 126 GRID MASKS VERIFIED BY EXACT RATIONAL ARITHMETIC.',flush=True)
        print('No exact 3+5 two-frame packing fits R <= 198869/100000.',flush=True)
        print('The LOW child is excluded. HIGH and the unrestricted M5 theorem remain open.',flush=True)
    output={'complete':not args.partial and len(summary)==23,'roots':summary,'elapsed':time.time()-start}
    (args.directory/'independent_verification.json').write_text(json.dumps(output,indent=2))

if __name__=='__main__':main()
