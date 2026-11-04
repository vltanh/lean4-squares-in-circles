#!/usr/bin/env python3
"""Independent exact integer replay of the all-angle AHID scalar cover.

No numerical modules or discovery code are imported. The checker reconstructs
all polynomial coefficients from the displayed physical rational expression,
checks every dyadic Bernstein box, and checks the entire closed parent union.
The continuous physical interpretation still requires the hand manuscript.
"""
from fractions import Fraction
from itertools import product
from math import comb
from pathlib import Path
import argparse
import hashlib
import json
import time

if not __debug__:
    raise RuntimeError("Exact replay requires assertions; Python -O is not supported")

F=Fraction
ROOT=F(5,12)
CERT_VARIATION=F(231,1000)
TARGET_VARIATION=F(23,100)
SCALE=46000
SHAPE=(5,)*4
SIZE=625
ZERO=(0,0,0,0)
EXPONENTS=tuple(product(range(5),repeat=4))
INDEX={e:i for i,e in enumerate(EXPONENTS)}
BINOM4=(1,4,6,4,1)


def add_to(target, terms, multiplier=1):
    for exponent,value in terms.items():
        target[exponent]=target.get(exponent,0)+multiplier*value


def multiply_univariate(terms, variable, coefficients):
    result={}
    for exponent,value in terms.items():
        for degree,coefficient in enumerate(coefficients):
            if coefficient:
                new=list(exponent);new[variable]+=degree
                assert new[variable]<=4
                key=tuple(new)
                result[key]=result.get(key,0)+value*coefficient
    return result


def complement(numerator, factors):
    result=dict(numerator)
    for variable,coefficients in factors:
        result=multiply_univariate(result,variable,coefficients)
    return result


def exponents(i,di,j=None,dj=0):
    e=[0,0,0,0];e[i]=di
    if j is not None:e[j]=dj
    return tuple(e)


def reconstruct_features(signs, owners, selected_owner):
    """P0 + epsilon_0 P1 + ... + tau_A P4 + tau_D P5.

    Each feature is SCALE times the rational scalar multiplied by
    D=product_i(1-x_i^4). All listed coefficients are integers.
    """
    assert signs[0]==1 and signs[3]==-1 and all(s in(-1,1)for s in signs)
    assert len(owners)==3 and all(o in(j,j+1)for j,o in enumerate(owners))
    assert selected_owner in owners
    features=[{}for _ in range(6)]
    full=complement({ZERO:1},[(i,(1,0,0,0,-1))for i in range(4)])
    add_to(features[0],full,-2*SCALE)
    for j,owner in enumerate(owners):
        i=j;right=j+1;other=right if owner==i else i
        # Explicit expansion of (1+s_i s_j x_i x_j)^2.
        base={ZERO:1,exponents(i,1,right,1):2*signs[i]*signs[right],
              exponents(i,2,right,2):1}
        # Explicit expansion of (1+s_i s_j x_i x_j)(s_i x_i-s_j x_j).
        absolute={exponents(i,1):signs[i],exponents(right,1):-signs[right],
                  exponents(i,2,right,1):signs[right],
                  exponents(i,1,right,2):-signs[i]}
        factors=[]
        for variable in range(4):
            if variable==owner:factor=(1,0,1)
            elif variable==other:factor=(1,0,-1)
            else:factor=(1,0,0,0,-1)
            factors.append((variable,factor))
        add_to(features[0],complement(base,factors),SCALE)
        add_to(features[j+1],complement(absolute,factors),SCALE)
    for endpoint,feature_index in ((0,4),(3,5)):
        factors=[(i,(1,0,-1)if i==endpoint else(1,0,0,0,-1))for i in range(4)]
        # 2 beta/23 - h = (-23 -38x +23x^2)/(46(1+x^2)).
        high={ZERO:-23,exponents(endpoint,1):-38,exponents(endpoint,2):23}
        # sharp toll minus four-beta toll = x(143-943x)/(368(1+x^2)).
        change={exponents(endpoint,1):143,exponents(endpoint,2):-943}
        add_to(features[0],complement(high,factors),SCALE//46)
        add_to(features[feature_index],complement(change,factors),SCALE//368)
    factors=[(i,(1,0,1)if i==selected_owner else(1,0,0,0,-1))for i in range(4)]
    loss=2*CERT_VARIATION*SCALE
    assert loss.denominator==1
    add_to(features[0],complement({exponents(selected_owner,1):1},factors),-int(loss))
    return [[p.get(e,0)for e in EXPONENTS]for p in features]


def transform_matrix(address):
    """Integer Bernstein transform multiplied by 12*denominator^4.

    On x in [5n/(12*2^d),5(n+1)/(12*2^d)], coefficient x^r is
    sum_m binom(r,m)l^(r-m)(u-l)^m binom(j,m)/binom(4,m).
    """
    n,d=address
    assert type(n)is int and type(d)is int and 0<=n<2**d and d>=0
    lo=5*n;step=5;den=12*2**d
    matrix=[]
    for j in range(5):
        row=[]
        for r in range(5):
            value=0
            for m in range(min(j,r)+1):
                value+=comb(r,m)*lo**(r-m)*step**m*den**(4-r)*comb(j,m)*(12//BINOM4[m])
            row.append(value)
        matrix.append(row)
    return matrix,12*den**4


def bernstein_integer_coefficients(coefficients,address):
    result=list(coefficients);denominator=1
    for axis in range(4):
        matrix,scale=transform_matrix(address[axis]);denominator*=scale
        output=[0]*SIZE
        stride=5**(3-axis);block=5*stride
        for start in range(0,SIZE,block):
            for offset in range(stride):
                values=[result[start+r*stride+offset]for r in range(5)]
                for j in range(5):
                    output[start+j*stride+offset]=sum(matrix[j][r]*values[r]for r in range(5))
        result=output
    return result,denominator


def path_address(path):
    address=[(0,0)]*4
    for step in path:
        assert isinstance(step,list)and len(step)==2
        axis,side=step
        assert type(axis)is int and 0<=axis<4 and type(side)is int and side in(0,1)
        n,d=address[axis];address[axis]=(2*n+side,d+1)
    return address


def check_cover(leaves):
    """Reconstruct one finite full binary tree. Every split retains both closed halves."""
    root={}
    for record in leaves:
        path=record['path'];node=root
        for axis,side in path:
            assert 'leaf'not in node,'A declared terminal has descendants'
            if 'axis'in node:assert node['axis']==axis,'Mixed split axes at one parent'
            else:node['axis']=axis
            node=node.setdefault(side,{})
        assert not node,'Repeated leaf or omitted subdivision'
        node['leaf']=True
    todo=[root];nodes=0;terminal=0
    while todo:
        node=todo.pop();nodes+=1
        if 'leaf'in node:
            assert node=={'leaf':True};terminal+=1
        else:
            assert set(node)=={'axis',0,1},'Missing complementary closed child'
            assert type(node['axis'])is int and 0<=node['axis']<4
            todo.extend((node[0],node[1]))
    assert terminal==len(leaves)
    assert nodes==2*terminal-1
    return nodes


def check_file(path,expected):
    raw=path.read_bytes();data=json.loads(raw)
    signs,owners,k=expected
    assert data['schema']=='four_row_chiral_polynomial_discovery_v1'
    assert data['root_upper']==str(ROOT)
    assert data['variation_certified_candidate']==str(CERT_VARIATION)
    assert data['signs']==signs and data['owners']==owners and data['owner_for_max']==k
    assert data['frontier']==[],'An unresolved frontier is not a proof'
    leaves=data['leaves'];assert leaves
    nodes=check_cover(leaves);assert data['nodes']==nodes
    features=reconstruct_features(signs,owners,k)
    zero_count=0;strict_count=0;max_depth=0;minimum_positive=None
    for number,leaf in enumerate(leaves):
        path_steps=leaf['path'];address=path_address(path_steps)
        max_depth=max(max_depth,len(path_steps))
        power=leaf['weight_power'];assert type(power)is int and 0<=power<=80
        W=2**power;weights=leaf['weights'];assert len(weights)==5
        assert all(type(x)is int for x in weights)
        assert all(-W<=x<=W for x in weights[:3])
        assert all(0<=x<=W for x in weights[3:])
        coefficients=[W*features[0][j]+sum(weights[i]*features[i+1][j]for i in range(5))for j in range(SIZE)]
        transformed,denominator=bernstein_integer_coefficients(coefficients,address)
        least=min(transformed)
        assert least>=0,(path.name,number,'Negative exact Bernstein coefficient',least)
        z=sum(x==0 for x in transformed);zero_count+=z
        if least>0:
            strict_count+=1
            candidate=F(least,denominator*W*SCALE)
            if minimum_positive is None or candidate<minimum_positive:minimum_positive=candidate
    assert max_depth==data['maxdepth']
    return {'file':path.name,'sha256':hashlib.sha256(raw).hexdigest(),
            'signs':signs,'owners':owners,'selected_owner':k,
            'nodes':nodes,'leaves':len(leaves),'strict_coefficient_leaves':strict_count,
            'nonnegative_coefficient_leaves':len(leaves)-strict_count,
            'exact_coefficients_checked':len(leaves)*SIZE,'zero_coefficients':zero_count,
            'maximum_depth':max_depth,'least_positive_polynomial_box_reserve':str(minimum_positive)}


def expected_domains():
    result=[]
    for a,b in product((-1,1),repeat=2):
        signs=[1,a,b,-1]
        for choices in product((0,1),repeat=3):
            owners=[j+v for j,v in enumerate(choices)]
            for k in sorted(set(owners)):
                name='s'+''.join('p'if s>0 else'm'for s in signs)+'_o'+''.join(str(v)for v in owners)+'_k'+str(k)+'.json'
                result.append((name,(signs,owners,k)))
    assert len(result)==80
    return result


def run(directory):
    start=time.monotonic();reports=[]
    domains=expected_domains()
    manifest=json.loads((directory/'DISCOVERY_MANIFEST.json').read_text())
    assert manifest['root_upper']==str(ROOT)and manifest['strict_variation_candidate']==str(CERT_VARIATION)
    assert manifest['target_variation']==str(TARGET_VARIATION)
    assert len(manifest['domains'])==len(domains)
    assert {d['file']for d in manifest['domains']}=={name for name,_ in domains}
    assert set(p.name for p in directory.glob('s*_o*_k*.json'))=={name for name,_ in domains}
    for index,(name,expected) in enumerate(domains):
        report=check_file(directory/name,expected);reports.append(report)
        print(json.dumps({'domain':index+1,'file':name,'leaves':report['leaves'],'status':'PASS_EXACT_INTEGER_BERNSTEIN'}),flush=True)
    assert manifest['nodes']==sum(r['nodes']for r in reports)
    assert manifest['leaves']==sum(r['leaves']for r in reports)
    assert manifest['open']==0
    result={'status':'PASS_COMPLETE_EXACT_CHIRAL_ROW_COVER',
            'scope':'Complete scalar sign/owner/folded-angle cover; physical lifting and immutable original caller remain separate obligations',
            'root_upper':str(ROOT),'certificate_variation':str(CERT_VARIATION),
            'physical_terminal_variation':str(TARGET_VARIATION),
            'physical_strict_reserve_per_selected_owner_slope':str(CERT_VARIATION-TARGET_VARIATION),
            'fixed_sign_patterns':4,'owned_axis_patterns':8,'complete_domains':len(reports),
            'nodes':sum(r['nodes']for r in reports),'leaves':sum(r['leaves']for r in reports),
            'coefficient_checks':sum(r['exact_coefficients_checked']for r in reports),
            'strict_coefficient_leaves':sum(r['strict_coefficient_leaves']for r in reports),
            'nonnegative_coefficient_leaves':sum(r['nonnegative_coefficient_leaves']for r in reports),
            'frontier':0,'new_original_cells_closed':0,'new_masks_closed':0,
            'domains':reports,'seconds':time.monotonic()-start,
            'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    return result


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory',type=Path,default=Path(__file__).parent/'chiral_cover')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args();result=run(args.directory)
    target=args.output or args.directory/'EXACT_REPLAY.json'
    target.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k!='domains'},indent=2))
