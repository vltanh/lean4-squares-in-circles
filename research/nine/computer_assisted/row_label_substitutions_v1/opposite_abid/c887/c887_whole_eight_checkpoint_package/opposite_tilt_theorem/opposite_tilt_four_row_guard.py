"""Exact guards for the full-angle opposite-endpoint AHID row theorem.

Every supplied bound requires independent ancestry from the unchanged strict
original-nine001/00 caller. This helper checks quantitative/sign guards only.
It neither proves original ancestry nor assembles an original-cell cover.
"""
from fractions import Fraction as F
from itertools import product, permutations

if not __debug__:
    raise RuntimeError('Exact guard evaluation requires assertions; Python -O is not supported')

CHAIN=(0,7,8,3)
THRESHOLD=F(23,100)
THEOREM_VERSION='opposite_endpoint_full_angle_AHID_row_23_100_v1'


def threshold(value=THRESHOLD):
    value=F(value)
    assert 0<value<=THRESHOLD
    return value


def box(raw):
    result=tuple(tuple(F(x)for x in pair)for pair in raw)
    assert all(len(pair)==2 and pair[0]<=pair[1]for pair in result)
    return result


def unpack(state):
    positions=box(state['positions']);angles=box(state['angles']);scalar=box(state['scalar'])
    assert len(positions)==18 and len(angles)==9 and len(scalar)==36
    raw=state.get('differences',{})
    differences=({tuple(record['pair']):box(record['intervals'])for record in raw}
                 if isinstance(raw,list)else{tuple(key):box(value)for key,value in raw.items()})
    assert all(len(key)==2 and 0<=key[0]<key[1]<9 and len(value)==2 for key,value in differences.items())
    return positions,angles,scalar,differences


def difference(positions,differences,i,j,axis):
    if i==j:return F(0),F(0)
    low=positions[2*j+axis][0]-positions[2*i+axis][1]
    high=positions[2*j+axis][1]-positions[2*i+axis][0]
    if i<j and(i,j)in differences:
        a,b=differences[i,j][axis];low=max(low,a);high=min(high,b)
    if i>j and(j,i)in differences:
        a,b=differences[j,i][axis];low=max(low,-b);high=min(high,-a)
    assert low<=high
    return low,high


def height_expressions():
    result=[]
    for signs in product((-1,1),repeat=3):
        terms={}
        for i,j,sg in zip(CHAIN,CHAIN[1:],signs):
            terms[2*i+1]=terms.get(2*i+1,F(0))-sg
            terms[2*j+1]=terms.get(2*j+1,F(0))+sg
        result.append(tuple(sorted((index,F(c))for index,c in terms.items()if c)))
    return tuple(result)


def complement_rows(limit=THRESHOLD):
    limit=threshold(limit)
    result=[]
    for n,(i,j)in enumerate(zip(CHAIN,CHAIN[1:])):
        result.append((((2*j,F(1)),(2*i,F(-1))),F(0),'opposite_tilt_AHID_order_'+str(n)))
    for n,terms in enumerate(height_expressions()):
        result.append((tuple((index,-value)for index,value in terms),-limit,'opposite_tilt_AHID_variation_'+str(n)))
    assert len(result)==11
    return tuple(result)


def expression_upper(terms,positions,differences):
    bound=sum(value*positions[index][1 if value>0 else 0]for index,value in terms)
    positive=[];negative=[]
    for index,value in terms:
        assert index%2==1 and value.denominator==1
        (positive if value>0 else negative).extend([index//2]*abs(int(value)))
    assert len(positive)==len(negative)<=3
    # Every matching is a literal decomposition into original height differences.
    for ordering in set(permutations(positive)):
        candidate=sum(difference(positions,differences,i,j,1)[1]for i,j in zip(negative,ordering))
        bound=min(bound,candidate)
    return bound


def evaluate(state,limit=THRESHOLD):
    limit=threshold(limit)
    positions,angles,scalar,differences=unpack(state)
    a_nonnegative=angles[0][0]>=0 or scalar[9][0]>=0
    a_nonpositive=angles[0][1]<=0 or scalar[9][1]<=0
    d_nonnegative=angles[3][0]>=0 or scalar[12][0]>=0
    d_nonpositive=angles[3][1]<=0 or scalar[12][1]<=0
    opposite=(a_nonnegative and d_nonpositive)or(a_nonpositive and d_nonnegative)
    orders=[difference(positions,differences,i,j,0)for i,j in zip(CHAIN,CHAIN[1:])]
    signed_upper=[expression_upper(terms,positions,differences)for terms in height_expressions()]
    variation=max(signed_upper)
    passed=opposite and all(interval[0]>=0 for interval in orders)and variation<=limit
    return {'status':'PASS_OPPOSITE_TILT_AHID_TERMINAL'if passed else'GUARD_NOT_IMPLIED',
            'opposite_endpoint_signs_proved':opposite,
            'endpoint_angle_intervals':[[str(v)for v in angles[i]]for i in(0,3)],
            'endpoint_beta_intervals':[[str(v)for v in scalar[i]]for i in(9,12)],
            'horizontal_order_intervals':[[str(v)for v in interval]for interval in orders],
            'signed_height_upper_bounds':[str(v)for v in signed_upper],
            'certified_height_variation_upper':str(variation),'variation_limit':str(limit),
            'maximum_proved_variation':str(THRESHOLD),'theorem_version':THEOREM_VERSION,
            'full_original_ancestry_required':True,'whole_original_cover_checked':False,
            'new_original_cells':0,'new_masks':0}
