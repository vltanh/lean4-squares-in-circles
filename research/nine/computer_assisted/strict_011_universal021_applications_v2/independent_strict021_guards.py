"""Independent signed-bound and whole-caller reconstruction for both new guards."""
if not __debug__:
    raise RuntimeError('Exact guard replay requires assertions.')
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations,product
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
CALLERS={
    'full-strict-01100-root-v2':('base.json','e11fe83de71455d05ab58bcc12625050c1d37ef1aac4df5d2069299e566782a2'),
    'full-strict-01100-representative-root-v1':('representative.json','f67d826cbf6098191ced2319ff35acdeb752579cf9d5f0ef8a59bde6e1969f8b')}

def assert_caller(document):
    file,expected=CALLERS[document['original_id']]
    raw=(HERE/'callers'/file).read_bytes()
    assert sha256(raw).hexdigest()==expected and document==json.loads(raw)
    assert document['mask']=='011/00' and document['radius_mode']=='strict' and document['target_q']=='1105/256'
    assert document['corner_relation']=='Every original corner norm_squared < 1105/256'
    assert document['physical_originals']==list(range(9))
    assert document['original_corners']==[list(x) for x in product(range(9),(-1,1),(-1,1))]
    assert document['original_pairs']==[list(x) for x in combinations(range(9),2)]
    assert document['pair_relation']=='Every original pair has disjoint open interiors; physical contact allowed'
    assert document['exact_mask_edges']==[
        dict(pair=list(pair),bit=bit,cone='xj-xi >= abs(yj-yi)',
             bit_relation='xj-xi < hi+hj' if bit else 'xj-xi >= hi+hj')
        for pair,bit in (((0,1),0),((1,2),1),((2,3),1),((4,5),0),((5,6),0))]
    assert document['inherited_001_premises']==document['inherited_original_cells']==[]
    return expected

def original_cone_order():
    premises=[
        dict(name='strict011v2:cone:1:2:-1',coefficients=[[2,'1'],[3,'1'],[4,'-1'],[5,'-1']],rhs='0'),
        dict(name='strict011v2:cone:1:2:1',coefficients=[[2,'1'],[3,'-1'],[4,'-1'],[5,'1']],rhs='0'),
        dict(name='strict011v2:cone:2:3:-1',coefficients=[[4,'1'],[5,'1'],[6,'-1'],[7,'-1']],rhs='0'),
        dict(name='strict011v2:cone:2:3:1',coefficients=[[4,'1'],[5,'-1'],[6,'-1'],[7,'1']],rhs='0')]
    conclusions=[]
    for offset in (0,2):
        co={}
        for premise in premises[offset:offset+2]:
            for column,value in premise['coefficients']:co[column]=co.get(column,F(0))+F(value)/2
        conclusions.append(dict(coefficients=[[k,str(v)] for k,v in sorted(co.items()) if v],rhs='0'))
    assert conclusions==[dict(coefficients=[[2,'1'],[4,'-1']],rhs='0'),dict(coefficients=[[4,'1'],[6,'-1']],rhs='0')]
    return dict(premises=premises,pairwise_weights=['1/2','1/2'],resulting_order_rows=conclusions)

def reconstruct(state,document,middle_original,mode):
    document_hash=assert_caller(document)
    assert state['id']==document['original_id'] and isinstance(state['path'],list)
    assert type(middle_original) is int
    assert mode in ('HI','C') and middle_original in ((7,8) if mode=='HI' else (2,))
    positions=tuple(tuple(F(v) for v in b) for b in state['positions'])
    assert len(positions)==18 and all(len(b)==2 and b[0]<=b[1] for b in positions)
    source=state['differences']
    if isinstance(source,dict):source=[dict(pair=list(k),intervals=v) for k,v in source.items()]
    assert isinstance(source,list)
    differences={}
    for entry in source:
        i,j=entry['pair']
        assert type(i) is int and type(j) is int and 0<=i<j<9 and (i,j) not in differences
        bounds=tuple(tuple(F(v) for v in interval) for interval in entry['intervals'])
        assert len(bounds)==2 and all(len(b)==2 and b[0]<=b[1] for b in bounds)
        differences[i,j]=bounds
    def upper(left,right,axis):
        bound=positions[2*left+axis][1]-positions[2*right+axis][0]
        if left>right and (right,left) in differences:bound=min(bound,differences[right,left][axis][1])
        if left<right and (left,right) in differences:bound=min(bound,-differences[left,right][axis][0])
        return bound
    def interval(i,j,axis):
        bounds=(-upper(i,j,axis),upper(j,i,axis));assert bounds[0]<=bounds[1]
        return bounds
    x=middle_original
    for i,j in ((1,3),(1,x),(3,x)):interval(i,j,1)
    heights=[upper(3,1,1),upper(1,3,1),upper(x,1,1)+upper(x,3,1),upper(1,x,1)+upper(3,x,1)]
    maximum=max(heights);assert maximum>=0
    if mode=='HI':
        horizontal=[interval(1,x,0),interval(x,3,0)]
        ordered=min(b[0] for b in horizontal)>=0
        order=dict(source='certified_horizontal_difference_intervals',intervals=[list(map(str,b)) for b in horizontal])
    else:
        ordered=True
        order=dict(source='exact_original_BC_CD_center_cones',certificate=original_cone_order())
    passed=ordered and maximum<=F(21,100)
    return dict(kind='strict011_universal021_'+mode+'_v2',
        status='PASS_STRICT011_UNIVERSAL021_GUARD' if passed else 'GUARD_NOT_IMPLIED',
        theorem='universal_actual_AB_two_link_v1',caller_root_id=state['id'],
        caller_root_document_sha256=document_hash,caller_path=deepcopy(state['path']),
        mask='011/00',radius_mode='strict',target_q='1105/256',
        middle_original=x,physical_row=[0,1,x,3],selected_distinct_originals=[0,1,x,3,4,5,6],
        all_nine_originals=list(range(9)),original_corners=36,original_pairs=36,marked_cones=5,
        actual_links_required=[[0,1],[4,5],[5,6]],strict_weak_links_retained=[[1,2],[2,3]],
        order=order,four_signed_height_upper_bounds=list(map(str,heights)),variation_upper=str(maximum),variation_limit='21/100',
        conclusion='q >= 1105/256 contradicts the strict-radius caller',
        actual_BC_assumed=False,closed_Q_equality_blocker_used=False,additional_frame_sign_or_DG_guard_required=False,
        certified_complete_state_ancestry_required=True,fresh_scalar_replay_required_at_use=True,
        installed_in_tree_replay=False,whole_mask_cover_checked=False,original_cell_credit=0,whole_mask_credit=0)

def verify_literal(printed,state,document):
    assert isinstance(printed,dict)
    mode={'strict011_universal021_HI_v2':'HI','strict011_universal021_C_v2':'C'}[printed['kind']]
    value=reconstruct(state,document,printed['middle_original'],mode)
    assert value['status']=='PASS_STRICT011_UNIVERSAL021_GUARD' and printed==value
    return value
