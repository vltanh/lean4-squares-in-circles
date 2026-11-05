"""New strict011 H/I and original-C quantitative guard proposals after reset.

These literals do not establish state ancestry or run the accepted scalar
certificate. Both remain separate mandatory obligations at actual use.
"""
if not __debug__:
    raise RuntimeError('Exact guard checks require assertions.')
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
CALLERS={
    'full-strict-01100-root-v2':('base.json','e11fe83de71455d05ab58bcc12625050c1d37ef1aac4df5d2069299e566782a2'),
    'full-strict-01100-representative-root-v1':('representative.json','f67d826cbf6098191ced2319ff35acdeb752579cf9d5f0ef8a59bde6e1969f8b')}

def caller(document):
    name,expected=CALLERS[document['original_id']]
    raw=(HERE/'callers'/name).read_bytes()
    assert sha256(raw).hexdigest()==expected and document==json.loads(raw)
    assert document['mask']=='011/00' and document['radius_mode']=='strict'
    return expected

def cone_certificate():
    rows=[]
    for i,j in ((1,2),(2,3)):
        for sign in (-1,1):
            coefficients={2*i:F(1),2*j:F(-1),2*i+1:F(-sign),2*j+1:F(sign)}
            rows.append(dict(name=f'strict011v2:cone:{i}:{j}:{sign}',
                coefficients=[[k,str(v)] for k,v in sorted(coefficients.items())],rhs='0'))
    return dict(premises=rows,pairwise_weights=['1/2','1/2'],
        resulting_order_rows=[dict(coefficients=[[2,'1'],[4,'-1']],rhs='0'),
                              dict(coefficients=[[4,'1'],[6,'-1']],rhs='0')])

def evaluate(state,document,middle_original,mode):
    document_hash=caller(document)
    assert state['id']==document['original_id'] and isinstance(state['path'],list)
    assert type(middle_original) is int
    assert (mode=='HI' and middle_original in (7,8)) or (mode=='C' and middle_original==2)
    positions=tuple(tuple(map(F,ab)) for ab in state['positions'])
    assert len(positions)==18 and all(len(ab)==2 and ab[0]<=ab[1] for ab in positions)
    raw=state['differences']
    if isinstance(raw,dict):raw=[dict(pair=list(pair),intervals=value) for pair,value in raw.items()]
    assert isinstance(raw,list)
    differences={}
    for entry in raw:
        pair=tuple(entry['pair'])
        assert len(pair)==2 and all(type(k) is int for k in pair) and 0<=pair[0]<pair[1]<9
        assert pair not in differences
        value=tuple(tuple(map(F,ab)) for ab in entry['intervals'])
        assert len(value)==2 and all(len(ab)==2 and ab[0]<=ab[1] for ab in value)
        differences[pair]=value
    def difference(i,j,axis):
        lo=positions[2*j+axis][0]-positions[2*i+axis][1]
        hi=positions[2*j+axis][1]-positions[2*i+axis][0]
        pair=tuple(sorted((i,j)))
        if pair in differences:
            a,b=differences[pair][axis]
            if i>j:a,b=-b,-a
            lo,hi=max(lo,a),min(hi,b)
        assert lo<=hi
        return lo,hi
    x=middle_original
    heights=[difference(1,3,1)[1],difference(3,1,1)[1],
        difference(1,x,1)[1]+difference(3,x,1)[1],
        difference(x,1,1)[1]+difference(x,3,1)[1]]
    upper=max(heights);assert upper>=0
    if mode=='HI':
        intervals=[difference(1,x,0),difference(x,3,0)]
        ordered=all(lo>=0 for lo,hi in intervals)
        order=dict(source='certified_horizontal_difference_intervals',
                   intervals=[list(map(str,ab)) for ab in intervals])
    else:
        ordered=True
        order=dict(source='exact_original_BC_CD_center_cones',certificate=cone_certificate())
    passed=ordered and upper<=F(21,100)
    return dict(kind='strict011_universal021_'+mode+'_v2',
        status='PASS_STRICT011_UNIVERSAL021_GUARD' if passed else 'GUARD_NOT_IMPLIED',
        theorem='universal_actual_AB_two_link_v1',caller_root_id=state['id'],
        caller_root_document_sha256=document_hash,caller_path=deepcopy(state['path']),
        mask='011/00',radius_mode='strict',target_q='1105/256',
        middle_original=x,physical_row=[0,1,x,3],
        selected_distinct_originals=[0,1,x,3,4,5,6],
        all_nine_originals=list(range(9)),original_corners=36,original_pairs=36,marked_cones=5,
        actual_links_required=[[0,1],[4,5],[5,6]],strict_weak_links_retained=[[1,2],[2,3]],
        order=order,four_signed_height_upper_bounds=list(map(str,heights)),
        variation_upper=str(upper),variation_limit='21/100',
        conclusion='q >= 1105/256 contradicts the strict-radius caller',
        actual_BC_assumed=False,closed_Q_equality_blocker_used=False,
        additional_frame_sign_or_DG_guard_required=False,
        certified_complete_state_ancestry_required=True,fresh_scalar_replay_required_at_use=True,
        installed_in_tree_replay=False,whole_mask_cover_checked=False,
        original_cell_credit=0,whole_mask_credit=0)

def evaluate_hi(state,document,extra):return evaluate(state,document,extra,'HI')
def evaluate_c(state,document):return evaluate(state,document,2,'C')
