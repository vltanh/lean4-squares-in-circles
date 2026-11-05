"""Literal producer for a future strict011 C-height theorem complement."""
if not __debug__:
    raise RuntimeError('C-height literal production requires assertions.')
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
import json

GUARD_BINDING='4c1fb0040f43281fd6e21bbece48d7293d0310a7341f490930c40ef51b689023'

def literal(document,sources):
    document_hash=sources.assert_caller(document)
    branches=[]
    for number,(s,t)in enumerate(((1,1),(1,-1),(-1,1),(-1,-1))):
        coefficients={3:-s,5:s-t,7:t}
        signed=[[j,str(a)]for j,a in sorted(coefficients.items())if a]
        row=[[j,str(-a)]for j,a in sorted(coefficients.items())if a]
        branches.append(dict(branch=number,signs=[s,t],signed_height_form=signed,
            relation='>=',threshold=str(F(21,100)),
            affine_row=dict(name='strict011_C_height_complement_v1:'+str(number),coefficients=row,rhs='-21/100')))
    return dict(kind='prepared_strict011_C_variation_closed_complement_v1',
        accepted_guard_binding_sha256=GUARD_BINDING,
        caller_root_id=document['original_id'],caller_root_document_sha256=document_hash,
        caller_initial_state_sha256=sha256(json.dumps(document['initial'],sort_keys=True,separators=(',',':')).encode()).hexdigest(),
        caller_initial_path=deepcopy(document['initial']['path']),
        mask='011/00',radius_mode='strict',target_q='1105/256',
        all_nine_originals=list(range(9)),original_corners=36,original_pairs=36,marked_cones=5,
        actual_links_required=[[0,1],[4,5],[5,6]],strict_weak_links_retained=[[1,2],[2,3]],
        selected_seven_originals=[0,1,2,3,4,5,6],other_originals_retained=[7,8],
        horizontal_order=dict(source='exact_original_BC_CD_center_cones',certificate=sources.cone_order()),
        normalization_equivalence=deepcopy(document.get('normalization_equivalence')),
        strict_physical_necessity='abs(yC-yB)+abs(yD-yC) > 21/100',
        branches=branches,closed_boundary_faces_retained=True,
        coverage_scope='all physical configurations of this exact strict caller after the accepted theorem',
        arbitrary_relaxed_box_coverage_claimed=False,actual_BC_assumed=False,
        D_frame_sign_or_DG_corridor_assumed=False,closed_Q_equality_blocker_used=False,
        fresh_scalar_replay_required_at_first_actual_use=True,
        future_complete_ancestry_adapter_review_required=True,
        frozen_four_eight_two_wrapper_changed=False,cover_installed=False,
        original_cell_credit=0,whole_mask_credit=0)
