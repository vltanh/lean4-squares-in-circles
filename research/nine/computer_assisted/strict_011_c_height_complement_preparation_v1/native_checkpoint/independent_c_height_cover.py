"""Independent exact four-form reconstruction and all-quadrant cover proof."""
if not __debug__:
    raise RuntimeError('Independent C-height checks require assertions.')
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json

GUARD_BINDING='4c1fb0040f43281fd6e21bbece48d7293d0310a7341f490930c40ef51b689023'

def symbolic_coverage():
    # In each complete closed sign quadrant put yB=w, yC=w+r*a,
    # yD=w+r*a+s*b with a,b>=0. Then W=a+b. Fixed world coefficients
    # are independent of the producer's signed-difference expansion.
    forms=((-1,0,1),(-1,2,-1),(1,-2,1),(1,0,-1))
    cases=[]
    for r,s in product((-1,1),repeat=2):
        residuals=[];attained=[]
        for branch,(cb,cc,cd)in enumerate(forms):
            assert cb+cc+cd==0
            alpha=F((cc+cd)*r);beta=F(cd*s)
            slack=(1-alpha,1-beta)
            assert all(value in (0,2)for value in slack)
            residuals.append(dict(branch=branch,coefficients_on_nonnegative_a_b=list(map(str,slack))))
            if slack==(0,0):attained.append(branch)
        assert len(attained)==1
        cases.append(dict(closed_signs=[r,s],a_definition='abs(yC-yB)',b_definition='abs(yD-yC)',
            W_coefficients=['1','1'],nonnegative_W_minus_form_coefficients=residuals,
            attaining_branch=attained[0],zero_sign_faces_retained=True))
    assert sorted(case['attaining_branch']for case in cases)==list(range(4))
    return dict(status='PASS_SYMBOLIC_MAX_IDENTITY_IN_ALL_FOUR_CLOSED_SIGN_QUADRANTS',
        cases=cases,identity='abs(yC-yB)+abs(yD-yC)=max(yD-yB,2*yC-yB-yD,yB+yD-2*yC,yB-yD)',
        strict_W_above_threshold_implies_some_strict_form_above=True,
        weakening_each_selected_strict_inequality_to_closed_preserves_cover=True)

def reconstruct(document,sources):
    raw_document_hash=sources.assert_caller(document)
    algebra=symbolic_coverage();assert len(algebra['cases'])==4
    form_rows=[[[3,'-1'],[7,'1']],[[3,'-1'],[5,'2'],[7,'-1']],
               [[3,'1'],[5,'-2'],[7,'1']],[[3,'1'],[7,'-1']]]
    inequality_rows=[[[3,'1'],[7,'-1']],[[3,'1'],[5,'-2'],[7,'1']],
                     [[3,'-1'],[5,'2'],[7,'-1']],[[3,'-1'],[7,'1']]]
    signs=[[1,1],[1,-1],[-1,1],[-1,-1]]
    branches=[]
    for branch in range(4):
        assert dict((j,-F(v))for j,v in form_rows[branch])==dict((j,F(v))for j,v in inequality_rows[branch])
        branches.append(dict(branch=branch,signs=signs[branch],signed_height_form=form_rows[branch],
            relation='>=',threshold='21/100',affine_row=dict(
                name='strict011_C_height_complement_v1:'+str(branch),coefficients=inequality_rows[branch],rhs='-21/100')))
    return dict(kind='prepared_strict011_C_variation_closed_complement_v1',
        accepted_guard_binding_sha256=GUARD_BINDING,
        caller_root_id=document['original_id'],caller_root_document_sha256=raw_document_hash,
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

def verify_literal(printed,document,sources):
    assert isinstance(printed,dict)
    expected=reconstruct(document,sources)
    assert printed==expected
    sources.check_unchanged()
    return expected
