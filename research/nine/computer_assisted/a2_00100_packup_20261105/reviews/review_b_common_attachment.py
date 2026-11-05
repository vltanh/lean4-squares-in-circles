"""Focused independent decoder and original-B physical attachment review."""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
from math import isqrt
from itertools import combinations
import importlib.util,json,sys,time
import review_b16_checkpoints as R

HERE=Path(__file__).resolve().parent
TARGET=HERE.parent/'b16_continue/additional_rows'
COMMON=HERE.parent/'b462_continue/additional_rows'

def rejected(fn):
    try:fn()
    except (AssertionError,KeyError):return True
    raise AssertionError('Damaged or unsupported input was accepted')

def downroot(q):
    d=2**16;n=isqrt(q.numerator*d*d//q.denominator)
    ans=F(n,d);assert ans*ans<=q;return ans

def main():
    start=time.monotonic();path=TARGET/'verify_b_common_additional_rows_v1.py'
    assert R.sha(path)=='41f766c2a2f3f4c4ed5fe0eaf77d6f3752fdb3b09f07e2fece968ea1ee595b87'
    spec=importlib.util.spec_from_file_location('reviewed_common_attachment',path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    cap=R.WORK/'recovery_20261105/extracted_b340/unpacked/b340_complete_original_package/accepted_repo/research/nine/computer_assisted/full_angle_common_side_row_v1'
    adapter=module.Adapter(R.WORK/'b16a_I32_complete_H_checkpoint',cap)
    parent=HERE.parent/'b16_geometry/node236_ancestry_prefix.json'
    assert R.sha(parent)=='e5a858f51e41475902275b97743a7aed29218ec6df287524b8b1dc6658cc422e'
    state=R.parse_state(R.read(parent)['final'],adapter)
    adapter.check_original(state)
    _,bounds,physical=adapter.rebuild(state,[])
    central=module.CENTRAL.rebuild('central_nine_radial_secant_0',physical['positions'],physical['scalar'])
    chord=None
    for i,j in combinations(range(9),2):
        for axis in (0,1):
            lo,hi=physical['differences'][i,j][axis]
            sign=1 if lo>=0 else (-1 if hi<=0 else None)
            if sign is None:continue
            l,u=physical['differences'][i,j][1-axis]
            zl=min(l,l/module.CHORD.H);zu=max(u,u/module.CHORD.H)
            if not -1<=zl<zu<=1:continue
            al,au=downroot(1-zl*zl),downroot(1-zu*zu)
            name=module.CHORD.PREFIX+'_'.join(map(str,['signed',i,j,axis,sign,1,zl,zu,al,au,'0000']))
            try:chord=module.CHORD.rebuild(name,physical['scalar'],physical['differences'])
            except AssertionError:continue
            if chord[1] < 0:break
        if chord and chord[1]<0:break
    assert chord is not None
    def row(index,literal):
        co,rhs,name=literal
        return dict(index=index,coefficients=[[i,str(v)] for i,v in co],rhs=str(rhs),name=name)
    printed=[row(1000000,central),row(1000001,chord)]
    rebuilt,checked_bounds,after=adapter.rebuild(state,printed)
    assert rebuilt=={1000000:central,1000001:chord}
    assert checked_bounds==bounds and after==physical
    mutations=[]
    for i in (0,1):
        damaged=deepcopy(printed);damaged[i]['rhs']=str(F(damaged[i]['rhs'])-1)
        assert rejected(lambda:adapter.rebuild(state,damaged));mutations.append('damaged_rhs_family_'+str(i))
    bad=deepcopy(state);bad['id']='negative-not-a-registered-original'
    assert rejected(lambda:adapter.check_original(bad));mutations.append('unknown_original')
    bad=deepcopy(state);bad['path'][0]=['angle',3,1]
    assert rejected(lambda:adapter.check_original(bad));mutations.append('changed_registered_prefix')
    bad=deepcopy(state);bad['differences'].pop((0,1))
    assert rejected(lambda:adapter.check_original(bad));mutations.append('missing_incoming_pair')
    b462=R.read(R.WORK/'recovery_20261105/registered_B_initial_states/negative-462e78d2e2d8be05.json')
    original_state=R.parse_state(b462['final'],adapter)
    assert not original_state['differences']
    assert rejected(lambda:adapter.check_original(original_state))
    wide=tuple((F(-91,60),F(91,60)) for _ in range(18))
    assert len(module.CENTRAL.eligible(wide))==9
    assert rejected(lambda:module.CENTRAL.rebuild('central_nine_near_axis_0_0_1',wide,physical['scalar']))
    mutations.append('unforced_near_label')
    assert rejected(lambda:module.CENTRAL.rebuild('central_nine_unknown_rule',physical['positions'],physical['scalar']))
    mutations.append('unknown_central_rule')
    adapter.recheck()
    assert not any(x in sys.modules for x in ('numpy','scipy','highspy','physical_relative_support_chords','central_nine_rows'))
    result=dict(status='PASS_SCOPED_DECODER_AND_ORIGINAL_B_ATTACHMENT_REVIEW',
        scope='Independent literal dispatch and physical attachment only; no actual weighted-use acceptance',
        valid_smoke_rows=[x['name'] for x in printed],rejected_controls=mutations,
        same_propagated_physical_intervals_used=True,no_new_terminal_or_cover_dispatch=True,
        untouched_registered_root_rejected_by_incoming_difference_guard=True,
        untouched_root_limit_is_conservative_not_unsound=True,
        actual_weighted_use_reviewed=False,original_cells_closed=0,masks_closed=0,
        source_identities=adapter.files,original_state_source_sha256=R.sha(parent),
        helper_source_sha256=R.sha(R.__file__),reviewer_source_sha256=R.sha(__file__),
        seconds=time.monotonic()-start)
    (HERE/'B_COMMON_ATTACHMENT_NONAUTHOR_REVIEW.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['status','valid_smoke_rows','rejected_controls','seconds']}))

if __name__=='__main__':
    assert __debug__
    main()
