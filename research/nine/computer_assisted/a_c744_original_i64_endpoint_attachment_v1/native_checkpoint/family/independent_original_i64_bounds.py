"""Original-wide endpoint transport after the complete I64 implication.

Imports no producer/optimizer. Native source reuse is explicit; the newly
completed 813-deduction receipt is distinct from every historical receipt.
"""
if not __debug__:raise RuntimeError('Exact original-wide transport requires assertions.')
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
import hashlib,importlib.util,json,sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
GATE=HERE.parent/'i64_fresh_gate_v3'
sys.path.insert(0,str(GATE));sys.path.insert(0,str(ROOT/'ac_work/tree'))
import historical_source_cache as HISTORY
import independent_certified_union_original_rows as LITERAL
TARGET='positive-c744bc031d40ee64'
ORIGINAL_PATH=[['angle',3,1],['angle_cut',[0,'0'],0],['inward_row_escape',[7,8],[4]]]
SCOPE='WHOLE_UNCHANGED_ORIGINAL_PARENT'
BINDING=HERE/'PREMISE_BINDING.json'
BINDING_SHA='63458318a3681d677745baf4a00d8a738a5705c6276659174e59f440fa9a06e3'
PREFIX='certified_a_c744_original_i64_bound_'
HEIGHT_NAME='certified_a_c744_original_i64_height_'+BINDING_SHA
HEIGHT=(((3,F(1)),(7,F(1)),(17,F(-2))),F(-16,25),HEIGHT_NAME)

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def read(path):return json.loads(Path(path).read_text())
def checked_ref(reference):
    assert set(reference)=={'path','sha256'}
    assert sha(reference['path'])==reference['sha256'],reference['path']
    return Path(reference['path'])

def assert_caller(state):
    assert state['id']==TARGET
    assert isinstance(state['path'],list)and state['path'][:len(ORIGINAL_PATH)]==ORIGINAL_PATH
    assert len(state['angles'])==9 and len(state['positions'])==18 and len(state['scalar'])==36

def check_guard(state):
    assert_caller(state);assert state['path']==ORIGINAL_PATH
    assert F(state['angles'][3][0])>=0
    differences={tuple(e['pair']):e['intervals']for e in state['differences']}
    dg,di=differences[3,6],differences[3,8]
    assert -1<F(dg[0][0])<=F(dg[0][1])<1
    assert F(dg[1][0])>=0 and F(di[0][1])<0
    return True

def verify_binding():
    assert sha(BINDING)==BINDING_SHA;b=read(BINDING)
    assert b['schema']=='A_c744_original_wide_I64_certified_endpoint_family_v2'
    assert b['original_id']==TARGET and b['original_path']==ORIGINAL_PATH
    assert b['scope']==SCOPE and b['valid_on_whole_original']is True
    assert b['mask']=='001/00'and b['squared_radius']=='1105/256'
    assert b['new_original_cells']==b['new_masks']==0 and b['original_still_open']is True
    for name in ('no_source_child_or_SAT_predicate_transported','no_auxiliary_bounds_transported',
      'source_narrowing_is_necessary_on_entire_original','historical_accepted_source_proofs_explicitly_reused',
      'fresh813_source_arithmetic_completed','source_precedes_this_endpoint_prefix',
      'necessary_weak_I64_row_separately_exposed'):assert b[name]is True
    assert b['old_source_arithmetic_repeated']is False
    assert (b['endpoint_rows'],b['whole_original_height_rows'],b['endpoint_plus_height_rows'])==(414,1,415)
    assert b['physical_premises']==dict(all_nine_originals=True,original_corners=36,original_pairs=36,
      marked_cones=5,actual_AB_BC_EF_FG=True,strict_weak_CD=True,original_mask='001/00',closed_shared_faces=True)
    for name,h in b['independent_helper_sha256'].items():assert sha(name)==h,name
    for key in ('source_record','source_manifest','fresh_narrowed_source_report','fresh_source_gate_binding',
      'fresh_scalar_report','historical_reuse_binding','whole_original_parent','completed_0_2_4_binding',
      'completed_1_binding','original_wide_hand','published_original_wide_source_review','fresh_gate_root_source_review'):
        checked_ref(b[key])
    assert b['source_record']['sha256']=='858f627dd6ab4ed6efbd6f57614787d037fe1482997eca4313a3a9eaa1e25244'
    assert b['fresh_narrowed_source_report']['sha256']=='a6798bdf6a99d3bfdbf5bbe4af6600577959fd06da2c97412c0f7f9fa384a07e'
    assert b['fresh_source_gate_binding']['sha256']=='80b4dcd1582f18e50b1db4b6d592b3f7b0863a4dff76ffb4ddbc6105e140820a'
    freeze=read(checked_ref(b['fresh_source_gate_binding']))
    for rel,h in freeze['files'].items():assert sha(GATE/rel)==h,rel
    for path,h in freeze['loaded_independent_dependency_sha256'].items():assert sha(path)==h,path
    source=read(checked_ref(b['source_record']));manifest=read(checked_ref(b['source_manifest']))
    report=read(checked_ref(b['fresh_narrowed_source_report']))
    evidence,_=HISTORY.validate()
    assert report['historical_source_proof_reuse']==evidence
    assert report['status']=='PASS_RECOVERED_NARROWED_A3_064_BOUND_RECORD_OPEN'
    assert report['original_id']==TARGET and report['original_path']==ORIGINAL_PATH
    assert report['scope']=='EXPLICIT_NARROWED_SUBSET_OF_OLD_COMPONENT3'
    expected_domain=dict(name='stronger_actual_ab_064_A_c744_I_high',coefficients=[[3,'1'],[7,'1'],[17,'-2']],rhs='-16/25')
    assert report['source_domain']==manifest['narrowed_I64_source_domain']==expected_domain
    assert b['necessary_weak_I64_row']==dict(coefficients=expected_domain['coefficients'],rhs=expected_domain['rhs'])
    assert report['new_original_cells']==report['new_masks']==0
    assert report['weighted_source_record_freshly_replayed']is True
    assert report['complete_A1_and_old_source_arithmetic_repeated']is False
    assert report['cold_portable_proof_claimed']is False
    assert report['old_lost_receipts_recreated']is False and report['retained235_consumer_replayed']is False
    assert report['cached_source_provider_calls']==dict(post=1,shared=1,a1=1,complements=1)
    assert (report['nodes'],report['leaf_domains'],report['open_leaves'],report['excluded_leaves'])==(1,1,1,0)
    assert (report['rounds'],report['deductions'],report['printed_rows_checked'])==(7,813,1941)
    assert (report['I64_literal_occurrences_checked'],report['universal_center_literal_occurrences_checked'])==(2,131)
    assert report['final_state_checked_by_unchanged_record_core']is True
    assert b['source_final_state']==source['final']==report['independently_checked_final_state']
    assert source['id']==TARGET and source['original_path']==ORIGINAL_PATH and source['status']=='OPEN'
    assert source['initial']['id']==TARGET and source['initial']['path']==ORIGINAL_PATH
    assert PREFIX.encode()not in Path(b['source_record']['path']).read_bytes()
    assert len(manifest['nodes'])==1 and manifest['nodes'][0]['children']==[]and 'split'not in manifest['nodes'][0]
    assert manifest['nodes'][0]['sha256']==b['source_record']['sha256']
    engine=report['inherited_engine_report'];assert sha(engine['path'])==engine['sha256']
    assert read(engine['path'])==engine['report']
    whole=read(checked_ref(b['whole_original_parent']))
    assert whole['scope']==SCOPE and whole['id']==TARGET and whole['original_path']==ORIGINAL_PATH
    assert engine['report']['ancestor_replay']['whole_ancestor']['certificate_sha256']==b['whole_original_parent']['sha256']
    check_guard(whole['record']['final'])
    old024=HISTORY.COMPLEMENTS.verify_binding();old1=HISTORY.A1.verify_binding()
    expected={0:([[2,'1'],[16,'-1']],'0'),1:([[3,'-1'],[7,'1']],'3/5'),
      2:([[3,'1'],[7,'-1']],'3/5'),4:([[3,'1'],[7,'1'],[17,'-2']],'3/5')}
    rows={e['component']:e['necessary_weak_row']for e in old024['consequences']};rows[1]=old1['necessary_weak_row']
    assert set(rows)=={0,1,2,4}
    for component,(co,rhs)in expected.items():assert rows[component]==dict(coefficients=co,rhs=rhs)
    assert b['old_necessary_weak_rows']==[dict(component=i,**rows[i])for i in (0,1,2,4)]
    scalar=read(checked_ref(b['fresh_scalar_report']))
    assert report['fresh_064_scalar_replay']['sha256']==b['fresh_scalar_report']['sha256']
    assert report['fresh_064_scalar_replay']['report']==scalar
    assert scalar['status']=='PASS_COMPLETE_EXACT_TWO_LINK_SCALAR_COVER'
    assert (scalar['domains'],scalar['leaves'],scalar['bernstein_coefficients'],scalar['frontier'])==(28,121,15125,0)
    assert scalar['coefficient']=='641/1000'and scalar['target_variation']=='16/25'and scalar['strict_except_all_zero']is True
    assert F(3,5)<F(16,25)
    # The separately reviewed hand theorem supplies the continuous four-form
    # implication and the strict-CD equality blocker at closed Q.
    review=read(checked_ref(b['published_original_wide_source_review']))
    assert review['status']=='PASS_ROOT_I64_RECOVERY_BYTES_AND_ORIGINAL_WIDE_PHYSICAL_ATTACHMENT'
    assert review['new_original_cells']==review['new_masks']==0
    assert len({0,1,8,3,4,5,6})==7
    state=b['source_final_state'];assert_caller(state);assert state['path']==ORIGINAL_PATH
    assert set(state)=={'id','path','angles','positions','scalar','differences','diagonal'}
    for name in ('positions','scalar','angles'):assert all(F(a)<=F(z)for a,z in state[name])
    assert all(F(a)>0 for a,z in state['scalar'][:9])
    assert all(-1<=F(a)<=F(z)<=1 for a,z in state['angles'])
    pairs=set(combinations(range(9),2))
    for name in ('differences','diagonal'):
        assert len(state[name])==36 and {tuple(e['pair'])for e in state[name]}==pairs
        assert all(len(e['intervals'])==2 and all(F(a)<=F(z)for a,z in e['intervals'])for e in state[name])
    return b

def verify_literal(literal,caller,binding):
    assert_caller(caller)
    assert binding['original_id']==TARGET and binding['original_path']==ORIGINAL_PATH
    assert binding['scope']==SCOPE and binding['valid_on_whole_original']is True
    co,rhs,name=literal
    if name==HEIGHT_NAME:
        assert literal==HEIGHT;return literal
    assert name.startswith(PREFIX+BINDING_SHA+'_')
    LITERAL.verify_literal((co,rhs,LITERAL.PREFIX+name[len(PREFIX):]),binding['source_final_state'],BINDING_SHA)
    return literal
