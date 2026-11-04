"""Fresh source replay and independent original-only bound-row decoding."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,subprocess,sys

HERE=Path(__file__).resolve().parent
AC=HERE.parents[1]/'ac_work/tree'
sys.path.insert(0,str(AC))
import independent_certified_union_original_rows as LITERAL

BINDING=HERE/'CB882_WHOLE_HEIGHT_BOUND_STATE_BINDING.json'
BINDING_SHA='f0e49cf500739a4c878ef34c5f420e5430ca22dd9e147986615a4c546554ee38'
PREFIX='certified_cb882_root_bound_'
TARGET='negative-b882d8ade0cf9ea0'
ORIGINAL_PATH=[['angle',3,0],['angle_cut',[0,'0'],1],['alternate_four_escape',[1,7],[3]]]
SOURCE_SHA='88fe0a11aed912184b29e8868fd1317e70b5c6dbd29a6107d3651d90a687e2d8'
SOURCE_CHECKER_SHA='a3a5758ace88998a7ddfad664b77bcb134ab84414998f8967a3009b2fc2741ad'
PREFIX_SHA='3faca11f2a9bebfb813ae2c13228e4685c1bcb29352773aad967390943f8daf8'
LITERAL_SHA='2c51bd8ccb712083b1aecde3f0e832b05e8d3ac130d82aa1ac5fa02598e32e50'

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def validate_bound_state(state,complete_pairs=True):
    assert set(state)=={'id','path','angles','positions','scalar','differences','diagonal'}
    assert state['id']==TARGET and state['path']==ORIGINAL_PATH
    for field,size in (('angles',9),('positions',18),('scalar',36)):
        assert isinstance(state[field],list)and len(state[field])==size
        for interval in state[field]:
            assert isinstance(interval,list)and len(interval)==2
            lo,hi=map(F,interval);assert lo<=hi
            if field=='angles':assert -1<=lo<=hi<=1
    expected={(i,j)for i in range(9)for j in range(i+1,9)}
    for field in ('differences','diagonal'):
        assert isinstance(state[field],list)
        pairs=[]
        for row in state[field]:
            assert set(row)=={'pair','intervals'}
            pair=row['pair'];assert len(pair)==2 and all(type(k)is int for k in pair)
            pairs.append(tuple(pair));assert len(row['intervals'])==2
            for interval in row['intervals']:
                assert len(interval)==2 and F(interval[0])<=F(interval[1])
        assert len(pairs)==len(set(pairs))and set(pairs)<=expected
        if complete_pairs:assert len(pairs)==36 and set(pairs)==expected

def validate_source_domain(binding,source,prefix):
    assert binding['schema']=='CB882_whole_original_height_bound_state_attachment_v1'
    assert binding['original_id']==TARGET and binding['original_path']==ORIGINAL_PATH
    assert binding['mask']=='001/00'and binding['squared_radius']=='1105/256'
    assert binding['source_scope']=='WHOLE_UNCHANGED_ORIGINAL_PARENT'
    for field in ('one_unsplit_whole_original_record','no_selected_height_alternative',
        'no_C887_DG_union','no_child_restrictions_or_auxiliary_bounds_transported',
        'all_nine_originals_retained','closed_shared_faces_retained'):
        assert binding[field]is True
    assert binding['new_original_cells']==binding['new_masks']==0
    assert source['schema']=='same_original_verified_prefix_bound_discovery_v1'
    assert source['scope']==binding['source_scope']
    assert source['id']==TARGET and source['original_path']==ORIGINAL_PATH
    assert source['prefix']==binding['original_prefix']
    assert source['new_original_cells']==source['new_masks']==0
    forbidden=('conditional_row','closed_domain','global_original_union','component',
               'restriction','children','split')
    assert all(key not in source for key in forbidden)
    assert prefix['schema']=='independently_replayed_same_original_state_v1'
    assert prefix['status']=='PASS_CERTIFIED_WHOLE_ORIGINAL_C_B882_STATE_OPEN'
    assert prefix['certificate_sha256']=='1c6eb1e62f496889f392338a485c004adfdfd1d1b99f9cec847ac1aa9c11af03'
    assert prefix['state']['id']==TARGET and prefix['state']['path']==ORIGINAL_PATH
    record=source['record']
    assert record['status']=='OPEN'and 'terminal'not in record
    assert all(key not in record for key in forbidden)
    assert record['initial']==prefix['state']and record['final']==binding['state']
    validate_bound_state(record['initial'],complete_pairs=False)
    validate_bound_state(binding['state'])
    forbidden_prefixes=(PREFIX,'certified_original_union_bound_','certified_original_root_bound_')
    for round_record in record['rounds']:
        for row in round_record['printed_rows']:
            assert not row['name'].startswith(forbidden_prefixes)

def verify_binding():
    assert sha(LITERAL.__file__)==LITERAL_SHA
    assert sha(BINDING)==BINDING_SHA;binding=json.loads(BINDING.read_text())
    source=binding['source_record'];assert source['sha256']==SOURCE_SHA==sha(source['path'])
    prefix=binding['original_prefix'];assert prefix['sha256']==PREFIX_SHA==sha(prefix['path'])
    checker=binding['source_checker']
    assert checker['sha256']==SOURCE_CHECKER_SHA==sha(checker['path'])
    assert Path(checker['path']).name=='verify_cb882_whole_height_consequence_bound_pass.py'
    for path,h in binding['source_checker_dependencies'].items():assert sha(path)==h
    validate_source_domain(binding,json.loads(Path(source['path']).read_text()),
                           json.loads(Path(prefix['path']).read_text()))
    return binding

def assert_caller(state):
    assert state['id']==TARGET and state['path'][:len(ORIGINAL_PATH)]==ORIGINAL_PATH

def verify_literal(literal,caller,binding):
    assert_caller(caller)
    assert binding['original_id']==TARGET and binding['original_path']==ORIGINAL_PATH
    co,rhs,name=literal;assert name.startswith(PREFIX+BINDING_SHA+'_')
    old=(co,rhs,LITERAL.PREFIX+name[len(PREFIX):])
    LITERAL.verify_literal(old,binding['state'],BINDING_SHA)
    return literal

def replay_source(output_folder):
    binding=verify_binding();output_folder=Path(output_folder).resolve()
    output_folder.mkdir(parents=True,exist_ok=True)
    output=output_folder/'whole_root_replay.json';log=output_folder/'whole_root_replay.log'
    with log.open('w')as stream:
        subprocess.run([sys.executable,'-B','-S',binding['source_checker']['path'],
            binding['source_record']['path'],str(output)],check=True,stdout=stream,stderr=subprocess.STDOUT)
    result=json.loads(output.read_text())
    assert result['status']=='PASS_CERTIFIED_WHOLE_ORIGINAL_STATE_OPEN'
    assert result['original_id']==TARGET and result['original_path']==ORIGINAL_PATH
    assert result['certificate_sha256']==SOURCE_SHA and result['prefix_sha256']==PREFIX_SHA
    assert result['final']==binding['state']
    assert result['rounds']==3 and result['deductions']==441 and result['printed_rows_checked']==1009
    assert result['height_exclusion_consequence_row_occurrences_checked']==5
    assert result['all_nine_original_squares_retained']is True and result['closed_shared_faces_retained']is True
    assert result['no_conditional_height_alternative']is True and result['no_C887_DG_union_imported']is True
    assert result['new_original_cells']==result['new_masks']==0
    verify_binding()
    return dict(status='PASS_FRESH_UNSPLIT_CB882_WHOLE_ORIGINAL_BOUND_STATE',binding_sha256=BINDING_SHA,
        source_report=dict(path=str(output),sha256=sha(output),report=result),original_id=TARGET,
        original_path=ORIGINAL_PATH,new_original_cells=0,new_masks=0),binding
