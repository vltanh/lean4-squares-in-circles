"""Independent source replay and original-only affine bound reconstruction."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,subprocess,sys
import independent_certified_union_original_rows as LITERAL

HERE=Path(__file__).resolve().parent
BINDING=HERE/'C887_WHOLE_HEIGHT_BOUND_STATE_BINDING.json'
BINDING_SHA='b24a9fa7675eb4d2330518da7481e5bca75700928035d202eeb9bf964a4adf2d'
PREFIX='certified_original_root_bound_'
TARGET='negative-887236b78100baf3'
ORIGINAL_PATH=[['angle',3,0],['angle_cut',[0,'0'],1],['alternate_four_escape',[1,7],[1]]]
SOURCE_CHECKER_SHA='c42e9a6b517a2f31fe79cf0280e10fda36966d11d1fdb5dfda546918c6c25e3e'

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def verify_binding():
    assert sha(BINDING)==BINDING_SHA;binding=json.loads(BINDING.read_text())
    assert binding['schema']=='C887_whole_original_height_bound_state_attachment_v1'
    assert binding['original_id']==TARGET and binding['original_path']==ORIGINAL_PATH
    assert binding['mask']=='001/00'and binding['squared_radius']=='1105/256'
    for field in ('one_unsplit_whole_original_node','no_child_restrictions_or_auxiliary_bounds_transported',
        'all_nine_originals_retained','closed_shared_faces_retained'):assert binding[field]is True
    assert binding['new_original_cells']==binding['new_masks']==0
    source=binding['source_tree'];folder=Path(source['folder'])
    assert sha(folder/'manifest.json')==source['manifest_sha256']
    manifest=json.loads((folder/'manifest.json').read_text())
    assert manifest['schema']=='same_original_physical_SAT_proxy_angle_tree_discovery_v1'
    assert manifest['id']==TARGET and manifest['original_path']==ORIGINAL_PATH
    assert manifest['parent']==binding['original_prefix']
    assert manifest['parent']['sha256']=='9a5c4af1e23964ee661e4e1ae427265a29303b2a6f6bd5a65c5ece14177040a3'
    assert sha(manifest['parent']['path'])==manifest['parent']['sha256']
    assert manifest['status']=='OPEN'and len(manifest['nodes'])==1
    node=manifest['nodes'][0]
    assert node['index']==0 and node['parent']is None and node['depth']==0
    assert node['restriction']is None and node['children']==[]and 'split'not in node
    assert node['status']=='OPEN'and node['file']==source['node_file']=='node_00000.json'
    assert node['sha256']==source['node_sha256']==sha(folder/node['file'])
    record=json.loads((folder/node['file']).read_text())
    assert record['id']==TARGET and record['original_path']==ORIGINAL_PATH
    assert record['status']=='OPEN'and 'terminal'not in record
    state=binding['state'];assert record['final']==state
    assert state['id']==TARGET and state['path']==ORIGINAL_PATH
    assert set(state)=={'id','path','angles','positions','scalar','differences','diagonal'}
    assert len(state['angles'])==9 and len(state['positions'])==18 and len(state['scalar'])==36
    for field in ('angles','positions','scalar'):
        assert all(F(a)<=F(b)for a,b in state[field])
    for field in ('differences','diagonal'):
        pairs=[tuple(row['pair'])for row in state[field]]
        assert len(pairs)==len(set(pairs))==36
        assert set(pairs)=={(i,j)for i in range(9)for j in range(i+1,9)}
        assert all(len(row['intervals'])==2 and all(F(a)<=F(b)for a,b in row['intervals'])for row in state[field])
    checker=binding['source_checker'];assert sha(checker['path'])==checker['sha256']==SOURCE_CHECKER_SHA
    assert Path(checker['path']).name=='verify_c887_global_union_height_consequence_tree.py'
    return binding

def assert_caller(state):
    assert state['id']==TARGET and state['path'][:len(ORIGINAL_PATH)]==ORIGINAL_PATH

def verify_literal(literal,caller,binding):
    assert_caller(caller);co,rhs,name=literal
    assert name.startswith(PREFIX+BINDING_SHA+'_')
    old=(co,rhs,LITERAL.PREFIX+name[len(PREFIX):])
    LITERAL.verify_literal(old,binding['state'],BINDING_SHA)
    return literal

def replay_source(output_folder):
    binding=verify_binding();output_folder=Path(output_folder).resolve()
    output_folder.mkdir(parents=True,exist_ok=True)
    output=output_folder/'whole_root_replay.json';log=output_folder/'whole_root_replay.log'
    with log.open('w')as stream:
        subprocess.run([sys.executable,'-B','-S',binding['source_checker']['path'],
            binding['original_prefix']['path'],binding['source_tree']['folder'],str(output)],
            check=True,stdout=stream,stderr=subprocess.STDOUT)
    result=json.loads(output.read_text())
    assert result['status']=='PASS_PARTIAL_WHOLE_ORIGINAL_C887_COVER'
    assert result['original_id']==TARGET and result['original_path']==ORIGINAL_PATH
    assert result['nodes']==result['leaf_domains']==1 and result['excluded_leaf_domains']==0
    assert result['complete_proxy_covers']==result['complete_sat_covers']==result['closed_angle_covers']==0
    assert result['height_exclusion_consequence_row_occurrences_checked']>0
    assert result['all_nine_original_squares_retained']is True and result['closed_shared_faces_retained']is True
    assert result['new_original_cells']==result['new_masks']==0
    verify_binding()
    return dict(status='PASS_FRESH_UNSPLIT_WHOLE_ORIGINAL_BOUND_STATE',binding_sha256=BINDING_SHA,
        source_report=dict(path=str(output),sha256=sha(output),report=result),
        original_id=TARGET,original_path=ORIGINAL_PATH,new_original_cells=0,new_masks=0),binding
