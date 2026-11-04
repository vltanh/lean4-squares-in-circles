"""Fresh component-3 source proof with strict conditional consumer binding."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,subprocess,sys
import independent_certified_union_original_rows as LITERAL

HERE=Path(__file__).resolve().parent
BINDING=HERE/'A_C744_COMPONENT3_POST_A1_BOUND_STATE_BINDING.json'
BINDING_SHA='338e53440f35ab321c126d6050f9de36c89a0424141ea6e1f6ba2fa6b756c23d'
PREFIX='certified_a_c744_component3_post_a1_root_bound_'
TARGET='positive-c744bc031d40ee64'
ORIGINAL_PATH=[['angle',3,1],['angle_cut',[0,'0'],0],['inward_row_escape',[7,8],[4]]]
SCOPE='ONE_CLOSED_MEMBER_OF_THE_COMPLETE_ACTUAL_AB_FIVE_COVER'
COMPONENT_SHA='170686e1f4cfa0a85ca6616492630326a4096001c0662e207827e820c01dc4b7'
WHOLE_PARENT_SHA='68aae2029165b1148d0b719ac962e7c50c649afd8fcee6bfba4af99f50f85893'
SOURCE_CHECKER_SHA='ee3467864672770b206fe2931e4b7100c6e110d8722e78acf3354abd8c35386d'
CLOSED_DOMAIN=dict(name='two_link_actual_AB_escape_3',coefficients=[[3,'1'],[7,'1'],[17,'-2']],rhs='-3/5')

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def verify_binding():
    assert sha(BINDING)==BINDING_SHA;binding=json.loads(BINDING.read_text())
    assert binding['schema']=='A_c744_component3_post_complete_A1_unsplit_bound_state_v1'
    assert binding['original_id']==TARGET and binding['original_path']==ORIGINAL_PATH
    assert type(binding['component'])is int and binding['component']==3 and binding['scope']==SCOPE
    assert binding['mask']=='001/00'and binding['squared_radius']=='1105/256'
    assert binding['valid_on_whole_original']is False
    assert binding['forbidden_consumer_components']==[0,1,2,4]
    for field in ('one_unsplit_complete_component3_node','no_new_child_restrictions_or_auxiliary_bounds_transported',
        'all_nine_originals_retained','closed_shared_faces_retained'):assert binding[field]is True
    assert binding['new_original_cells']==binding['new_masks']==0
    assert binding['closed_domain']==CLOSED_DOMAIN
    component=binding['component_parent'];assert component['sha256']==COMPONENT_SHA==sha(component['path'])
    assert component['schema']=='AC_named_closed_two_link_complement_bound_discovery_v1'
    original=binding['conditional_parent'];assert original['sha256']==WHOLE_PARENT_SHA==sha(original['path'])
    original_record=json.loads(Path(original['path']).read_text())
    assert original_record['id']==TARGET and original_record['original_path']==ORIGINAL_PATH
    assert original_record['scope']=='WHOLE_UNCHANGED_ORIGINAL_PARENT'
    conditional=json.loads(Path(component['path']).read_text())
    assert conditional['schema']==component['schema']
    assert conditional['component']==3 and conditional['closed_domain']==CLOSED_DOMAIN
    assert conditional['parent']==original
    source=binding['source_tree'];folder=Path(source['folder'])
    assert sha(folder/'manifest.json')==source['manifest_sha256']
    manifest=json.loads((folder/'manifest.json').read_text())
    assert manifest['schema']=='same_original_physical_SAT_proxy_angle_tree_discovery_v1'
    assert manifest['id']==TARGET and manifest['original_path']==ORIGINAL_PATH
    assert manifest['scope']==SCOPE and manifest['component']==3
    assert manifest['parent']==component and manifest['conditional_parent']==original
    assert manifest['closed_domain']==CLOSED_DOMAIN
    assert manifest['status']=='OPEN'and len(manifest['nodes'])==1
    node=manifest['nodes'][0]
    assert node['index']==0 and node['parent']is None and node['depth']==0
    assert node['restriction']is None and node['children']==[]and 'split'not in node
    assert node['status']=='OPEN'and node['file']==source['node_file']=='node_00000.json'
    assert node['sha256']==source['node_sha256']==sha(folder/node['file'])
    record=json.loads((folder/node['file']).read_text())
    assert record['id']==TARGET and record['original_path']==ORIGINAL_PATH
    assert record['status']=='OPEN'and 'terminal'not in record
    assert record['initial']==conditional['record']['final']
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
    assert Path(checker['path']).name=='verify_a_c744_component3_a1_consequence_lazy_tree.py'
    assert binding['source_checker_precedes_new_rows'] is True
    assert binding['saved_source_report_not_a_premise'] is True
    previous=binding['preceding_conditional_bound_binding']
    assert previous['sha256']=='c27b8690fc4fcd096cfcc2efc8776c2b51106762e94ad724de7e57c2a78db574'
    assert sha(previous['path'])==previous['sha256']
    assert manifest['component3_shared_bound_state']==dict(path=previous['path'],sha256=previous['sha256'],component=3)
    consequence=binding['completed_component1_consequence']
    assert consequence==manifest['component1_closed_consequence']
    assert consequence['sha256']=='5c46eb3c5e3c60e9e776dd52db041cff92d0718c12feb040b9ada0fc745a801a'
    assert consequence['source_component']==1 and consequence['scope']=='WHOLE_UNCHANGED_ORIGINAL_PARENT'
    assert sha(consequence['path'])==consequence['sha256']
    assert 'component3_post_a1_bound_state' not in manifest
    def no_new_prefix(value):
        if isinstance(value,dict):
            assert not (isinstance(value.get('name'),str) and value['name'].startswith(PREFIX))
            for child in value.values():no_new_prefix(child)
        elif isinstance(value,list):
            for child in value:no_new_prefix(child)
    no_new_prefix(record)
    return binding

def assert_consumer(component,scope,parent,conditional_parent,closed_domain,binding):
    assert type(component)is int and component==3
    assert scope==SCOPE
    assert parent==binding['component_parent']
    assert conditional_parent==binding['conditional_parent']
    assert closed_domain==binding['closed_domain']==CLOSED_DOMAIN

def assert_caller(state):
    assert state['id']==TARGET and state['path'][:len(ORIGINAL_PATH)]==ORIGINAL_PATH

def verify_literal(literal,state,consumer,binding):
    assert_consumer(consumer['component'],consumer['scope'],consumer['parent'],
        consumer['conditional_parent'],consumer['closed_domain'],binding)
    assert_caller(state);co,rhs,name=literal
    assert name.startswith(PREFIX+BINDING_SHA+'_')
    LITERAL.verify_literal((co,rhs,LITERAL.PREFIX+name[len(PREFIX):]),binding['state'],BINDING_SHA)
    return literal

def replay_source(output_folder):
    binding=verify_binding();output_folder=Path(output_folder).resolve()
    output_folder.mkdir(parents=True,exist_ok=True)
    output=output_folder/'component3_root_replay.json';log=output_folder/'component3_root_replay.log'
    with log.open('w')as stream:
        subprocess.run([sys.executable,'-B','-S',binding['source_checker']['path'],
            binding['source_tree']['folder'],str(output)],check=True,stdout=stream,stderr=subprocess.STDOUT)
    report=json.loads(output.read_text())
    assert report['status']=='PASS_PARTIAL_TWO_LINK_COMPLEMENT_TREE'
    assert report['original_id']==TARGET and report['original_path']==ORIGINAL_PATH
    assert report['component']==3 and report['closed_domain']==CLOSED_DOMAIN
    assert report['conditional_parent']==binding['conditional_parent']
    assert report['nodes']==report['leaf_domains']==report['open_leaves']==1
    assert report['excluded_leaves']==0 and report['closed_unions']=={}
    assert report['all_nine_originals_retained']is True and report['closed_shared_faces_retained']is True
    assert report['new_original_cells']==report['new_masks']==0
    assert report['rounds']==7 and report['deductions']==565 and report['printed_rows_checked']==1436
    assert report['completed_component1_consequence_occurrences_checked']==2
    fresh=report['fresh_completed_component1_consequence_source']
    assert fresh['status']=='PASS_FRESH_COMPLETE_COMPONENT1_ORIGINAL_CONSEQUENCE'
    assert fresh['excluded_component']==1 and fresh['source_report']['report']['open_leaves']==0
    verify_binding()
    return dict(status='PASS_FRESH_UNSPLIT_A_C744_COMPONENT3_POST_A1_BOUND_STATE',binding_sha256=BINDING_SHA,
        source_report=dict(path=str(output),sha256=sha(output),report=report),
        original_id=TARGET,original_path=ORIGINAL_PATH,component=3,scope=SCOPE,
        valid_on_whole_original=False,new_original_cells=0,new_masks=0),binding
