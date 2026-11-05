"""Explicit reuse of complete accepted A1-publication proof dependencies.

No lost receipt is recreated. Embedded full report objects are checked against
both their original hashes and every surviving input/decoder hash. The caller
freshly replays its own weighted record with the unchanged exact arithmetic.
"""
if not __debug__:raise RuntimeError('Historical proof identity checks require assertions.')
from pathlib import Path
from copy import deepcopy
import hashlib,json,sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
sys.path.insert(0,str(ROOT/'ac_work/tree'))
import independent_a_c744_component3_post_a1_bound_rows as POST
import independent_a_c744_component3_shared_bound_rows as SHARED
import independent_a_c744_component1_consequence as A1
import independent_a_c744_complement_consequences as COMPLEMENTS
TARGET='positive-c744bc031d40ee64'
ORIGINAL_PATH=[['angle',3,1],['angle_cut',[0,'0'],0],['inward_row_escape',[7,8],[4]]]
BINDING=HERE/'HISTORICAL_PROOF_BINDING.json'

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def read(path):return json.loads(Path(path).read_text())
def embedded_reference(ref):
    # This computes the hash of bytes already fully represented in the
    # published outer report. It writes no historical receipt or proof record.
    assert set(ref)=={'path','sha256','report'}
    raw=(json.dumps(ref['report'],indent=2)+'\n').encode()
    assert hashlib.sha256(raw).hexdigest()==ref['sha256']
    return ref['report']

def check_common(report):
    assert report['original_id']==TARGET and report['original_path']==ORIGINAL_PATH
    assert report['all_nine_originals_retained']is True and report['closed_shared_faces_retained']is True
    assert report['new_original_cells']==report['new_masks']==0
    assert report['mask']=='001/00'

def check_open_source(report,binding,counts):
    check_common(report)
    assert report['status']=='PASS_PARTIAL_TWO_LINK_COMPLEMENT_TREE'
    assert report['component']==3 and report['closed_domain']==POST.CLOSED_DOMAIN
    assert report['conditional_parent']==binding['conditional_parent']
    assert (report['nodes'],report['leaf_domains'],report['excluded_leaves'],report['open_leaves'])==(1,1,0,1)
    assert report['closed_unions']=={}
    assert tuple(report[k]for k in('rounds','deductions','printed_rows_checked'))==counts
    tree=binding['source_tree'];mp=str(Path(tree['folder'])/'manifest.json')
    assert report['input_sha256'][mp]==tree['manifest_sha256']
    assert report['input_sha256'][str(Path(tree['folder'])/tree['node_file'])]==tree['node_sha256']

def check_complete_source(report,component,tree,counts,closed_domain):
    check_common(report)
    assert report['status']=='PASS_COMPLETE_TWO_LINK_COMPLEMENT_TREE'
    assert report['component']==component and report['closed_domain']==closed_domain
    assert tuple(report[k]for k in('nodes','leaf_domains','excluded_leaves','open_leaves','rounds','deductions','printed_rows_checked'))==counts
    folder=Path(tree['folder']);mp=folder/'manifest.json'
    assert sha(mp)==tree['manifest_sha256']==report['input_sha256'][str(mp)]
    manifest=read(mp)
    assert manifest['id']==TARGET and manifest['original_path']==ORIGINAL_PATH
    assert manifest['component']==component and manifest['closed_domain']==closed_domain
    assert manifest['status']=='CANDIDATE_COVER_CLOSED'
    for node in manifest['nodes']:
        path=folder/node['file'];raw=path.read_bytes()
        assert hashlib.sha256(raw).hexdigest()==node['sha256']==report['input_sha256'][str(path)]
        assert b'stronger_actual_ab_064_A_c744_I_high'not in raw
        assert b'certified_a_c744_original_064_'not in raw

def validate():
    binding=read(BINDING)
    assert binding['schema']=='historically_accepted_A1_complete_source_reuse_v2'
    assert binding['original_id']==TARGET and binding['original_path']==ORIGINAL_PATH
    assert binding['lost_receipts_used']is False and binding['source_arithmetic_repeated']is False
    for path,h in binding['source_sha256'].items():assert sha(path)==h,path
    ref=binding['published_outer_report'];assert sha(ref['path'])==ref['sha256']=='5c14a5ee853378adf31fcb56665bafa0c98656eec9bab0ca27ba596c03dc826d'
    outer=read(ref['path'])
    post_binding=POST.verify_binding();shared_binding=SHARED.verify_binding()
    a1_binding=A1.verify_binding();complement_binding=COMPLEMENTS.verify_binding()
    check_open_source(outer,post_binding,(7,565,1436))
    assert outer['completed_component1_consequence_occurrences_checked']==2
    shared=outer['fresh_component3_shared_bound_source']
    a1=outer['fresh_completed_component1_consequence_source']
    complements=outer['freshly_replayed_original_complement_consequences']
    assert shared['binding_sha256']==SHARED.BINDING_SHA and shared['component']==3
    assert shared['valid_on_whole_original']is False and shared['scope']==SHARED.SCOPE
    shared_report=embedded_reference(shared['source_report'])
    check_open_source(shared_report,shared_binding,(4,446,1025))
    assert a1['binding_sha256']==A1.BINDING_SHA and a1['excluded_component']==1
    assert a1['necessary_weak_row']==a1_binding['necessary_weak_row']
    a1_report=embedded_reference(a1['source_report'])
    check_complete_source(a1_report,1,a1_binding['source_tree'],(757,566,566,0,230,74846,134855),a1_binding['excluded_closed_domain'])
    assert complements['binding_sha256']==COMPLEMENTS.BINDING_SHA and complements['excluded_components']==[0,2,4]
    declaration,zero=[embedded_reference(x)for x in complements['source_reports']]
    assert declaration['status']=='PASS_COMPLETE_DECLARATION_WITH_OPEN_COMPLEMENTS'
    assert declaration['original_id']==TARGET and declaration['original_path']==ORIGINAL_PATH
    assert declaration['all_nine_original_squares_retained']is True and declaration['all_shared_faces_retained']is True
    assert declaration['original_mask']=='001/00'and declaration['original_corner_predicates']==declaration['original_pair_predicates']==36
    assert declaration['all_five_closed_complements_present']is True
    assert declaration['excluded_complement_domains']==2 and declaration['open_complement_domains']==3
    assert [x['component']for x in declaration['component_audits']]==list(range(5))
    assert [x['component']for x in declaration['component_audits']if x['status']=='PASS_EXCLUDED_PHYSICAL_DOMAIN']==[2,4]
    assert [i for i,x in enumerate(declaration['final_states'])if x is None]==[2,4]
    for entry in complement_binding['consequences']:
        assert declaration['component_audits'][entry['component']]['closed_domain']==entry['excluded_closed_domain']
    assert declaration['new_original_cells']==declaration['new_masks']==0
    zero_domain=next(x for x in complement_binding['consequences']if x['component']==0)['excluded_closed_domain']
    check_complete_source(zero,0,complement_binding['component0_proof'],(41,31,31,0,6,1154,1385),zero_domain)
    assert binding['embedded_report_sha256']=={
        'shared_four':shared['source_report']['sha256'],'complete_A1':a1['source_report']['sha256'],
        'five_declaration':complements['source_reports'][0]['sha256'],
        'complete_component0':complements['source_reports'][1]['sha256']}
    reports=[outer,shared_report,a1_report,declaration,zero]
    actual={}
    for report in reports:
        for field in('input_sha256','checker_dependency_sha256','source_sha256'):
            for path,h in report.get(field,{}).items():
                if path in actual:assert actual[path]==h
                actual[path]=h
    assert actual==binding['historical_report_inputs']
    for path,h in actual.items():assert sha(path)==h,path
    post=dict(status='PASS_HISTORICALLY_ACCEPTED_UNSPLIT_A_C744_COMPONENT3_POST_A1_BOUND_STATE',binding_sha256=POST.BINDING_SHA,
        source_report=dict(path=ref['path'],sha256=ref['sha256'],report=outer),
        original_id=TARGET,original_path=ORIGINAL_PATH,component=3,scope=POST.SCOPE,
        valid_on_whole_original=False,source_arithmetic_repeated=False,new_original_cells=0,new_masks=0)
    evidence=dict(status='PASS_HISTORICALLY_ACCEPTED_PUBLISHED_PROOF_IDENTITIES',
        binding_sha256=sha(BINDING),published_outer_report=ref,
        embedded_reports=binding['embedded_report_sha256'],source_files=len(binding['source_sha256']),
        historical_report_inputs=len(actual),complete_component0_nodes=41,complete_component1_nodes=757,
        complete_component0_closed_leaves=31,complete_component1_closed_leaves=566,
        source_arithmetic_repeated=False,new_receipts_recreated=False,lost_receipts_used=False,
        old_component3_conditional_scope_preserved=True,new_original_cells=0,new_masks=0)
    return evidence,dict(post=(post,post_binding),shared=(shared,shared_binding),a1=a1,complements=complements)

class InstalledCache:
    def __init__(self,cache):self.cache=cache;self.calls=dict(post=0,shared=0,a1=0,complements=0);self.previous=[]
    def __enter__(self):
        for key,module,name in(('post',POST,'replay_source'),('shared',SHARED,'replay_source'),('a1',A1,'replay_source'),('complements',COMPLEMENTS,'replay_source_exclusions')):
            old=getattr(module,name);self.previous.append((module,name,old))
            def cached(output,key=key,module=module):
                module.verify_binding();self.calls[key]+=1
                return deepcopy(self.cache[key])
            setattr(module,name,cached)
        return self
    def __exit__(self,*ignored):
        for module,name,function in self.previous:setattr(module,name,function)
