#!/usr/bin/env python3
"""Independent source/complete-cover/literal audit of the actual LP pilot."""
if not __debug__:
    raise RuntimeError('Exact pilot audit requires assertions.')
from pathlib import Path
from hashlib import sha256
from fractions import Fraction as F
from itertools import product
import importlib.util
import json
import sys

W=Path('/workspace/scratch/f9f48fcfb253')
HERE=Path(__file__).resolve().parent
CHECKPOINT=W/'global_work/strict_011_rebuilt_v3'
RUN=W/'repo/research/nine/.runs/strict011_representative_first_real_phase_v1'

def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def load(name,path,expected):
    assert digest(path)==expected
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module

assert digest(CHECKPOINT/'CHECKPOINT_MANIFEST.json')=='ac389f6184af6503294a13fb30c1da82e38d052a5d579bf43ccd4a0017b0485b'
manifest_path=RUN/'manifest.json'
assert digest(manifest_path)=='94dacdafea838579c1bf81b74b64685a2729679549173ef47ee67a3310e84a78'
assert digest(RUN/'EXACT_REPLAY.json')=='81ffe31f37cdd26b4b8ac957381c0438e66f0019c1cdabe81d50595ab68e8545'
assert digest(RUN/'DISCOVERY_COMPLETION.json')=='b66a5e5f0ad983078f6154b81615d06cdba79ff424c9092db338112cd9f6025d'
source=json.loads((RUN/'DISCOVERY_SOURCE_BINDING.json').read_text())
assert source['driver_sha256']=='58a85d7976aff42bbda10137f0c951985c674e220568f93d9244dfdf1b92275e'
assert source['root_id']=='full-strict-01100-representative-root-v1'
assert source['mask']=='011/00' and source['radius_mode']=='strict'
assert source['physical_originals']==9 and source['original_corners']==source['original_pairs']==36 and source['marked_cones']==5
I=load('first_actual_independent_root',CHECKPOINT/'strict_011_representative_root_v1/independent_strict_011_adapter.py',
       'c575144623b13c55fc3e57ed9bd17d1a90415991f5ddf3bdf0540f8ea8b69068')
G=load('first_actual_exact_core',CHECKPOINT/'dependencies/workspace/b_work/independent_physical_sat_replay.py',
       '1d069c90f289dce136e41afeb5d564ec7016ac06f58eeb733ca7552801b6fafc')
X=load('first_actual_proxy_core',CHECKPOINT/'dependencies/workspace/b_work/independent_physical_proxy_cover.py',
       '3b46b8a966c712e23894ae4cd7964355730f2bfe3c58a04871ade9d35ddf1277')
manifest=json.loads(manifest_path.read_text())
assert set(manifest)=={'schema','root_document','root','nodes'}
assert manifest['schema']=='fresh_full_strict011_representative_complete_tree_v1'
root_document=RUN/manifest['root_document']['file']
assert digest(root_document)==manifest['root_document']['sha256']
state=I.verify_root(json.loads(root_document.read_text()))
entries={e['id']:e for e in manifest['nodes']}
assert len(entries)==len(manifest['nodes'])==5
records={}
hashes={}
for node,e in entries.items():
    p=RUN/e['file'];assert p.resolve().is_relative_to(RUN)
    assert digest(p)==e['sha256'];records[node]=json.loads(p.read_text());hashes[str(p)]=digest(p)
root=entries[manifest['root']]
audit,parent=G.check_record(records[manifest['root']],state,I.Adapter())
assert parent==state
split=root['split'];assert split['kind']=='proxy' and split['pair']==[0,1]
choices=[tuple(c['choice']) for c in split['children']]
assert len(choices)==4 and set(choices)==set(product((0,1),(-1,1)))
assert {c['node'] for c in split['children']}==set(entries)-{manifest['root']}
audits=[];closed=[]
for child in split['children']:
    node=child['node'];assert 'split' not in entries[node]
    expected=X.proxy_child(state,[0,1],child['choice'],I.Adapter())
    a,s=G.check_record(records[node],expected,I.Adapter())
    audits.append(dict(node=node,choice=child['choice'],audit=a))
    if s is None:closed.append(node);assert child['choice']==[0,-1]
assert len(closed)==1
terminal=records[closed[0]]['terminal']
assert records[closed[0]]['rounds']==[]
expected_rows={
    'strict011v2:inset_tangent:0:1':({18:F(-1,2),36:F(-1,2),45:F(-1)},F(-1)),
    'strict011v2:inset_tangent:1:1':({19:F(-1,2),37:F(-1,2),46:F(-1)},F(-1)),
    'strict011v2:mask:0:1:0':({0:F(1),2:F(-1),18:F(1,2),36:F(1,2),19:F(1,2),37:F(1,2)},F(0)),
    'strict011v2:proxy:0:1:0:-1':({0:F(-1),2:F(1),45:F(1),46:F(1)},F(0))}
assert {r['name'] for r in terminal['rows']}==set(expected_rows)
by_index={}
for row in terminal['rows']:
    terms={k:F(v) for k,v in row['coefficients']}
    assert len(terms)==len(row['coefficients'])
    assert (terms,F(row['rhs']))==expected_rows[row['name']]
    assert row['index'] not in by_index;by_index[row['index']]=row
assert len(terminal['weights'])==4 and {k for k,w in terminal['weights']}==set(by_index)
bounds=list(map(F,terminal['absolute_variable_bounds']));assert len(bounds)==54 and all(b>=0 for b in bounds)
coefficients=[F(0)]*54;rhs=F(0)
for index,weight in terminal['weights']:
    assert type(weight) is int and weight==274877906944
    factor=F(weight,1<<40);assert factor==F(1,4)
    row=by_index[index];rhs+=factor*F(row['rhs'])
    for column,value in row['coefficients']:coefficients[column]+=factor*F(value)
assert not any(coefficients) and rhs==F(-1,2)
payment=sum(b*abs(c) for b,c in zip(bounds,coefficients))
reserve=-rhs-payment
assert payment==0 and reserve==F(1,2)
assert terminal['weighted_coefficients']==list(map(str,coefficients))
assert F(terminal['weighted_rhs'])==rhs and F(terminal['reserve'])==reserve
for p,expected in hashes.items():assert digest(p)==expected
assert not any(n.split('.')[0] in {'numpy','scipy','z3','sympy','highspy'} for n in sys.modules)
result=dict(status='PASS_INDEPENDENT_ACTUAL_LP_PILOT_COMPLETE_COVER_AND_LITERAL_DUAL_AUDIT',
    actual_process_exit_reported_by_root=dict(session=14074,exit_code=0),
    root_id=state['id'],mask='011/00',radius_mode='strict',nodes=5,excluded_leaves=1,open_leaves=3,
    full_original_inventory=dict(squares=9,corners=36,pairs=36,marked_cones=5),
    manifest_sha256=digest(manifest_path),actual_exact_report_sha256=digest(RUN/'EXACT_REPLAY.json'),
    actual_completion_sha256=digest(RUN/'DISCOVERY_COMPLETION.json'),
    actual_source_binding_sha256=digest(RUN/'DISCOVERY_SOURCE_BINDING.json'),
    node_input_sha256=hashes,exact_child_audits=audits,
    nonzero_weights=4,each_normalized_weight='1/4',weighted_rhs=str(rhs),reserve=str(reserve),
    residual_nonzero_columns=0,residual_absolute_bound_payment=str(payment),
    actual_nonzero_residual_exercised=False,numerical_solver_called_by_this_audit=False,
    source_script_sha256=digest(Path(__file__)),hand_review_sha256=digest(HERE/'ACTUAL_LP_FIRST_USE_HAND_REVIEW.md'),
    whole_mask_proved=False,original_cell_credit=0,whole_mask_credit=0)
out=HERE/'ACTUAL_LP_FIRST_USE_REVIEW.json'
with out.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps(dict(status=result['status'],nonzero_weights=4,reserve=str(reserve),
    residual_payment=str(payment),report=str(out),sha256=digest(out))))
