#!/usr/bin/env python3
"""Replay the delivered Cd402 ancestry union and eight terminal substitutions.

The compressed records are self-contained. The hash-bound native independent
checker runtime and its published legacy bases remain explicit dependencies;
this launcher does not claim cold or whole-original proof acceptance.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from collections import Counter
import argparse,hashlib,json,sys,tarfile,time

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def dump(path,value):path.write_text(json.dumps(value,indent=2)+'\n')

ap=argparse.ArgumentParser()
ap.add_argument('--packet',type=Path,default=Path(__file__).resolve().parent)
ap.add_argument('--native-c-family-root',type=Path,required=True)
ap.add_argument('--output',type=Path,required=True)
a=ap.parse_args()
assert __debug__
packet=a.packet.resolve();native=a.native_c_family_root.resolve();out=a.output.resolve()
assert native.is_dir() and not out.exists()
out.mkdir(parents=True)
started=time.monotonic()
archive_meta=json.loads((packet/'ARCHIVE_MANIFEST.json').read_text())
archive=packet/archive_meta['archive']
assert sha(archive)==archive_meta['sha256']
assert sha(packet/'PAYLOAD_SHA256.json')==archive_meta['inventory_sha256']
inventory=json.loads((packet/'PAYLOAD_SHA256.json').read_text())
with tarfile.open(archive,'r:xz')as tar:
    members=tar.getmembers()
    assert len(members)==archive_meta['regular_members']==len(inventory)
    assert all(m.isfile()and m.name.startswith('payload/')
               and not Path(m.name).is_absolute()and '..'not in Path(m.name).parts for m in members)
    assert len({m.name for m in members})==len(members)
    assert {m.name[len('payload/'):]for m in members}==set(inventory)
    tar.extractall(out/'inputs',filter='data')
payload=out/'inputs/payload'
for name,digest in inventory.items():assert sha(payload/name)==digest

native_meta=json.loads((packet/'NATIVE_DEPENDENCIES.json').read_text())
runtime_hashes={}
for item in native_meta['runtime_sources']:
    runtime_file=native.parent/item['relative_to_native_runs_root']
    snapshot=payload/item['payload_path']
    assert sha(snapshot)==item['sha256']==sha(runtime_file)
    runtime_hashes[str(runtime_file.resolve())]=item['sha256']
sys.path.insert(0,str(native));sys.path.insert(0,str(native/'source/ac_work/tree'))
import independent_c_general_rows_adapter as EXT
import check_cd402_complete_cover as CHECK

inputs=json.loads((payload/'INPUT_BINDINGS.json').read_text())
assert inputs['original_id']==CHECK.TARGET=='negative-d4021ade840b985c'
assert inputs['original_mask']=='001/00'
targets=set(inputs['target_indices']);assert targets=={40,41,471,472,478,479,486,487}
source=json.loads((payload/'evidence/SOURCE_MANIFEST.json').read_text())
grafted=json.loads((payload/'evidence/GRAFTED_MANIFEST.json').read_text())
receipt=json.loads((payload/'evidence/NEW_TERMINALS_EXACT_REPLAY.json').read_text())
assert receipt['source_manifest_sha256']==sha(payload/'evidence/SOURCE_MANIFEST.json')
assert receipt['grafted_manifest_sha256']==sha(payload/'evidence/GRAFTED_MANIFEST.json')
assert receipt['new_excluded']==8 and receipt['pending_before']==25 and receipt['pending_after']==17

def edge_key(e):
    if e is None:return None
    if e['kind']in('proxy','sat'):return e['kind'],tuple(e['pair']),tuple(e['choice'])
    assert e['kind']=='angle'
    return 'angle',e['owner'],F(e['cut']),e['choice']

def structure(manifest):
    entries=manifest['nodes'];nodes={n['index']:n for n in entries}
    pending={n['index']:n for n in manifest['pending']}
    assert len(nodes)==len(entries)and len(pending)==len(manifest['pending'])
    assert not(set(nodes)&set(pending))
    stopped={n['index']for n in manifest['stopped']}
    seen=set();leaves=set();covers=[]
    def walk(idx,parent=None,edge=None):
        assert idx not in seen
        seen.add(idx)
        n=nodes.get(idx,pending.get(idx));assert n is not None
        assert n['parent']==parent and edge_key(n['edge'])==edge_key(edge)
        if idx in pending:
            leaves.add(idx);return
        split=n.get('split');children=split['children']if split else[]
        if not children:
            assert n['status']=='CANDIDATE_CLOSED' or idx in stopped
            leaves.add(idx);return
        assert len(children)==len(set(children))
        child_entries=[nodes.get(i,pending.get(i))for i in children]
        assert all(child_entries)
        restrictions=[c['edge']for c in child_entries];kind=split['kind']
        if kind in('proxy','sat'):
            pair=tuple(split['pair'])
            assert len(pair)==2 and 0<=pair[0]<pair[1]<9
            expected=set(product((0,1),(-1,1)))if kind=='proxy'else set(product(pair,(0,1),(-1,1)))
            actual=[tuple(e['choice'])for e in restrictions]
            assert len(actual)==len(set(actual))==len(expected)and set(actual)==expected
            assert all(e['kind']==kind and tuple(e['pair'])==pair for e in restrictions)
        else:
            assert kind=='angle'and len(children)==2
            assert sorted(e['choice']for e in restrictions)==[0,1]
            assert all(e['kind']==kind and e['owner']==split['owner']and F(e['cut'])==F(split['cut'])for e in restrictions)
        covers.append(idx)
        for i,e in zip(children,restrictions):walk(i,idx,e)
    walk(0)
    assert seen==set(nodes)|set(pending)
    return nodes,pending,covers

nodes,pending,covers=structure(source)
gn,gp,gc=structure(grafted)
assert set(gn)==set(nodes)|targets
assert set(gp)==set(pending)-targets
assert len(covers)==len(gc)==141
for idx,n in nodes.items():
    for key in('index','parent','edge','depth','file','split'):
        assert n.get(key)==gn[idx].get(key)
for idx,n in pending.items():
    if idx not in targets:assert n==gp[idx]

inherited=json.loads((payload/'evidence/INHERITED_NODE_SHA256.json').read_text())
needed={int(k)for k in inputs['ancestral_inputs']}
assert needed=={0,3,4,12,14,16,52,467,470,476}
for idx in targets:
    chain=[];parent=pending[idx]['parent']
    while parent is not None:
        chain.append(parent);parent=nodes[parent]['parent']
    assert list(reversed(chain))==inputs['ancestral_chains'][str(idx)]
for idx in needed:
    item=inputs['ancestral_inputs'][str(idx)]
    assert sha(payload/item['payload_path'])==item['sha256']==inherited[item['original_path']]
for idx in targets:
    item=inputs['terminal_inputs'][str(idx)]
    assert sha(payload/item['payload_path'])==item['sha256']

checker=CHECK.BASE.Checker()
adapter=EXT.extend_adapter(CHECK.Adapter,allow_rotating=True)(checker)
CHECK.BASE.verify_all_bindings()
original_input=inputs['original_bound_input']
assert original_input['sha256']==CHECK.ORIGINAL_SHA
CHECK.ORIGINAL=payload/original_input['payload_path']
register_input=inputs['original_register']
assert sha(payload/register_input['payload_path'])==CHECK.REGISTER_SHA
bindings={}
root_audit,root_state,original_source_map=CHECK.original_state(adapter,bindings)
assert CHECK.CORE.state_view(root_state)==source['original']==grafted['original']
assert sha(CHECK.ORIGINAL)==original_input['sha256']
print('ORIGINAL_BOUND_PASS',root_audit,flush=True)

audits=[];visited=set();proved=set()
def child_state(after,edge):
    if edge['kind']=='proxy':
        return CHECK.PROXY.proxy_child(after,tuple(edge['pair']),edge['choice'],adapter)
    if edge['kind']=='sat':
        return CHECK.CORE.sat_child(after,tuple(edge['pair']),edge['choice'],adapter)
    return CHECK.angle_child(after,edge['owner'],F(edge['cut']),edge['choice'],adapter)

def visit(idx,initial):
    assert idx not in visited
    visited.add(idx)
    if idx in targets:
        assert CHECK.CORE.state_view(initial)==pending[idx]['state']
        entry=inputs['terminal_inputs'][str(idx)]
        record=json.loads((payload/entry['payload_path']).read_text())
        audit,after=CHECK.CORE.check_record(record,initial,adapter)
        assert after is None
        proved.add(idx);kind='new_terminal'
    else:
        assert idx in needed
        entry=inputs['ancestral_inputs'][str(idx)]
        record=json.loads((payload/entry['payload_path']).read_text())
        audit,after=CHECK.CORE.check_record(record,initial,adapter)
        assert after is not None
        kind='saved_ancestor'
        n=nodes[idx];assert n['depth']==len(initial['path'])-3
        children=n['split']['children']
        for child_idx in children:
            if child_idx not in needed and child_idx not in targets:continue
            child=nodes.get(child_idx,pending.get(child_idx))
            assert child is not None and child['parent']==idx
            visit(child_idx,child_state(after,child['edge']))
    audits.append(dict(index=idx,kind=kind,payload_record=entry['payload_path'],sha256=entry['sha256'],audit=audit))
    print('REPLAYED',idx,kind,audit['status'],audit.get('deductions',0),flush=True)
visit(0,root_state)
assert visited==needed|targets and proved==targets

hand=json.loads((payload/'evidence/NODE41_HAND_CANCELLATION.json').read_text())
terminal=json.loads((payload/inputs['terminal_inputs']['41']['payload_path']).read_text())
assert hand['source_record_sha256']==inputs['terminal_inputs']['41']['sha256']
assert hand['source_rows']==terminal['terminal']['rows']
weights=list(map(F,hand['weights']));assert len(weights)==len(hand['source_rows'])==5 and all(w>=0 for w in weights)
coeff={};rhs=F(0)
for row,w in zip(hand['source_rows'],weights):
    rhs+=w*F(row['rhs'])
    for k,c in row['coefficients']:coeff[k]=coeff.get(k,F(0))+w*F(c)
assert all(c==0 for c in coeff.values())and rhs<0
assert rhs==F(hand['summed_rhs']) and -rhs==F(hand['reserve'])

EXT.no_producers()
assert not any(name in sys.modules for name in('numpy','scipy','highspy','physical_sat_engine_snapshot','physical_sat_diagonal_engine'))
for name,digest in inventory.items():assert sha(payload/name)==digest
for name,digest in runtime_hashes.items():assert sha(name)==digest
for name,digest in bindings.items():assert sha(name)==digest
CHECK.BASE.verify_all_bindings()
dependencies={str(Path(m.__file__).resolve()):sha(m.__file__)for m in tuple(sys.modules.values())
    if getattr(m,'__file__',None)and Path(m.__file__).is_file()
    and '/research/nine/.runs/'in str(Path(m.__file__).resolve())}
report=dict(schema='Cd402_native_eight_terminal_ancestry_delta_replay_v1',
    status='PASS_NATIVE_ANCESTRY_AND_EIGHT_TERMINAL_SUBSTITUTIONS',
    original_id=CHECK.TARGET,original_path=CHECK.ROOT_PATH,original_mask='001/00',squared_radius='1105/256',
    all_nine_originals_retained=True,all_36_corners_and_pairs_retained=True,
    original_bound_replayed=root_audit,ancestral_records_replayed=len(needed),new_terminals_replayed=len(proved),
    record_audits=audits,complete_child_covers_checked=len(covers),
    total_bound_deductions=root_audit['deductions']+sum(v['audit']['deductions']for v in audits),
    printed_rows_checked=root_audit['printed_rows_checked']+sum(v['audit']['printed_rows_checked']for v in audits),
    new_terminal_rows_checked=sum(v['audit']['printed_rows_checked']for v in audits if v['kind']=='new_terminal'),
    pending_before=25,pending_after=17,exact_cancelling_hand_table_reserve=str(-rhs),
    untouched_old_node_arithmetic_replayed=False,whole_original_excluded=False,
    native_runtime_required=True,cold_standalone_proof=False,
    numerical_modules_or_producers_imported=False,lean_lake_ci_run=False,
    archive_sha256=archive_meta['sha256'],payload_inventory_sha256=archive_meta['inventory_sha256'],
    launcher_sha256=sha(__file__),original_source_relocation=original_source_map,
    original_input_sha256=bindings,native_runtime_source_sha256=runtime_hashes,
    actual_checker_dependency_sha256=dependencies,new_row_counts=EXT.COUNTS,
    new_original_cells=0,new_masks=0,seconds=time.monotonic()-started)
dump(out/'NATIVE_REPLAY.json',report)
print(json.dumps({k:v for k,v in report.items()if k not in('record_audits','original_source_relocation','original_input_sha256','native_runtime_source_sha256','actual_checker_dependency_sha256')}),flush=True)
