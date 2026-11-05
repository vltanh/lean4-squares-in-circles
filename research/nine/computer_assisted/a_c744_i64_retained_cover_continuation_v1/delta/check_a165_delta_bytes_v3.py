#!/usr/bin/env python3
"""Check the complete native delta's bytes, report identities, and old-prefix attachment.

This does not repeat any rational weighted-row arithmetic.
"""
if not __debug__:
    raise RuntimeError('Assertions are required.')
from pathlib import Path
import argparse
import hashlib
import json

EXPECTED_INPUT = '274e0ab65d290d61b8dee91146e2e4f2ee3316ece91bc19bbe05d6afb4e43805'
EXPECTED_REPORT = '98bc7f287f1eb62e0a132437d808c48121a017317adde4ea9083f83364d2ad8f'
EXPECTED_TREE = '4469ce8ceda7692f49faa58ece25872c0448fbd8fc86447acb6facf0cd4e2283'
EXPECTED_OLD = 'a8f67d1de94a9a8eac0034b3a85f77d971fff500de3ea73d2458501246a3a1ad'
CHANGED = (144,145,146,148,149,151,152,154,155,156,157,158,159,160,161,163,164)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(path):
    return json.loads(path.read_text())

def safe(folder, name):
    p = Path(name)
    assert not p.is_absolute() and p.parts and all(x not in ('.','..') for x in p.parts)
    out = folder / p
    assert out.resolve().is_relative_to(folder) and out.is_file() and not out.is_symlink()
    return out

def check(folder, base):
    folder, base = folder.resolve(), base.resolve()
    manifest_path = folder/'INPUT_MANIFEST.json'
    assert sha(manifest_path) == EXPECTED_INPUT
    inventory = read(manifest_path)['files']
    assert not any(p.is_symlink() for p in folder.rglob('*'))
    assert {str(p.relative_to(folder)) for p in folder.rglob('*') if p.is_file()} == set(inventory)|{'INPUT_MANIFEST.json'}
    pins = {str(manifest_path): EXPECTED_INPUT}
    for name, entry in inventory.items():
        p = safe(folder,name)
        assert p.stat().st_size == entry['bytes'] and sha(p) == entry['sha256'], name
        pins[str(p)] = entry['sha256']
    report_path = folder/'reports/A165_I64_EXACT_CONTINUATION_REPLAY_V1.json'
    assert sha(report_path) == EXPECTED_REPORT
    report = read(report_path)
    old = read(folder/'SOURCE_MANIFEST.json')
    tree = read(folder/'tree/manifest.json')
    assembly = read(folder/'TREE_ASSEMBLY.json')
    assert sha(folder/'SOURCE_MANIFEST.json') == EXPECTED_OLD == report['source_manifest_sha256']
    assert sha(folder/'tree/manifest.json') == EXPECTED_TREE == report['continued_manifest_sha256']
    assert report['status'] == 'PASS_A165_I64_COMPLETE_RETAINED_COVER_OPEN'
    assert report['all165_nodes_freshly_replayed'] is True
    for key in ('new_original_cells','new_masks','numerical_solves'):
        assert report[key] == 0
    assert report['cold_portable_replay_claimed'] is False
    assert report['historical_A1_and_source_arithmetic_repeated'] is False
    assert report['fresh813_source_repeated'] is False
    assert (report['nodes'],report['leaf_domains'],report['excluded_leaves'],report['open_leaves']) == (165,132,118,14)
    inner_path = folder/'reports'/Path(report['inherited_complete_arithmetic_report']['path']).name
    assert sha(inner_path) == report['inherited_complete_arithmetic_report']['sha256']
    inner = read(inner_path)
    for key in ('nodes','leaf_domains','excluded_leaves','open_leaves','rounds','deductions','printed_rows_checked'):
        assert inner[key] == report[key], key
    observed = read(folder/'reports/A165_I64_FULL_REPLAY_OBSERVED_EXIT_V1.json')
    assert observed['observed_session_id'] == 20956 and observed['observed_process_exit_code'] == 0
    assert observed['complete_consumer_replay_report']['sha256'] == EXPECTED_REPORT
    assert observed['inherited_consumer_report']['sha256'] == sha(inner_path)
    assert observed['execution_log']['sha256'] == sha(folder/'reports/A165_I64_EXACT_CONTINUATION_REPLAY_V1.log')
    assert observed['fresh_component_scalar'] == inner['component_scalar_proof'] == {
        'domains':28,'leaves':103,'bernstein_coefficients':12875,'frontier':0,'strict_except_all_zero':True}
    controls = read(folder/'reports/A165_I64_ATTACHMENT_PREPARATION_CONTROLS_V1.json')
    assert controls['status'] == 'PASS_A165_ATTACHMENT_SCOPE_AND_PREFIX_CONTROLS'
    assert controls['source_manifest_sha256'] == EXPECTED_OLD
    assert controls['source_payload_hashes_checked'] == 165 and controls['damaged_attachments_rejected'] == 19
    assert tuple(controls['retained_open_leaves']) == CHANGED
    assert controls['weighted_arithmetic_checked'] is False and controls['whole_cover_replayed'] is False
    freeze = read(folder/'sources/SOURCE_BINDINGS.json')
    for name, h in freeze['files'].items():
        assert sha(safe(folder/'sources',name)) == h
    assert len(freeze['files']) == 8 and len(freeze['external_input_sha256']) == 318
    assert sha(base/'INPUT_MANIFEST.json') == assembly['base_input_manifest_sha256'] == 'd8ca6d465aa3831e26d6d0149b8ce734a1043c51694f81a9ce9b9a4e3baaf965'
    assert sha(base/'BINDINGS.json') == assembly['base_binding_sha256'] == 'd3c7032b4aeb12649d8d971d0256de95e05dfdcb622ead8a4b6e69ccb633bde2'
    pins[str(base/'INPUT_MANIFEST.json')] = assembly['base_input_manifest_sha256']
    pins[str(base/'BINDINGS.json')] = assembly['base_binding_sha256']
    aliases = read(base/'BINDINGS.json')['files']
    base_inventory = read(base/'INPUT_MANIFEST.json')['files']
    source_folder = '/workspace/scratch/f9f48fcfb253/d_work/A_c744_component3_four_first_use_snapshot/'
    assert len(old['nodes']) == len(tree['nodes']) == len(assembly['nodes']) == 165
    for key in ('parent','id','original_path','conditional_parent','component','closed_domain','scope'):
        assert tree[key] == old[key], key
    assert tree['closed_domain']['rhs'] == '-3/5'
    changed=[];new_closed=[];appended_rounds=deductions=changed_bytes=0
    for n,(before,after,item) in enumerate(zip(old['nodes'],tree['nodes'],assembly['nodes'])):
        assert before['index'] == after['index'] == item['index'] == n
        assert before['file'] == after['file'] == item['file'] == f'node_{n:05d}.json'
        for key in ('parent','depth','restriction','children'):
            assert before.get(key) == after.get(key), (n,key)
        alias = aliases[source_folder+before['file']]
        source = safe(base,alias['path'])
        assert alias['sha256'] == before['sha256'] == base_inventory[alias['path']] == sha(source)
        pins[str(source)] = before['sha256']
        if n not in CHANGED:
            assert item['source'] == 'PUBLISHED_A1_ASSEMBLED_PACKET' and item['member'] == alias['path']
            assert before == after and item['sha256'] == before['sha256']
            continue
        changed.append(n)
        assert not before['children'] and before['status'] == 'OPEN'
        assert item['source'] == 'THIS_DELTA' and item['member'] == 'tree/'+after['file']
        current = safe(folder,item['member'])
        assert sha(current) == item['sha256'] == after['sha256'] != before['sha256']
        original, continued = read(source), read(current)
        assert continued['initial'] == original['initial']
        prefix = original['rounds']
        rounds = continued['rounds']
        assert rounds[:len(prefix)] == prefix
        appended_rounds += len(rounds)-len(prefix)
        deductions += sum(len(x['proposals']) for x in rounds[len(prefix):])
        changed_bytes += current.stat().st_size
        if after['status'] == 'CANDIDATE_CLOSED': new_closed.append(n)
        else: assert after['status'] == 'OPEN'
    assert tuple(changed) == CHANGED and new_closed == [155,158,160]
    assert (appended_rounds,deductions,changed_bytes) == (27,1664,15203667)
    leaves = [x for x in tree['nodes'] if not x['children']]
    assert len(leaves) == 132
    assert sum(x['status'] == 'OPEN' for x in leaves) == 14
    assert sum(x['status'] == 'CANDIDATE_CLOSED' for x in leaves) == 118
    for p,h in pins.items(): assert sha(Path(p)) == h,p
    return dict(status='PASS_A165_DELTA_BYTES_HEADERS_PREFIX_AND_BASE_ALIASES',
        input_manifest_sha256=EXPECTED_INPUT,files=len(inventory)+1,
        report_sha256=EXPECTED_REPORT,manifest_sha256=EXPECTED_TREE,
        nodes=165,unchanged_published_payloads=148,changed_payloads=17,
        changed_payload_bytes=changed_bytes,new_excluded_leaf_indices=new_closed,
        excluded_leaves=118,open_leaves=14,appended_rounds=27,appended_deductions=1664,
        source_files=8,external_source_pins_declared=318,scalar=inner['component_scalar_proof'],
        all_input_hashes_unchanged=True,arithmetic_replayed=False,cold_proof_claimed=False,
        new_original_cells=0,new_masks=0)

if __name__ == '__main__':
    p=argparse.ArgumentParser();p.add_argument('--delta',required=True,type=Path)
    p.add_argument('--a1-packet',required=True,type=Path);p.add_argument('--output',required=True,type=Path)
    a=p.parse_args();assert not a.output.exists();result=check(a.delta,a.a1_packet)
    with a.output.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps(result),flush=True)
