#!/usr/bin/env python3
"""Freeze a held B462 whole-original launch without starting a solver."""
from pathlib import Path
import hashlib
import json
import os

ROOT=Path('/workspace/scratch/f9f48fcfb253')
HERE=Path(__file__).resolve().parent
ORIGINAL='negative-462e78d2e2d8be05'
ORIGINAL_SHA='24d91df8ce4a2472ebf76ac4b73c1fc07c58fbb5f9c213be8b415d1b8b2cc302'
DRIVER_SHA='02334833b824a58d49fcd316d154a59bc61866b0b3428f8fe7dcac12799af786'
SOURCES_SHA='dbb1fd76098c2868375299c67ba589001d453008109bdf46f7bfc2f72d13b399'
REVIEW_SHA='4ca43201674acdf1b9a5d130c5f41205c4b8ed2b81f928aaa818c814635b2466'
CURRENT_REGISTER_SHA='3dfaff7a880ab358930fb0ea835a1fdbe9959711f3c08ac47ee9817e7c693dde'

def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb')as f:
        for b in iter(lambda:f.read(1<<20),b''):h.update(b)
    return h.hexdigest()

def main():
    if not __debug__:raise RuntimeError('Exact assertions must be enabled')
    sources={}
    def pin(path,expected=None):
        p=Path(path).resolve();h=sha(p)
        if expected is not None:assert h==expected,str(p)
        assert str(p)not in sources or sources[str(p)]==h,str(p)
        sources[str(p)]=h;return p
    def read(path,expected=None):return json.loads(pin(path,expected).read_text())
    driver=pin(ROOT/'b_work/resume_b_five_proxy_round_atomic_center_tree_v1.py',DRIVER_SHA)
    source_freeze=read(HERE/'B_ATOMIC_ACCEPTED_CENTER_RUNTIME_SOURCE_FREEZE.json',SOURCES_SHA)
    assert len(source_freeze['files'])==247
    for p,h in source_freeze['files'].items():pin(p,h)
    review=read(ROOT/'d_work/B_ACCEPTED_CENTER_RUNTIME_ROOT_REVIEW.json',REVIEW_SHA)
    assert review['source_freeze_sha256']==SOURCES_SHA
    pin(ROOT/'ac_work/tree/B_ACCEPTED_CENTER_ATOMIC_RUNTIME_INDEPENDENT_REVIEW.json',
        '865016f82f838f46bcf8d2b9fb0a5d67fe93f60e36180b61a47995ff34067fed')
    pin(ROOT/'ac_work/tree/B_ACCEPTED_CENTER_ATOMIC_RUNTIME_INDEPENDENT_REVIEW.md')
    original_path=HERE/'registered_B_initial_states'/f'{ORIGINAL}.json'
    original=read(original_path,ORIGINAL_SHA)
    assert original['schema']=='B_registered_original_initial_state_v1'
    assert original['id']==ORIGINAL and original['scope']=='WHOLE_UNCHANGED_ORIGINAL_PARENT'
    assert original['status']=='OPEN' and original['all_nine_originals_retained']
    assert original['all_original_corners_and_pairs_retained'] and original['strict_CD_retained']
    original_register=read(original['register']['path'],original['register']['sha256'])
    current=read(ROOT/'repo/research/nine/gates/A2_00100_FIXED_FRONTIER.json',CURRENT_REGISTER_SHA)
    def definitions(register):
        return {c['id']:(c['sign'],c['baseline_frontier_index'],c['path'])for c in register['cells']}
    assert len(original_register['cells'])==len(current['cells'])==231
    assert definitions(original_register)==definitions(current)
    current_cell=next(c for c in current['cells']if c['id']==ORIGINAL)
    assert current_cell['status']=='OPEN' and current_cell['path']==original['path']
    assert current['closed_cells']==222 and current['open_cells']==9

    seed=HERE/'B462_accepted_center_prepared_whole_seed_v1'
    manifest=read(seed/'manifest.json')
    assert manifest['schema']=='B_proxy_first_complete_physical_tree_discovery_v1'
    assert manifest['completed']is True and manifest['status']=='OPEN' and len(manifest['nodes'])==1
    assert manifest['parent']==dict(path=str(original_path),sha256=ORIGINAL_SHA)
    for group in('sources','accepted_geometric_sources'):
        for p,h in manifest[group].items():pin(p,h)
    entry=manifest['nodes'][0]
    assert entry['index']==entry['depth']==0 and entry['status']=='OPEN'
    node=read(seed/entry['file'],entry['sha256'])
    assert node['parent']is None and node['choice']is None and node['children']==[]
    assert node['initial']==node['record']['initial']==node['record']['final']==original['final']
    assert node['record']['rounds']==[] and node['record']['status']=='OPEN'
    old_seed=ROOT/'global_work/recovery_20261105/B462_fresh_registered_seed'
    old=read(old_seed/'manifest.json','a72f82b211e6584423a72e66f31434fab950aa0b10efe8f65ef3bc1c7814b717')
    for group in('sources','accepted_geometric_sources'):
        for p,h in old[group].items():pin(p,h)
    old_node=pin(old_seed/old['nodes'][0]['file'],old['nodes'][0]['sha256'])
    assert (seed/entry['file']).read_bytes()==old_node.read_bytes()
    assert (seed/'PREVIOUS_COMPLETE_MANIFEST.json').read_bytes()==(old_seed/'manifest.json').read_bytes()

    reports={}
    for name in('B462_ACCEPTED_CENTER_FRESH_WHOLE_SEED_EXACT_REPLAY.json',
                'B462_ACCEPTED_CENTER_PREPARED_SEED_EXACT_REPLAY.json'):
        path=HERE/name;r=read(path)
        assert r['status']=='PASS_PARTIAL_PHYSICAL_TREE' and r['nodes']==r['open_leaves']==1
        assert r['excluded_leaves']==r['local_rounds']==r['local_deductions']==r['local_printed_rows']==0
        assert r['entire_registered_original_domain_retained']is True
        assert r['initial_original_id']==ORIGINAL and r['initial_path']==original['path']
        assert r['parent_certificate_sha256']==ORIGINAL_SHA
        assert r['universal_center_disk_rows_checked']==0
        assert not r['whole_original_proved'] and not r['complete']
        for p,h in r['source_sha256'].items():pin(p,h)
        reports[name]=dict(path=str(path),sha256=sha(path),nodes=1,open_leaves=1,
                          rounds=0,deductions=0,center_rows=0,whole_domain_retained=True)
    assert read(HERE/'B462_ACCEPTED_CENTER_PREPARED_SEED_EXACT_REPLAY.json')['certificate_sha256']==sha(seed/'manifest.json')
    pin(ROOT/'b_work/B462_REGISTERED_ORIGINAL_PHYSICAL_ATTACHMENT.md')
    pin(HERE/'B462_ACCEPTED_CENTER_LAUNCH_ATTACHMENT.md')
    pin(__file__)

    output=ROOT/'repo/research/nine/.runs/b462_fresh_accepted_center_atomic_v1'
    log=output.with_suffix('.log')
    assert not output.exists() and not log.exists()
    packet=ROOT/'b_work/b16a_I32_complete_H_checkpoint'
    command=['python','-B','-u',str(driver),str(seed),str(output),'--packet',str(packet),
             '--rounds','6','--existing-rounds','0','--proxy-rounds','0',
             '--max-depth','26','--max-new-nodes','1000']
    for p,h in sources.items():assert sha(p)==h,p
    stat=os.statvfs(ROOT)
    result=dict(schema='B462_accepted_center_whole_original_launch_freeze_v1',
        status='FROZEN_COMPLETE_ORIGINAL_OPEN_SEED_NUMERICAL_START_HELD_FOR_ROOT_SLOT_CONFIRMATION',
        original_id=ORIGINAL,original_path=original['path'],original_scope=original['scope'],
        original_certificate_sha256=ORIGINAL_SHA,source_manifest_sha256=sha(seed/'manifest.json'),
        original_definition_register_sha256=original['register']['sha256'],
        current_status_register_sha256=CURRENT_REGISTER_SHA,all_231_definition_tuples_identical=True,
        current_original_counts=dict(closed=222,open=9),current_mask_counts=dict(closed=8,open=24),
        complete_initial_domain=True,initial_nodes=1,initial_excluded_leaves=0,initial_open_leaves=1,
        all_nine_originals_36_corners_36_pairs_5_cones_retained=True,strict_CD_retained=True,
        actual_prepare_only_driver_session=31800,actual_prepare_only_driver_observed_exit_code=0,
        earlier_seed_exact_session=95125,earlier_seed_exact_observed_exit_code=0,
        prepared_seed_exact_session=70299,prepared_seed_exact_observed_exit_code=0,
        exact_reports=reports,accepted_runtime_source_freeze_sha256=SOURCES_SHA,
        accepted_runtime_root_review_sha256=REVIEW_SHA,source_inputs=sources,
        command=command,environment=dict(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1'),
        output=str(output),log=str(log),output_and_log_absent_at_freeze=True,
        actual_f_bfree_bytes_before_freeze=stat.f_bfree*stat.f_frsize,
        accepted_center_family_added_to_this_discovery_context=True,new_mathematical_rule_created=False,
        numerical_worker_started=False,optimization_called_during_preparation=False,
        lost_187_node_numerical_suffix_reconstructed=False,old_sources_and_seeds_unchanged=True,
        one_file_atomicity_only=True,node_manifest_multifile_transaction_claimed=False,
        new_original_cells=0,new_masks=0,ledger_mutated=False,launch_ownership='root scheduling; hold until explicit free-slot confirmation')
    target=HERE/'B462_ACCEPTED_CENTER_HELD_WHOLE_ORIGINAL_LAUNCH_FREEZE.json'
    with target.open('x')as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps(dict(status=result['status'],source_pins=len(sources),freeze_sha256=sha(target),
                          seed_manifest_sha256=result['source_manifest_sha256'],output=str(output))),flush=True)

if __name__=='__main__':main()
