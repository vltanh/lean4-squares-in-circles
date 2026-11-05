#!/usr/bin/env python3
"""Fresh zero-round14-terminal arithmetic plus complete91 cover, with explicit old proof reuse."""
from pathlib import Path
from copy import deepcopy
from fractions import Fraction as F
import argparse
import importlib.util
import json
import sys
import attachment as A


def main():
    ap=argparse.ArgumentParser()
    for name in ('packet','predecessor-tree','predecessor-report','tree','output'):
        ap.add_argument('--'+name,type=Path,required=True)
    args=ap.parse_args(); here=Path(__file__).resolve().parent
    freeze=A.source_freeze(here); packet=args.packet.resolve(); tree=args.tree.resolve(); output=args.output.resolve()
    assert not output.exists()
    old_report,old_manifest,old_entries,old_records,inputs,prior_report,prior,entries,old,pins=A.predecessor(
        packet,args.predecessor_tree.resolve(),args.predecessor_report.resolve())
    manifest_sha=A.H.sha(tree/'manifest.json'); manifest=A.H.read(tree/'manifest.json')
    records={}; replacements=[]
    for index,entry in sorted(entries.items()):
        p=tree/entry['file']; record=A.H.read(p)
        if index in A.LEAVES:
            assert record==A.closed_record(old[index],A.TERMINAL)
            replacements.append(dict(index=index,old_sha256=entry['sha256'],new_sha256=A.H.sha(p)))
        else:
            assert A.H.sha(p)==entry['sha256'] and record==old[index]
        records[index]=record
    assert manifest==A.expected_manifest(prior,replacements,A.H.sha(here/'SOURCE_BINDING.json'))
    spec=importlib.util.spec_from_file_location('unchanged_c887_fourteen_terminal_transport',packet/'replay_portable_c_height_packet_v3.py')
    transport=importlib.util.module_from_spec(spec);spec.loader.exec_module(transport)
    inventory,aliases,locate,output_aliases=transport.install(packet,output)
    import verify_c887_ownerfree_physical_tree as ORIGINAL
    core=ORIGINAL.SAT;assert A.H.sha(core.__file__)==A.H.CORE_SHA
    adapter=ORIGINAL.Adapter(ORIGINAL.Checker())
    assert adapter.K.V.Q==F(1105,256)
    assert adapter.K.V.EDGES==((0,1,0),(1,2,0),(2,3,1),(4,5,0),(5,6,0))
    covers,_=A.H.validate_complete_parent_paths(old_entries,old_records,adapter,core,ORIGINAL)
    fresh=[];controls=[]
    for index in A.LEAVES:
        initial=A.H.restore_state(old[index]['final'],adapter,core)
        assert records[index]['initial']==old[index]['initial']==old[index]['final']
        assert records[index]['rounds']==old[index]['rounds']==[]
        audit,after=core.check_record(records[index],initial,adapter)
        assert after is None and audit['status']=='PASS_EXCLUDED_PHYSICAL_DOMAIN'
        assert (audit['rounds'],audit['deductions'],audit['printed_rows_checked'])==(0,0,0)
        fresh.append(dict(index=index,terminal=A.TERMINAL,exact_audit=audit,full_path=initial['path'],
            parent=entries[index]['parent'],depth=entries[index]['depth'],
            old_node_sha256=entries[index]['sha256'],new_node_sha256=A.H.sha(tree/entries[index]['file'])))
        for label,change in (
            ('wrong_original',lambda r:r['initial'].__setitem__('id','foreign')),
            ('omitted_parent_restriction',lambda r:r['initial']['path'].pop()),
            ('wrong_terminal_label',lambda r:r['terminal'].__setitem__('label','foreign terminal')),
            ('kept_OPEN_status',lambda r:r.__setitem__('status','OPEN'))):
            damaged=deepcopy(records[index]);change(damaged)
            try:core.check_record(damaged,initial,adapter)
            except (AssertionError,ValueError,TypeError,KeyError):controls.append(dict(index=index,rejected=label))
            else:raise AssertionError(('malformed terminal accepted',index,label))
    assert len(controls)==56
    entries_new={e['index']:deepcopy(e)for e in manifest['nodes']}
    leaves,parents=A.composed_statuses(entries_new)
    assert list(entries_new.values())==manifest['nodes']
    assert len(covers)==18 and len(leaves)==73
    assert sum(r['excluded']for r in leaves)==17
    for p,digest in pins.items():assert A.H.sha(p)==digest
    assert A.H.sha(tree/'manifest.json')==manifest_sha
    for entry in manifest['nodes']:assert A.H.sha(tree/entry['file'])==entry['sha256']
    for name,digest in inventory.items():assert A.H.sha(packet/name)==digest
    A.source_freeze(here)
    assert not any(name in sys.modules for name in ('numpy','scipy','highspy','physical_sat_engine_snapshot','physical_sat_diagonal_engine','ac_physical_context'))
    report=dict(status='PASS_COMPLETE_C88791_WITH_FOURTEEN_NEW_EXISTING_INTERVAL_TERMINALS',
        original_id=A.H.TARGET,original_path=A.H.ORIGINAL_PATH,mask='001/00',squared_radius='1105/256',
        source_binding_sha256=A.H.sha(here/'SOURCE_BINDING.json'),new_manifest_sha256=manifest_sha,
        predecessor_manifest_sha256=A.PREDECESSOR_MANIFEST_SHA,predecessor_exact_report_sha256=A.PREDECESSOR_REPORT_SHA,
        accepted_old_complete_consumer_report_sha256=A.H.REPORT_SHA,accepted_old_complete_manifest_sha256=A.H.TREE_SHA,
        historical_input_identities_rehashed=inputs,historical_weighted_arithmetic_reused_not_repeated=True,
        prior_three_terminal_arithmetic_reused_not_repeated=True,
        all_nodes=91,unchanged_payloads_byte_verified=77,complete_parent_paths_checked=91,
        complete_proxy_covers=9,complete_sat_covers=6,complete_closed_angle_covers=3,
        leaf_domains=73,excluded_leaf_domains=17,open_leaf_domains=56,
        fresh_terminal_leaf_indices=list(A.LEAVES),retained_prior_excluded_leaf_indices=list(A.OLD_CLOSED),
        fresh_terminal_audits=fresh,damaged_controls_rejected=controls,
        complete_cover_audits=covers,leaf_table=leaves,recomputed_closed_parent_indices=parents,
        unchanged_independent_core_sha256=A.H.CORE_SHA,all_nine_originals_retained=True,
        original_corner_predicates=36,original_pair_predicates=36,marked_cones=5,
        strict_weak_CD_retained=True,closed_shared_faces_retained=True,
        new_hull_or_endpoint_family_used=False,numerical_solver_called=False,
        new_original_cells=0,new_masks=0,original_still_open=True,cold_self_contained_replay_claimed=False)
    p=output/'EXACT_REPLAY.json';p.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(status=report['status'],report_sha256=A.H.sha(p),nodes=91,
        fresh_terminals=14,excluded_leaves=17,open_leaves=56)),flush=True)


if __name__=='__main__':main()
