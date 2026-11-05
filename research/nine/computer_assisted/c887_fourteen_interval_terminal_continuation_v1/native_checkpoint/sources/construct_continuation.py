#!/usr/bin/env python3
"""Construct only the 14 proved-terminal candidates on a complete frozen91-node cover."""
from pathlib import Path
import argparse
import json
import attachment as A


def main():
    ap=argparse.ArgumentParser()
    for name in ('packet','predecessor-tree','predecessor-report','output'):
        ap.add_argument('--'+name, type=Path, required=True)
    args=ap.parse_args(); here=Path(__file__).resolve().parent
    A.source_freeze(here)
    packet=args.packet.resolve(); source=args.predecessor_tree.resolve(); output=args.output.resolve()
    assert not output.exists() and not output.is_relative_to(packet) and not output.is_relative_to(source)
    _,_,_,_,_,_,manifest,entries,records,pins=A.predecessor(packet,source,args.predecessor_report.resolve())
    output.mkdir(parents=True,exist_ok=False); replacements=[]
    for index,entry in sorted(entries.items()):
        path=output/entry['file']
        if index in A.LEAVES:
            record=A.closed_record(records[index],A.TERMINAL)
            path.write_text(json.dumps(record,indent=2)+'\n')
            replacements.append(dict(index=index,old_sha256=entry['sha256'],new_sha256=A.H.sha(path)))
        else:
            path.write_bytes((source/entry['file']).read_bytes())
            assert A.H.sha(path)==entry['sha256']
    final=A.expected_manifest(manifest,replacements,A.H.sha(here/'SOURCE_BINDING.json'))
    (output/'manifest.json').write_text(json.dumps(final,indent=2)+'\n')
    for path,digest in pins.items():assert A.H.sha(path)==digest
    A.source_freeze(here)
    receipt=dict(status='CONSTRUCTED_COMPLETE91_FOURTEEN_INTERVAL_TERMINAL_CANDIDATE',
        source_binding_sha256=A.H.sha(here/'SOURCE_BINDING.json'),
        predecessor_manifest_sha256=A.PREDECESSOR_MANIFEST_SHA,
        manifest_sha256=A.H.sha(output/'manifest.json'),
        changed_payloads=14,unchanged_payloads=77,new_terminal_leaf_indices=list(A.LEAVES),
        historical_initials_and_rounds_preserved=True,all_source_hashes_unchanged=True,
        exact_terminal_and_full_cover_gate_pending=True,new_hull_or_endpoint_family_used=False,
        numerical_solver_called=False,new_original_cells=0,new_masks=0)
    (output/'CONSTRUCTION_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt),flush=True)


if __name__=='__main__':main()
