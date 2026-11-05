"""Preserve four exact partial C covers; never change the fixed cell ledger."""
from pathlib import Path
from hashlib import sha256
import argparse
import json
import shutil


def digest(path):
    h = sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def dump(path, data):
    Path(path).write_text(json.dumps(data, indent=2) + '\n')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('repo', type=Path)
    ap.add_argument('c_root', type=Path)
    a = ap.parse_args()
    repo, c = a.repo.resolve(), a.c_root.resolve()
    nine = repo / 'research/nine'
    packet = c / 'frozen_c_finite_frontiers_v2'
    ledger = nine / 'gates/A2_00100_FIXED_FRONTIER.json'
    ledger_hash = digest(ledger)
    register = read(ledger)
    assert len(register['cells']) == 231
    assert register['closed_cells'] == 224 and register['open_cells'] == 7
    originals = {v['id']: v for v in register['cells']}
    expected = {
        'c887_main_259': ('negative-887236b78100baf3', 259, 135, 0, 43),
        'cd402_opposite_507': ('negative-d4021ade840b985c', 507, 351, 0, 13),
        'c887_scalar_alternative_189': ('negative-887236b78100baf3', 189, 115, 24, 0),
        'cb882_abid_138': ('negative-b882d8ade0cf9ea0', 138, 67, 13, 12),
    }
    manifest = read(packet / 'MANIFEST.json')
    graph = read(c / 'C_FINITE_FRONTIERS_V2_HASH_GRAPH_REPLAY.json')
    ready = read(c / 'C_FINITE_FRONTIERS_V2_ARCHIVE_AUDIT.json')
    assert manifest['standalone_arithmetic_packet'] is False
    assert manifest['arithmetic_replayed_by_freezer'] is False
    assert manifest['new_original_cells'] == manifest['new_masks'] == 0
    assert manifest['every_open_alternative_retained']
    assert manifest['processed_record_bytes_unchanged']
    assert graph['status'] == 'PASS_HASH_AND_COMPLETE_FRONTIER_TRANSPORT_ONLY'
    assert ready['status'] == 'PASS_FROZEN_C_ARCHIVE_AND_EVERY_MEMBER_BYTE_AUDIT'
    assert ready['all_regular_members_rehashed'] and ready['no_links_or_path_traversal']
    assert ready['inventory_and_member_names_exhaustive']
    assert ready['independent_arithmetic_replayed_now'] is False
    assert ready['standalone_arithmetic_packet'] is False
    assert ready['new_original_cells'] == ready['new_masks'] == 0
    for filename, key in (
        ('MANIFEST.json', 'manifest_sha256'),
        ('INVENTORY.json', 'inventory_sha256'),
        ('EXTERNAL_PROOF_INPUTS.json', 'external_inputs_sha256'),
        ('PUBLISHED_DEPENDENCY_RECOVERY.json', 'published_recovery_sha256'),
        ('PUBLISHED_DEPENDENCY_ARCHIVE_CATALOG.json', 'published_catalog_sha256'),
    ):
        assert digest(packet / filename) == ready[key]
    assert digest(c / 'C_FINITE_FRONTIERS_V2_HASH_GRAPH_REPLAY.json') == ready['hash_graph_report_sha256']
    assert digest(c / 'code/archive_frozen_c_frontiers.py') == ready['archive_auditor_source_sha256']
    assert len(read(packet / 'INVENTORY.json')) == graph['files_rehashed'] == 1393
    assert ready['regular_members'] == 1394
    assert ready['uncompressed_member_bytes'] == 1493985907
    assert len(manifest['covers']) == len(expected)
    report_bindings = []
    for cover in manifest['covers']:
        name = cover['name']
        original, nodes, excluded, pending, stopped = expected[name]
        assert originals[original]['status'] == 'OPEN'
        assert cover['original_id'] == original
        counts = cover['counts']
        assert [counts[k] for k in ('processed_nodes', 'candidate_excluded_leaves', 'pending', 'stopped')] == [nodes, excluded, pending, stopped]
        assert counts['open_leaves'] == pending + stopped
        assert counts['whole_candidate_closed'] is False
        observed = read(packet / cover['verbatim_manifest'])
        assert digest(packet / cover['verbatim_manifest']) == cover['original_manifest_sha256']
        report_path = packet / cover['exact_replay']['path']
        assert digest(report_path) == cover['exact_replay']['sha256']
        report = read(report_path)
        assert report['status'] == cover['exact_replay']['status']
        assert report['original_id'] == original
        assert report['original_path'] == originals[original]['path']
        assert report['original_mask'] == '001/00' and report['squared_radius'] == '1105/256'
        assert report['manifest_snapshot_sha256'] == cover['original_manifest_sha256']
        assert [report[k] for k in ('nodes', 'excluded_leaves', 'unprocessed_leaves', 'stopped_leaves')] == [nodes, excluded, pending, stopped]
        assert report['open_leaves'] == pending + stopped
        assert not report['whole_original_excluded']
        for k in ('all_nine_originals_retained', 'all_36_corners_and_pairs_retained',
                  'all_five_cones_and_mask_bits_retained', 'no_other_original_consequence_imported',
                  'closed_shared_faces_retained'):
            assert report[k]
        assert not report['numerical_producer_imported'] and not report['lean_lake_ci_run']
        assert report['new_original_cells'] == report['new_masks'] == 0
        graph_cover = next(v for v in graph['covers'] if v['name'] == name)
        assert graph_cover['counts'] == counts and graph_cover['exact_partial_report_included']
        report_bindings.append(dict(name=name, original_id=original, counts=counts,
            report=cover['exact_replay']['path'], report_sha256=digest(report_path),
            original_manifest_sha256=cover['original_manifest_sha256'],
            native_manifest_sha256=digest(packet / cover['native_manifest'])))
    archive = c / 'frozen_c_finite_frontiers_v2.tar.xz'
    assert digest(archive) == ready['archive_sha256'] == '60c5fef27b403c0312665b4d1e361f671d4fff0cc30aeda92a12de8c76f9ec2f'
    assert archive.stat().st_size == ready['archive_bytes'] == 123751936
    out = nine / 'computer_assisted/a2_00100_c_finite_frontiers_v2'
    assert not out.exists()
    out.mkdir()
    copied = {}

    def copy(source, relative):
        target = out / relative
        assert not target.exists()
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        value = digest(target)
        assert value == digest(source)
        copied[str(relative)] = dict(sha256=value, bytes=target.stat().st_size)

    parts, combined = [], sha256()
    with archive.open('rb') as stream:
        for index, block in enumerate(iter(lambda: stream.read(8 * 1024 * 1024), b''), 1):
            name = archive.name + f'.part{index:03d}'
            target = out / name
            target.write_bytes(block)
            value = sha256(block).hexdigest()
            assert digest(target) == value
            parts.append(dict(file=name, bytes=len(block), sha256=value))
            combined.update(block)
    assert len(parts) == 15 and combined.hexdigest() == ready['archive_sha256']
    dump(out / 'ARCHIVE_PARTS.json', dict(archive=archive.name, archive_bytes=archive.stat().st_size,
        archive_sha256=ready['archive_sha256'], top_directory=packet.name, parts=parts))
    for name in ('MANIFEST.json', 'INVENTORY.json', 'EXTERNAL_PROOF_INPUTS.json',
                 'PUBLISHED_DEPENDENCY_RECOVERY.json', 'PUBLISHED_DEPENDENCY_ARCHIVE_CATALOG.json',
                 'ORIGINAL_PATH_MAP.json', 'SOURCE_BINDINGS.json', 'FREEZE_CONFIG.json'):
        copy(packet / name, name)
    copy(packet / 'README.md', 'FROZEN_PACKET_README.md')
    for cover in manifest['covers']:
        for field in ('verbatim_manifest', 'native_manifest'):
            copy(packet / cover[field], cover[field])
        copy(packet / cover['exact_replay']['path'], cover['exact_replay']['path'])
    for name in ('C_FINITE_FRONTIERS_V2_ARCHIVE_AUDIT.json',
                 'C_FINITE_FRONTIERS_V2_HASH_GRAPH_REPLAY.json',
                 'C_FINITE_FRONTIERS_V2_PUBLICATION_HANDOFF.md',
                 'C_FINITE_FRONTIERS_V2_RECOVERY_PREFIX_MAP.json',
                 'C_FRONTIER_FREEZER_V2_B16_AGENT_REVIEW.json',
                 'C_PUBLISHED_DEPENDENCY_B16_REHASH.json',
                 'CB882_ABID_FINAL_SCOPE_B16_REVIEW.json'):
        copy(c / name, name)
    for name in ('archive_frozen_c_frontiers.py', 'freeze_c_completed_frontiers.py',
                 'freeze_c_completed_frontiers_v2.py', 'verify_frozen_c_frontiers.py',
                 'verify_frozen_c_frontiers_v2.py', 'build_c_published_dependency_catalog.py'):
        copy(c / 'code' / name, 'transport_sources/' + name)
    copy(__file__, 'publish_c_finite_frontiers_v2.py')
    readme = f'''# C-family native partial checkpoint: no cell credit

This publication preserves four freshly exact-replayed partial covers of
three unchanged original cells in mask `001/00`. The register remains
**224/231 CLOSED, 7 OPEN**; whole masks remain **8/32 CLOSED**.

| Cover | Processed | Excluded leaves | Pending | Stopped | OPEN |
| --- | ---: | ---: | ---: | ---: | ---: |
| C887 main | 259 | 135 | 0 | 43 | 43 |
| Cd402 opposite-boundary continuation | 507 | 351 | 0 | 13 | 13 |
| C887 scalar alternative | 189 | 115 | 24 | 0 | 24 |
| Cb882 two ABID neighborhoods | 138 | 67 | 13 | 12 | 25 |

The scalar C887 cover is an alternative to the main cover; their counts
cannot be added. Processed counts exclude pending graph domains. All OPEN
alternatives and closed shared faces remain explicit. No whole original
or mask closes in this publication.

## What is checked

Each included native report independently reconstructs its original
physical attachment, exact rational deductions, complete covers and
actual terminals. All nine original squares, 36 corners and pairs, five
marked cones, actual AB/BC/EF/FG links, and strictly weak CD remain.
The C887 sharp terminal, one Cd402 AHID terminal and two literal Cb882
ABID terminals keep their precise hand-proof guards. Original H remains
present in both ABID uses. The deep-cylinder helper has no actual use.

The separate transport gate hashes all 1,393 inventoried files and checks
the four complete partial graphs. The archive audit streams and rehashes
all 1,394 regular members ({ready['uncompressed_member_bytes']:,} expanded bytes).
Those transport gates do not rerun arithmetic or grant original credit.

## Recovery

Concatenate the 15 parts in `ARCHIVE_PARTS.json` order, checking each
part and then the whole archive ({ready['archive_bytes']:,} bytes):

`{ready['archive_sha256']}`

Extract the `frozen_c_finite_frontiers_v2` directory and run its
`python3 -B -S verify_payload.py` for hash/graph verification. This is a
**native checkpoint with explicit published dependencies**. It does not
claim a standalone cold arithmetic replay. Exactly 994 external inputs
map to exact members of four previously published archives, whose 1,954
regular members and Git blobs were independently rehashed. Six derived
outputs are included in the packet instead of remaining external.

The [publication/recovery handoff](C_FINITE_FRONTIERS_V2_PUBLICATION_HANDOFF.md)
lists all archive paths, hashes, scoped recovery rules and native exact
replay entrypoints. The [frozen packet guide](FROZEN_PACKET_README.md)
explains the complete guarded components and source transport. Apply a
prefix rule only to its explicit input list. Restoring dependencies and
performing a fresh cold arithmetic replay are separate operations.

Later Cb882 and C887 continuations are outside this immutable snapshot.
The claim remains strict `q < Q = 1105/256`; no global closed-Q theorem
or equality classification is asserted. No Lean, Lake, compilation or CI.
'''
    (out / 'README.md').write_text(readme)
    assert digest(ledger) == ledger_hash
    audit = dict(status='PASS_ZERO_CREDIT_C_NATIVE_CHECKPOINT_PUBLICATION',
        expected_parent='195d1ffb3dfeef021e254744672a5c425352e987',
        fixed_register_sha256=ledger_hash, fixed_original_count=231,
        closed_originals=224, open_originals=7, original_ledger_unchanged=True,
        new_original_cells=0, new_masks=0, complete_original=False,
        standalone_arithmetic_packet=False, arithmetic_rerun_by_publisher=False,
        native_reports_checked=report_bindings, every_copied_file_rehashed=True,
        copied_files=copied, archive_sha256=ready['archive_sha256'],
        archive_bytes=ready['archive_bytes'], archive_parts=15,
        every_part_rehashed=True, all_archive_members_rehashed_by_pinned_auditor=True,
        no_lean_lake_compilation_or_ci=True)
    dump(out / 'ZERO_CREDIT_PUBLICATION_AUDIT.json', audit)
    print(json.dumps(dict(status=audit['status'], directory=str(out),
                         copied_files=len(copied), archive_parts=15,
                         register_unchanged=True), indent=2))


if __name__ == '__main__':
    assert __debug__
    main()
