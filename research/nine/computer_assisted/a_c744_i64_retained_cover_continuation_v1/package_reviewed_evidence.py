#!/usr/bin/env python3
"""Preserve reviewed exact evidence byte-for-byte; this is not a proof replay."""
from pathlib import Path
import hashlib
import json
import shutil

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / 'repo/research/nine/computer_assisted'
A = ROOT / 'ac_work/recovery_20261105_reset2'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def write(path, value):
    with Path(path).open('x') as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write('\n')


def copy(source, target, expected=None):
    source, target = Path(source), Path(target)
    assert source.is_file() and not source.is_symlink() and not target.exists()
    if expected is not None:
        assert sha(source) == expected
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, target)
    assert target.read_bytes() == source.read_bytes()


def packet(source, target, expected):
    manifest = source / 'INPUT_MANIFEST.json'
    assert sha(manifest) == expected
    members = read(manifest)['files']
    assert {str(p.relative_to(source)) for p in source.rglob('*') if p.is_file()} == set(members) | {'INPUT_MANIFEST.json'}
    assert not any(p.is_symlink() for p in source.rglob('*'))
    for name, entry in members.items():
        path = source / name
        assert path.resolve().is_relative_to(source.resolve())
        assert path.stat().st_size == entry['bytes'] and sha(path) == entry['sha256']
    for name in sorted(set(members) | {'INPUT_MANIFEST.json'}):
        copy(source / name, target / name)


def finish(folder, readme, evidence):
    (folder / 'README.md').write_text(readme)
    copy(__file__, folder / 'package_reviewed_evidence.py')
    members = {str(p.relative_to(folder)): {'bytes': p.stat().st_size, 'sha256': sha(p)}
               for p in sorted(folder.rglob('*')) if p.is_file()}
    write(folder / 'PUBLICATION_MANIFEST.json', dict(
        schema='reviewed_native_exact_evidence_publication_v1', files=members,
        total_bytes=sum(v['bytes'] for v in members.values()), evidence=evidence,
        source_bytes_unchanged=True, native_dependency_aliases_explicit=True,
        cold_self_contained_replay_claimed=False, new_original_cells=0, new_masks=0,
        lean_lake_ci_run=False))
    return dict(folder=str(folder.relative_to(ROOT / 'repo')), files=len(members) + 1,
                bytes=sum(p.stat().st_size for p in folder.rglob('*') if p.is_file()),
                publication_manifest_sha256=sha(folder / 'PUBLICATION_MANIFEST.json'))


def main():
    a = DEST / 'a_c744_i64_retained_cover_continuation_v1'
    c = DEST / 'c887_fresh_original_bounds_root_replay_v1'
    assert not a.exists() and not c.exists()
    a.mkdir(); c.mkdir()
    ready = read(A / 'A165_NATIVE_DELTA_READY_V1.json')
    assert sha(A / 'A165_NATIVE_DELTA_READY_V1.json') == 'ed91a5f3e3e3039c62060350419d318fa8050abbac9c365607c6c22c6d1bb12e'
    for path, entry in ready['files'].items():
        assert Path(path).stat().st_size == entry['bytes']
        copy(path, a / 'delta' / Path(path).name, entry['sha256'])
    copy(A / 'A165_NATIVE_DELTA_READY_V1.json', a / 'delta/A165_NATIVE_DELTA_READY_V1.json')
    for name in ['A165_NATIVE_DELTA_ROOT_EXTRACTION_V1.json', 'A165_NATIVE_DELTA_ROOT_BYTE_AUDIT_V1.json',
                 'A165_I64_CONTINUATION_ROOT_SOURCE_REVIEW.json',
                 'A165_FIRST_I64_HEIGHT_ROOT_SOURCE_AND_ATTACHMENT_REVIEW.json']:
        copy(ROOT / 'd_work' / name, a / 'root_review' / name)
    for name in ['README.md', 'TREE_ASSEMBLY.json', 'DEPENDENCIES.json', 'I64_ENDPOINT_DEPENDENCIES.json',
                 'reports/A165_I64_EXACT_CONTINUATION_REPLAY_V1.json',
                 'reports/A165_I64_FULL_REPLAY_OBSERVED_EXIT_V1.json',
                 'sources/COMPLETE_RETAINED_COVER_ATTACHMENT.md']:
        copy(A / 'a165_i64_native_continuation_delta_v1' / name, a / 'readable_evidence' / name)
    packet(A / 'a165_first_height_native_checkpoint_v1', a / 'separate_first_height_use',
           '3c8d14d33438e89c5ca444a2f938c3247aa11ee48717dc358f9c15bc3b175c42')
    ar = read(a / 'readable_evidence/reports/A165_I64_EXACT_CONTINUATION_REPLAY_V1.json')
    assert (ar['nodes'], ar['excluded_leaves'], ar['open_leaves']) == (165, 118, 14)
    a_summary = finish(a, '''# A-c744: exact continuation of the complete retained cover

The complete retained 165-node cover now has 118 excluded leaves and 14 OPEN
leaves. The new exclusions are leaves 155, 158 and 160. All 165 consumer records
and all complete covers were independently replayed; the observed process
exited zero. There were 112 rounds, 28,533 deductions and 48,549 printed rows.
The fresh component scalar replay checked 28 domains, 103 leaves and 12,875
Bernstein coefficients. No numerical optimizer or new split was used.

The original component-3 domain remains the old closed 3/5 domain. Every
original initial state, every old round and every 4/8/2 alternative is retained.
The original-wide 16/25 endpoint family supplies 1,664 positive weighted uses.
The old source/complement proofs and the separately published 813-deduction
source are explicitly reused by identity, rather than claimed as freshly run.

The compact archive in `delta/` holds all 17 changed payloads, the complete new
manifest, source files, full fresh report, inherited full report and observed
execution evidence. `readable_evidence/TREE_ASSEMBLY.json` maps all 148 omitted
unchanged payloads to the published A1 base packet. The archive has 45 regular
members and preserves 16,153,258 uncompressed bytes. Root fresh extraction and
the exact-member/prefix/base-alias audit passed. The two earlier byte-audit
harness errors and their corrected v3 source are retained as preparation
history; neither error was a mathematical replay failure.

For extraction, use the preserved `a165_delta_transport_v1.py` and inventory;
then the archived `materialize_tree.py` combines the delta with the identified
published A1 base. Native dependency aliases are still required for arithmetic
replay. This is not a claim of a cold standalone proof.

`separate_first_height_use/` records one subsequent exact deduction at leaf
154. Half of the accepted 16/25 height row and half of each current negative-yB
and negative-yD endpoint row improve yI's lower bound by 71693/524288, with
zero residual. The independent unchanged core accepts it and rejects five
damaged records. This separate one-leaf deduction has not replaced the cover.

The whole original and mask remain OPEN. The fixed totals remain 222/231
originals and 8/32 masks CLOSED. No Lean, Lake, compilation or CI was run.
''', dict(full_consumer_report_sha256=sha(a / 'readable_evidence/reports/A165_I64_EXACT_CONTINUATION_REPLAY_V1.json'),
          manifest_sha256='4469ce8ceda7692f49faa58ece25872c0448fbd8fc86447acb6facf0cd4e2283',
          nodes=165, excluded_leaves=118, open_leaves=14, new_excluded_leaf_indices=[155,158,160],
          archive_sha256=ready['archive_sha256'], first_height_use_composed_into_cover=False))
    fresh = ROOT / 'd_work/c887_external_fresh_gate_v1'
    receipt = read(fresh / 'ROOT_FRESH_REPLAY_RECEIPT.json')
    assert sha(fresh / 'ROOT_FRESH_REPLAY_RECEIPT.json') == '364e19d8342f5d35f5b836dd835a0154eb6ef01501517fd8dcfd6abbc4c4ef20'
    assert receipt['native_subprocess_observed_exit_code'] == 0 and receipt['native_inputs_rehashed_before_and_after'] == 557
    files = [p for p in fresh.rglob('*') if p.is_file()]
    assert len(files) == 7 and not any(p.is_symlink() for p in fresh.rglob('*'))
    for path in files:
        copy(path, c / 'fresh_replay' / path.relative_to(fresh))
    for name in ['C887_FRESH_WHOLE_STATE_ROOT_SOURCE_REVIEW.json', 'replay_external_c887_fresh_bounds_v1.py',
                 'C887_EXTERNAL_FRESH_GATE_ROOT_PROCESS.log']:
        copy(ROOT / 'd_work' / name, c / 'root_review' / name)
    for name in ['INDEPENDENT_SOURCE_AND_PHYSICAL_REVIEW.json', 'INDEPENDENT_SOURCE_AND_PHYSICAL_REVIEW.md',
                 'BYTE_DOMAIN_HULL_AUDIT.json', 'audit_sources_and_original_hull_v2.py',
                 'audit_sources_and_original_hull.py', 'AUDIT_V1_PREPARATION_FAILURE.json', 'EXPORT_RECEIPT.json']:
        copy(ROOT / 'b_work/c887_external_fresh_start_review_v1' / name, c / 'peer_review' / name)
    c_summary = finish(c, '''# C887: fresh independent replay of whole-original starting bounds

The source packet in commit 4efd616976b22fb3dd1802a0314deba461753099
(`c887_fresh_original_starting_state_v1`) has now passed root source/physical
review and a fresh independent exact replay. This folder preserves all seven
fresh output files, including the original-prefix and accepted-height child
reports, full whole-state report, raw logs and observed execution receipt.

The fresh proof reconstructs the original C887 prefix and its accepted height
consequences, then six root rounds with 624 deductions and 1,288 printed rows.
All eight physical D/G alternatives start from the same parent. Four are
excluded and four survive. Their coordinatewise hull supplies necessary bounds
on all 207 original slope, center, frame, pair-difference and diagonal intervals;
165 intervals strictly improve the earlier target. The parent's original ID,
path and choices are restored, and no child SAT auxiliary crosses the union.

The missing older strong-box archive supplies no premise. The earlier target
is used only as a weaker statement, with exact containment checked separately.
The source bytes and all 557 native inputs were checked before and after the
fresh replay; the certified hull matches the published hull exactly. The fresh
process exited zero. The accepted general cone, rotating center cone and
incircle families are reconstructed independently; no tangent row is used.

`root_review/replay_external_c887_fresh_bounds_v1.py` preserves the native
command and full input binding. The already-published source archive and its
explicit native dependency aliases are still needed. No cold standalone
replay is claimed. A peer's read-only source/hull audit and its corrected
metadata-only preparation harness are also preserved.

These are whole-original necessary bounds, not an exclusion. C887 and its
mask remain OPEN. Totals remain 222/231 originals and 8/32 masks CLOSED.
No numerical optimizer, Lean, Lake, compilation or CI was run.
''', dict(published_source_commit=receipt['published_commit'], source_archive_sha256=receipt['archive_sha256'],
          fresh_report_sha256=receipt['fresh_report_sha256'], exact_native_pins=557,
          complete_DG_alternatives=8, excluded_DG_alternatives=4, whole_original_excluded=False))
    result = dict(status='PASS_BYTE_IDENTICAL_REVIEWED_PUBLICATION_SELECTION', packets=[a_summary,c_summary],
                  mathematical_arithmetic_repeated=False)
    write(ROOT / 'd_work/A165_C887_FRESH_PACKAGING.json', result)
    print(json.dumps(result))


if __name__ == '__main__':
    main()
