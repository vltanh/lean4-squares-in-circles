#!/usr/bin/env python3
"""Copy completed reviewed exact checkpoints; no proof arithmetic or search."""
from pathlib import Path
import hashlib
import json
import shutil

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / 'repo/research/nine/computer_assisted'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write(path, value):
    with Path(path).open('x') as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write('\n')


def copy(source, target):
    assert Path(source).is_file() and not Path(source).is_symlink() and not Path(target).exists()
    Path(target).parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, target)
    assert Path(source).read_bytes() == Path(target).read_bytes()


def preserve(source, target, manifest_name, expected):
    manifest = source / manifest_name
    assert sha(manifest) == expected
    data = json.loads(manifest.read_text())
    members = data['files']
    assert {str(p.relative_to(source)) for p in source.rglob('*') if p.is_file()} == set(members) | {manifest_name}
    assert not any(p.is_symlink() for p in source.rglob('*'))
    for name, entry in members.items():
        path = source / name
        assert path.resolve().is_relative_to(source.resolve())
        assert path.stat().st_size == entry['bytes'] and sha(path) == entry['sha256']
    for name in sorted(set(members) | {manifest_name}):
        copy(source / name, target / name)


def finish(folder, source_hash, copies, readme):
    for source, target in copies:
        copy(ROOT / source, folder / target)
    copy(__file__, folder / 'package_reviewed_evidence.py')
    (folder / 'README.md').write_text(readme)
    files = {str(p.relative_to(folder)): {'bytes': p.stat().st_size, 'sha256': sha(p)}
             for p in sorted(folder.rglob('*')) if p.is_file()}
    write(folder / 'PUBLICATION_MANIFEST.json', dict(
        schema='completed_native_exact_evidence_publication_v1', source_packet_manifest_sha256=source_hash,
        files=files, total_bytes=sum(v['bytes'] for v in files.values()), source_bytes_unchanged=True,
        native_dependency_aliases_explicit=True, cold_self_contained_replay_claimed=False,
        new_original_cells=0, new_masks=0, lean_lake_ci_run=False))
    return dict(folder=str(folder.relative_to(ROOT / 'repo')), files=len(files) + 1,
                bytes=sum(p.stat().st_size for p in folder.rglob('*') if p.is_file()),
                publication_manifest_sha256=sha(folder / 'PUBLICATION_MANIFEST.json'))


def main():
    c = DEST / 'c887_fourteen_interval_terminal_continuation_v1'
    s = DEST / 'strict_011_c_height_first_exact_cover_use_v1'
    assert not c.exists() and not s.exists()
    c.mkdir(); s.mkdir()
    ch = '0b62b72b0be57649e0608c1e8a0fc9fe222086b550aa28dbfd8d1b2b942f7ef5'
    sh = 'a88dd86ec253289e51256ab8a3be59c3168a5c9385bc1ccd6c1c23bde65155fd'
    preserve(ROOT / 'b_work/c887_fourteen_terminal_publication_v1', c / 'native_checkpoint', 'INPUT_MANIFEST.json', ch)
    preserve(ROOT / 'global_work/strict011_c_height_tree_first_use_v1', s / 'native_checkpoint', 'PUBLICATION_MANIFEST.json', sh)
    c_result = finish(c, ch, [
        ('d_work/C887_FOURTEEN_TERMINAL_ROOT_PACKET_BYTE_AUDIT.json', 'ROOT_PACKET_BYTE_AUDIT.json'),
        ('b_work/C887_FOURTEEN_TERMINAL_PACKET_VERIFICATION_RECEIPT.json', 'PACKET_VERIFICATION_RECEIPT.json')],
        '''# C887: fourteen additional exact interval terminals

The complete retained 91-node C887 cover now has 17 excluded leaves and 56
OPEN leaves. Fourteen zero-round leaves are newly excluded by the existing
independent center-interval terminal. The three previously proved D/G
terminals remain included. No new hull, endpoint family or geometry is used.

The fresh independent gate checks all fourteen new terminals, rejects 56
damaged cases, and reconstructs every child initial state in all eighteen
complete proxy/SAT/angle covers. Every predecessor node outside the fourteen
changes remains byte-identical. Historical weighted arithmetic and the three
earlier terminal proofs are explicitly reused by exact identity.

The native checkpoint includes all seventeen changed payloads relative to
the published original 91-node base. Its exact assembly table identifies the
other 74 final payloads. Both predecessor and final manifests are preserved;
the byte checker and fresh-directory materializer reproduce both complete
trees without requiring an unpublished predecessor directory. Root source
review preceded construction; independent replay and materialization both
observed exit zero. Root separately rechecked all packet and base aliases.

See [the native hand and replay instructions](native_checkpoint/README.md).
The published C height base and explicit historical native aliases are still
required. No cold standalone proof is claimed. The entire original and mask
remain OPEN: totals are unchanged at 222/231 originals and 8/32 masks CLOSED.
No numerical optimizer, Lean, Lake, compilation or CI was run.
''')
    s_result = finish(s, sh, [
        ('d_work/STRICT011_C_HEIGHT_FIRST_USE_ROOT_EVIDENCE_REVIEW.json', 'ROOT_FIRST_USE_EVIDENCE_REVIEW.json'),
        ('d_work/STRICT011_STRENGTHENED_PILOT_PRIORITY_STOP_V1.json', 'NUMERICAL_PILOT_STOP_RECEIPT.json'),
        ('d_work/STRICT011_STRENGTHENED_PILOT_PROCESS_V1.log', 'NUMERICAL_CAPACITY_WAITER.log')],
        '''# Preserved completed strict-011 C-height first exact use

This checkpoint preserves work completed before the current-mask priority
change. Further 011 development is paused while 001/00 remains OPEN. The
separate numerical pilot's capacity waiter was stopped before it launched;
its observed stop receipt and log are included. No resume adapter was written.

The new height-cover reader passed root and peer source/physical review before
the first exact use. Its complete five-node tree retains all four closed
height alternatives of the original strict-radius caller. A fresh scalar
subprocess checks 28 domains, 351 leaves and 43,875 rational Bernstein
coefficients. All four child records then replay with positive weights on
their independently reconstructed conditional height rows: four rounds,
four deductions, eight printed rows and zero residual. All four leaves remain
OPEN. The gate observed exit zero; root rechecked the full frozen evidence
and all 293 inputs listed by the complete replay.

The attachment derives each child's height context from its checked parent
union, propagates that context through unchanged complete 4/8/2 covers, and
forbids a second height union on the same path. It preserves all nine physical
originals, 36 corners, 36 pair disjunctions, five exact marked cones, strict
radius and closed faces. The unchanged base-state schema carries no hidden
new predicate. Hand-chosen exact weights are used; the separate real-LP
corner-row gate is not claimed.

[The native checkpoint](native_checkpoint/README.md) includes all frozen
sources, the complete raw scalar and tree reports, first-use receipt, actual
execution logs, root/peer reviews and the prelaunch output-parent correction.
Explicit earlier published dependencies remain necessary; this is not a cold
standalone replay. No original or mask is closed. Totals remain 222/231
originals and 8/32 masks CLOSED. No Lean, Lake, compilation or CI was run.
''')
    result = dict(status='PASS_BYTE_IDENTICAL_COMPLETED_C14_AND_011_PRESERVATION',
                  packets=[c_result,s_result], mathematical_arithmetic_repeated=False)
    write(ROOT / 'd_work/C14_COMPLETED011_PACKAGING.json', result)
    print(json.dumps(result))


if __name__ == '__main__':
    main()
