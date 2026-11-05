#!/usr/bin/env python3
"""Copy reviewed native evidence unchanged; no mathematical replay is performed."""
from pathlib import Path
import hashlib
import json
import shutil

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / 'repo/research/nine/computer_assisted'

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def write(path, value):
    with path.open('x') as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write('\n')

def packet(source, destination, expected):
    inventory = source / 'INPUT_MANIFEST.json'
    assert sha(inventory) == expected
    data = json.loads(inventory.read_text())
    assert {str(p.relative_to(source)) for p in source.rglob('*') if p.is_file()} == set(data['files']) | {'INPUT_MANIFEST.json'}
    assert not any(p.is_symlink() for p in source.rglob('*'))
    for name, entry in data['files'].items():
        path = source / name
        assert path.resolve().is_relative_to(source.resolve())
        assert path.stat().st_size == entry['bytes'] and sha(path) == entry['sha256']
    shutil.copytree(source, destination)
    for p in source.rglob('*'):
        if p.is_file():
            q = destination / p.relative_to(source)
            assert q.read_bytes() == p.read_bytes()

def finalize(folder, source_inventory, copies, readme):
    for source, name in copies:
        target = folder / name
        target.parent.mkdir(parents=True, exist_ok=True)
        assert not target.exists()
        shutil.copyfile(ROOT / source, target)
        assert sha(target) == sha(ROOT / source)
    shutil.copyfile(__file__, folder / 'package_reviewed_evidence.py')
    (folder / 'README.md').write_text(readme)
    members = {str(p.relative_to(folder)): {'bytes': p.stat().st_size, 'sha256': sha(p)}
               for p in sorted(folder.rglob('*')) if p.is_file()}
    write(folder / 'PUBLICATION_MANIFEST.json', {
        'schema': 'reviewed_native_proof_evidence_publication_v1',
        'source_packet_manifest_sha256': source_inventory,
        'files': members, 'total_bytes': sum(v['bytes'] for v in members.values()),
        'source_bytes_unchanged': True, 'native_dependency_aliases_explicit': True,
        'cold_self_contained_replay_claimed': False,
        'new_original_cells': 0, 'new_masks': 0, 'lean_lake_ci_run': False})
    return {'folder': str(folder.relative_to(ROOT / 'repo')),
            'files': len(members) + 1,
            'bytes': sum(p.stat().st_size for p in folder.rglob('*') if p.is_file()),
            'publication_manifest_sha256': sha(folder / 'PUBLICATION_MANIFEST.json')}

def main():
    a = DEST / 'a_c744_original_i64_endpoint_attachment_v1'
    c = DEST / 'c887_three_terminal_continuation_v1'
    assert not a.exists() and not c.exists()
    a.mkdir(); c.mkdir()
    ah = '8edf7970a83abc7f8d1b8d42aeb7a33aea1a24059c1a712e24151f2c40474e78'
    ch = 'ae0f8dffdad4fd1399eb4dcd07450408db3bee86af6b8b37404ce9f21a06c156'
    packet(ROOT / 'ac_work/recovery_20261105_reset2/a_c744_original_i64_endpoint_native_v1', a / 'native_checkpoint', ah)
    packet(ROOT / 'b_work/c887_three_terminal_publication_v1', c / 'native_checkpoint', ch)
    results = []
    results.append(finalize(a, ah, [
        ('d_work/A_ORIGINAL_I64_ENDPOINT_PACKET_ROOT_BYTE_AUDIT.json', 'ROOT_PACKET_BYTE_AUDIT.json'),
        ('d_work/A_ORIGINAL_I64_FIRST_DIRECT_ROOT_FRESH_REPLAY.log', 'ROOT_FRESH_268_REPLAY.log')],
        '''# A-c744 whole-original I64 endpoint attachment

The unchanged A original now has 414 accepted necessary endpoint inequalities,
plus its separate I64 height inequality. The complete physical implication is
in [the hand attachment](native_checkpoint/family/WHOLE_ORIGINAL_ENDPOINT_ATTACHMENT.md).
It combines the complete old components 0/1/2/4 with the actual-AB 16/25 theorem
and the strict-CD equality blocker, then transports the separately published
seven-round source endpoints. No selected source SAT predicate or auxiliary
bound is transported. The source I slope remains [-1,1].

The first whole-original use appends one ordinary round with 268 positive
unit-weight deductions and zero residual. Both the agent and the independent
root record replay pass, with identical OPEN final state. The original path
and inherited inward-row choice remain unchanged. The earlier pre-round v2
entry failure, the corrected v3 source, all full reports and the root log are
preserved. The prior 813-deduction source proof and older source ancestry are
reused by exact identity; they are not claimed as newly repeated here.

[Native evidence and reproduction](native_checkpoint/README.md) includes the
immutable 38-file selection and explicit published dependency aliases. Root
checks rehash all 55 aliases and the exact member set. Extraction alone does
not install the historical native paths. The original and mask remain OPEN;
the A165 consumer continuation is separate. Totals remain 222/231 original
cells and 8/32 masks CLOSED. No Lean, Lake or CI was run.
'''))
    results.append(finalize(c, ch, [
        ('d_work/C887_THREE_TERMINAL_ROOT_SOURCE_REVIEW.json', 'ROOT_SOURCE_AND_PHYSICAL_REVIEW.json'),
        ('b_work/C887_THREE_TERMINAL_PACKET_VERIFICATION_RECEIPT.json', 'PACKET_VERIFICATION_RECEIPT.json')],
        '''# Three exact C887 terminal exclusions

The complete retained 91-node original C887 cover now excludes leaves 29, 30
and 64 and retains 70 OPEN leaves. The accepted D/G separator must have a
strictly positive vertical component. The three selected normals contradict
that requirement, including the zero-slope face. The unchanged independent
record core checks each exact zero-round terminal.

The [hand attachment](native_checkpoint/code/HAND_ATTACHMENT.md), complete new
manifest, three changed records, full exact report, observed exit receipt,
peer review and root physical/source review are preserved. Every other node
payload is byte-identical. All nine proxy, six SAT and three closed-angle
unions retain every alternative and exact child state. The new gate reuses
the accepted historical 57 weighted rounds explicitly, after checking 543
source identities; those old weighted rounds are not repeated. The earlier
negative center-coordinate experiment remains separate diagnostic evidence.

[Native evidence and reproduction](native_checkpoint/README.md) identifies
the previously published C height packet and all 88 unchanged payload aliases.
Root packet verification observed exit zero and rechecked the entire member
set and historical aliases. This thin continuation needs the published old
packet. No whole original or mask is closed: totals remain 222/231 originals
and 8/32 masks CLOSED. No numerical search, Lean, Lake or CI was run.
'''))
    write(ROOT / 'd_work/A_ENDPOINT_C_TERMINALS_PACKAGING.json', {
        'status': 'PASS_BYTE_IDENTICAL_REVIEWED_PUBLICATION_SELECTION',
        'packets': results, 'mathematical_arithmetic_repeated': False})
    print(json.dumps(results))

if __name__ == '__main__':
    main()
