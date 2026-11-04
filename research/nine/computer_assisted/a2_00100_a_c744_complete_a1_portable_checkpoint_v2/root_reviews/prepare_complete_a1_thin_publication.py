#!/usr/bin/env python3
"""Publish the frozen complete A1 component checkpoint without ledger credit."""
from pathlib import Path
import hashlib
import json
import shutil

W = Path('/workspace/scratch/f9f48fcfb253')
R = W / 'repo'
S = W / 'ac_work/compact_A1_publication'
REL = 'research/nine/computer_assisted/a2_00100_a_c744_complete_a1_portable_checkpoint_v2'
DEST = R / REL
AUDIT = W / 'd_work/A_C744_COMPLETE_A1_THIN_ARCHIVE_ROOT_AUDIT.json'

def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda: f.read(1048576), b''):
            h.update(b)
    return h.hexdigest()

def copy(src, rel, pin=None):
    assert src.is_file() and not src.is_symlink()
    before = sha(src)
    if pin is not None:
        assert before == pin, src
    out = DEST / rel
    assert not out.exists(), out
    out.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(src, out)
    assert sha(out) == sha(src) == before

def main():
    assert not DEST.exists(), DEST
    audit = json.loads(AUDIT.read_text())
    assert audit['status'] == 'PASS_ROOT_COMPLETE_A1_THIN_ARCHIVE_AND_RECEIPT_AUDIT'
    register = R / 'research/nine/gates/A2_00100_FIXED_FRONTIER.json'
    register_sha = sha(register)
    assert register_sha == 'b805df8706151a4eb43bd8c0912205ffbfd67d8dfb582daf441717e04fd023dc'
    ready = json.loads((S / 'PUBLICATION_READY.json').read_text())
    bindings = json.loads((S / 'TRANSPORT_SOURCE_BINDINGS.json').read_text())
    for rel, item in bindings['files'].items():
        copy(S / rel, rel, item['sha256'])
    for name in ['PUBLICATION_READY.json', 'TRANSPORT_SOURCE_BINDINGS.json']:
        copy(S / name, name)
    for src, item in bindings['source_transport_scripts'].items():
        copy(Path(src), 'source_transport_scripts/' + Path(src).name, item['sha256'])
    copy(AUDIT, 'root_reviews/' + AUDIT.name)
    copy(W / 'd_work/audit_complete_a1_thin_archive_root.py', 'root_reviews/audit_complete_a1_thin_archive_root.py', audit['source_sha256'])
    copy(Path(__file__), 'root_reviews/' + Path(__file__).name)
    members = json.loads((S / 'ARCHIVE_AUDIT.json').read_text())['members']
    for name in ['A_C744_COMPLETE_COMPONENT1_CONSEQUENCE_HAND_PROOF.md',
                 'A_C744_COMPONENT1_CLOSED_NEGATION_DERIVATION.md',
                 'A_C744_COMPONENT1_CLOSED_CONSEQUENCE_BINDING.json']:
        copy(W / 'ac_work/tree' / name, 'physical_proof/' + name, members['payload/ac_work/tree/' + name]['sha256'])

    archive = Path(ready['archive'])
    assert sha(archive) == ready['archive_sha256']
    parts = []
    joined = hashlib.sha256()
    with archive.open('rb') as f:
        for index, chunk in enumerate(iter(lambda: f.read(8 * 1024 * 1024), b''), 1):
            name = archive.name + '.part' + str(index).zfill(3)
            p = DEST / name
            p.write_bytes(chunk)
            joined.update(chunk)
            parts.append(dict(file=name, bytes=len(chunk), sha256=sha(p)))
    assert joined.hexdigest() == ready['archive_sha256']
    assert sum(p['bytes'] for p in parts) == ready['archive_bytes']
    archive_manifest = dict(schema='complete_a1_consequence_thin_archive_v2',
        archive=archive.name, archive_sha256=ready['archive_sha256'], archive_bytes=ready['archive_bytes'],
        parts=parts, extracted_directory='complete_a1_consequence_delta_v2',
        archive_members=859, uncompressed_bytes=607136233,
        delta_manifest_sha256='70c971d00fb804d0765cce66ef540b3c79e18a0eed29b08d5f63793b94eedf4d',
        assembled_input_manifest_sha256='d8ca6d465aa3831e26d6d0149b8ce734a1043c51694f81a9ce9b9a4e3baaf965',
        required_published_base=ready['required_base'],
        all_members_rehashed=True, xz_integrity_passed=True,
        root_archive_audit_sha256=sha(AUDIT), new_original_cells=0, new_masks=0,
        component1_status='CLOSED', whole_original_status='OPEN', lean_lake_ci_run=False)
    (DEST / 'ARCHIVE_MANIFEST.json').write_text(json.dumps(archive_manifest, indent=2, sort_keys=True)+'\n')

    (DEST / 'README.md').write_text('''# A c744: complete component 1, portable consequence checkpoint

The complete component 1 of `positive-c744bc031d40ee64` is excluded by a
fresh isolated exact replay. Its necessary consequence on the unchanged
original is `y_D - y_B <= 3/5`. The actual component 3 consumer freshly
replays the complete source before using that inequality.

The whole original remains OPEN because component 3 is unfinished. This
checkpoint adds **zero original cells and zero masks**. The fixed ledgers
remain **221/231 original cells** and **8/32 masks** closed. It preserves
all nine original squares, 36 corners, 36 physical pairs, five center cones
and the exact marked conditions. No Lean, Lake or CI was run.

## Complete proof and scope

| Independently replayed item | Result |
| --- | --- |
| Complete component 1 cover | 757 nodes; 566 excluded leaves; zero OPEN leaves |
| Component 1 arithmetic | 230 rounds; 74,846 deductions; 134,855 premise rows |
| Actual component 3 source record | Seven rounds; 565 deductions; 1,436 premise rows |
| New A1 consequence in that record | Two weighted occurrences |
| Literal/scope controls | Four valid cases; 17 damaged cases rejected |
| Portable input inventory | 2,249 files; 1,091,622,669 bytes |

Component 1 is the closed alternative `y_B - y_D <= -3/5`. Its complete
exclusion implies `y_D - y_B < 3/5`, and therefore the transported weak
closed inequality. Keeping the excluded equality face is a valid weakening.
Only the original-variable row is transported. The older source checker
cannot consume that row, so there is no circular dependency. Together with
the distinct component 3 condition `y_B + y_D - 2*y_I <= -3/5`, it gives
`y_D <= y_I` within component 3. That conditional order is not asserted on
the whole original or another component.

The physical proof and closed-negation derivation are directly available
under `physical_proof/`. `TRANSPORT_AND_REPLAY.md` records the full source
and replay protocol. `fresh_replay_v2/PORTABLE_RECEIPT.json` binds the fresh
arithmetic reports. Root independently checks the compressed archive,
every shipped member and the report bindings; that byte audit is separate
from the recorded fresh arithmetic replay.

## Reconstruct the exact portable packet

This is a thin archive. It requires the previously published sibling
`a2_00100_a_c744_portable_open_checkpoint`, whose archive SHA-256 is
`e7ddb4f4e5b943a6f69a0aa861f6721ca49835311fa595ef40a10881b62e4343`.
The base bytes are reused without modification. `ARCHIVE_MANIFEST.json`
pins every ordered part and the complete new archive.

1. Join each package's parts in its own manifest order and verify the
   complete SHA-256. Extract both archives into a fresh directory.
2. Use the extracted base's `packet` directory as `--a-base`. The new
   extracted root is `complete_a1_consequence_delta_v2`.
3. With Python 3.12, materialize outside `/workspace` and run the replay
   into a separate fresh output directory:

```sh
python3.12 -B -S complete_a1_consequence_delta_v2/materialize_a1_checkpoint.py \\
  --delta complete_a1_consequence_delta_v2 \\
  --a-base a_c744_portable_open_checkpoint/packet \\
  --output /tmp/a1_packet

python3.12 -B -S /tmp/a1_packet/replay_portable_a1_checkpoint_v2.py \\
  --packet /tmp/a1_packet --output /tmp/a1_replay
```

The new archive has 859 regular members and 63,425,472 compressed bytes;
its SHA-256 is
`8378b765edebbba407e394ed98743193a556255687f7ddb8480bafe31d5710f2`.
It contains 846 new mathematical payload files and reuses 1,392 exact
base-member aliases. The materializer verifies every source hash and
rejects missing members or conflicting aliases. The small outer
`delta_v2/` directory holds provenance metadata, not the complete payload;
extract the archive before materializing.

Every arithmetic child forbids numerical imports, old-workspace reads,
unlisted packet reads and all input mutations. All inputs are rehashed at
completion. The v1 diagnostic-write rejection and its logs are preserved;
v2 changes only one explicitly disjoint output route. Every mathematical
payload hash is unchanged between those transport versions.

The frozen reference register is explicitly historical commit `ec6b94c`.
The publication register retains the later B340 independent review and
the same 231 original definitions and statuses. No whole-mask or closed-Q
promotion follows from this component checkpoint. The eventual `001/00`
whole-mask assembly retains its established strict-radius scope.
''')

    files = {}
    for p in sorted(DEST.rglob('*')):
        if p.is_file():
            files[p.relative_to(DEST).as_posix()] = dict(sha256=sha(p), bytes=p.stat().st_size)
    manifest = dict(schema='a_c744_complete_a1_portable_publication_v2',
        original_id='positive-c744bc031d40ee64', mask='001/00',
        original_path=[['angle',3,1],['angle_cut',[0,'0'],0],['inward_row_escape',[7,8],[4]]],
        package=REL, files=files, archive=archive_manifest,
        register_sha256_before_and_after=register_sha,
        fixed_originals=231, closed_originals=221, open_originals=10,
        fixed_masks=32, closed_masks=8, open_masks=24,
        positional_roots=7915, roadmap_ids=15,
        new_original_cells=0, new_masks=0, whole_original_status='OPEN', component1_status='CLOSED',
        all_nine_originals_retained=True, corners=36, physical_pairs=36, marked_cones=5,
        lean_lake_ci_run=False)
    mp = R / (REL + '_manifest.json')
    assert not mp.exists()
    mp.write_text(json.dumps(manifest, indent=2, sort_keys=True)+'\n')

    h = R / 'research/nine/HANDOFF_A2_FIXED_CLOSURE.md'
    text = h.read_text()
    marker = '## Read first\n\n'
    assert text.count(marker) == 1
    text = text.replace(marker, marker + '''The [complete A1 portable consequence checkpoint](computer_assisted/a2_00100_a_c744_complete_a1_portable_checkpoint_v2/README.md)
freshly excludes all 566 terminal domains of component 1 of A-c744 and
verifies its original-wide consequence `y_D-y_B<=3/5` in the actual
component 3 consumer. The isolated replay checks 757 nodes, 74,846 source
deductions and all 2,249 assembled inputs. Root verifies xz integrity and
all 859 thin-archive members. Component 3 remains unfinished, so the whole
original stays OPEN and this checkpoint earns **zero cells or masks**.
The previously published A packet is an explicit byte-pinned dependency.

''', 1)
    h.write_text(text)
    p = R / 'research/nine/PROGRESS.md'
    text = p.read_text()
    marker = '## D821 complete native proof; portable acceptance pending\n'
    assert text.count(marker) == 1
    text = text.replace(marker, '''## A-c744 complete component 1: portable consequence accepted

The [complete A1 portable checkpoint](computer_assisted/a2_00100_a_c744_complete_a1_portable_checkpoint_v2/README.md)
excludes every one of 566 terminal domains in the 757-node component 1
tree. Fresh exact replay checks 230 rounds, 74,846 deductions and 134,855
premise rows. Its original-wide necessary consequence `y_D-y_B<=3/5`
is then used twice in the independently checked component 3 source record.
The older source checker cannot consume that consequence.

The isolated replay rehashes all 2,249 assembled inputs. Root separately
checks xz integrity, all 859 archive members, every outer source binding
and the exact fresh receipt. The thin archive reuses only hash-identical
members of the accepted A OPEN packet. Component 3 remains OPEN; no whole
original or mask is newly closed. Counts remain **221 CLOSED / 10 OPEN**
and **8 CLOSED / 24 OPEN**. The full-mask target remains strict-radius.

''' + marker, 1)
    p.write_text(text)
    assert sha(register) == register_sha
    print(json.dumps(dict(package=REL, files=len(files), bytes=sum(x['bytes'] for x in files.values()),
        manifest_sha256=sha(mp), archive_parts=len(parts), new_original_cells=0, new_masks=0)), flush=True)

if __name__ == '__main__':
    main()
