#!/usr/bin/env python3
"""Freeze the complete-A1 consequence delta without copying published inputs."""
from pathlib import Path
import argparse, hashlib, json, shutil

HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parent.parent


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--plan', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    plan_path = args.plan.resolve()
    plan = json.loads(plan_path.read_text())
    assert plan['schema'] == 'complete_A1_consequence_thin_publication_plan_v1'
    assert plan['new_original_cells'] == plan['new_masks'] == 0
    assert plan['original_status'] == 'OPEN' and plan['component1_status'] == 'CLOSED'
    assert plan['live_frontier_included'] is False and plan['no_base_bytes_duplicated'] is True
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    mappings, inventory = {}, {}
    for group in (plan['base_A_portable_archive']['reused_files'], plan['new_payload_files']):
        for original, entry in group.items():
            path = Path(original)
            assert path.is_absolute() and path.is_relative_to(WORKSPACE)
            relative = Path('payload') / path.relative_to(WORKSPACE)
            item = dict(path=str(relative), sha256=entry['sha256'])
            assert original not in mappings or mappings[original] == item
            mappings[original] = item
            inventory[str(relative)] = entry['sha256']
    assert len({entry['path'] for entry in mappings.values()}) == len(mappings)
    for original, entry in plan['new_payload_files'].items():
        source = Path(original)
        assert sha(source) == entry['sha256'] and source.stat().st_size == entry['bytes']
        target = out / mappings[original]['path']
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        assert sha(target) == entry['sha256']
    directories = {}
    for original, entry in mappings.items():
        before, after = Path(original).parent, Path(entry['path']).parent
        while before.is_relative_to(WORKSPACE):
            if str(before) in directories:
                assert directories[str(before)] == str(after)
            directories[str(before)] = str(after)
            if before == WORKSPACE:
                break
            before, after = before.parent, after.parent
    dump(out / 'BINDINGS.json', dict(files=mappings, directories=directories))
    shutil.copyfile(plan_path, out / 'PUBLICATION_PLAN.json')
    for name in ('replay_portable_a1_checkpoint_v1.py', 'materialize_a1_checkpoint.py',
                 'build_compact_a1_checkpoint.py', 'prepare_compact_a1_checkpoint.py'):
        shutil.copyfile(HERE / name, out / name)
    proof = {key: plan[key] for key in (
        'original_id', 'original_path', 'original_status', 'component1_status',
        'reference_commit', 'reference_binding', 'complete_component1',
        'actual_component3_probe', 'expected_source', 'expected_actual', 'original_necessary_row')}
    proof.update(schema='complete_A1_original_consequence_portable_proof_v1', mask='001/00',
        all_nine_original_squares_retained=True, original_corner_predicates=36,
        original_pair_predicates=36, closed_shared_faces_retained=True,
        actual_AB_BC_EF_FG_and_strict_CD_retained=True,
        old_saved_PASS_reports_are_not_premises=True,
        conditional_A3_shared_bounds_not_valid_on_whole_original=True,
        new_original_cells=0, new_masks=0, lean_lake_ci_run=False)
    dump(out / 'PUBLICATION_PROOF.json', proof)
    (out / 'README.md').write_text('''# Complete A1 complement and its original-wide height consequence

This thin checkpoint preserves the complete component1 exclusion for registered
original `positive-c744bc031d40ee64`, its necessary row `y_D-y_B<=3/5`, and the
first exactly replayed use of that row on the unchanged component3 root.
Component1 has757 nodes and566 excluded leaves. Component3 and the whole
registered original remain OPEN. No original or mask credit is granted.

The physical hand proof, immutable original definition, exact certificates,
source binding, literal controls and native reports are inventoried below.
The full published OPEN A packet supplies unchanged older inputs by hash.
No mathematical source byte, literal row, rational value or original path is
rewritten during materialization or replay. Old reports identify expected
results; the portable protocol repeats the complete source arithmetic.

Use Python3.12 with `-B -S`. Materialize into a fresh directory outside
`/workspace` so the archived read guards remain unchanged:

```sh
python3.12 -B -S materialize_a1_checkpoint.py --delta DELTA --a-base PUBLISHED_A_PACKET --output /tmp/a1_packet
python3.12 -B -S /tmp/a1_packet/replay_portable_a1_checkpoint_v1.py --packet /tmp/a1_packet --output /tmp/a1_replay
```

The A3 consumer first runs the frozen older complete-A1 checker in a separate
guarded process, then repeats its older A3 conditional-bound dependency and
checks the new unsplit actual-use record. The source checker cannot consume
the newly derived row. The literal/scope controls are separately repeated.
The derived order `y_D<=y_I` requires the component3 closed-domain row and is
never asserted on the whole original.

Path transport changes only exact inventoried filename/directory references.
Raw input bytes and hashes are unchanged. Known archived diagnostic outputs
are routed into fresh output subtrees disjoint from every frozen input.
Packet writes, unlisted packet reads, external workspace reads and numerical
imports are forbidden; every source child installs the same restrictions.
Every inventoried input is rehashed at completion. No Lean, Lake or CI runs.

The archive is intended for streaming tar/xz creation without a raw tar file.
`DELTA_MANIFEST.json` binds the shipped files; `INPUT_MANIFEST.json` binds the
assembled proof, including reused published members. `PUBLICATION_PLAN.json`
records each exact base member and each new source. The actual portable
receipt is an outer publication attachment, never an input premise.
''')
    for path in out.rglob('*'):
        if path.is_file():
            inventory[str(path.relative_to(out))] = sha(path)
    dump(out / 'INPUT_MANIFEST.json', dict(schema='complete_A1_thin_assembled_input_inventory_v1',
        files=dict(sorted(inventory.items())), external_workspace_reads_forbidden=True,
        numerical_imports_forbidden=True))
    release = dict(schema='complete_A1_consequence_thin_delta_files_v1',
        files={str(p.relative_to(out)): sha(p) for p in sorted(out.rglob('*')) if p.is_file()},
        assembled_input_manifest_sha256=sha(out / 'INPUT_MANIFEST.json'),
        plan_sha256=sha(plan_path), mathematical_payload_files=plan['new_payload_files_count'],
        mathematical_payload_uncompressed_bytes=plan['new_payload_uncompressed_bytes'],
        reused_A_aliases=plan['base_A_portable_archive']['files_reused'],
        base_members_not_duplicated=True, new_original_cells=0, new_masks=0)
    dump(out / 'DELTA_MANIFEST.json', release)
    print(json.dumps({key: value for key, value in release.items() if key != 'files'}, indent=2))


if __name__ == '__main__':
    main()
