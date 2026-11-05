#!/usr/bin/env python3
"""Preserve exact reviewed evidence and held source preparation without replay."""
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
        json.dump(value, stream, indent=2, sort_keys=True); stream.write('\n')

def build(source, name, manifest_name, expected, extra_members, attachments, readme):
    source = ROOT / source; folder = DEST / name
    assert not folder.exists()
    manifest = source / manifest_name
    assert sha(manifest) == expected
    inventory = json.loads(manifest.read_text())
    actual = {str(p.relative_to(source)) for p in source.rglob('*') if p.is_file()}
    assert actual == set(inventory['files']) | {manifest_name} | set(extra_members)
    assert not any(p.is_symlink() for p in source.rglob('*'))
    for rel, entry in inventory['files'].items():
        p = source / rel
        assert p.resolve().is_relative_to(source.resolve())
        assert p.stat().st_size == entry['bytes'] and sha(p) == entry['sha256']
    for rel, expected_hash in extra_members.items():
        assert sha(source / rel) == expected_hash
    folder.mkdir()
    shutil.copytree(source, folder / 'native_checkpoint')
    for rel in actual:
        assert (source / rel).read_bytes() == (folder / 'native_checkpoint' / rel).read_bytes()
    for source_name, target_name in attachments:
        p = ROOT / source_name; q = folder / target_name
        q.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(p, q); assert sha(p) == sha(q)
    shutil.copyfile(__file__, folder / 'package_reviewed_evidence.py')
    (folder / 'README.md').write_text(readme)
    members = {str(p.relative_to(folder)): {'bytes':p.stat().st_size, 'sha256':sha(p)}
               for p in sorted(folder.rglob('*')) if p.is_file()}
    write(folder / 'PUBLICATION_MANIFEST.json', {
        'schema':'reviewed_exact_continuation_and_held_source_publication_v1',
        'source_manifest':manifest_name, 'source_manifest_sha256':expected,
        'files':members, 'total_bytes':sum(v['bytes'] for v in members.values()),
        'native_source_bytes_unchanged':True, 'new_original_cells':0, 'new_masks':0,
        'mathematical_arithmetic_repeated_by_packaging':False,
        'numerical_job_started_by_packaging':False, 'lean_lake_ci_run':False})
    return {'folder':str(folder.relative_to(ROOT / 'repo')), 'files':len(members)+1,
            'bytes':sum(p.stat().st_size for p in folder.rglob('*') if p.is_file()),
            'publication_manifest_sha256':sha(folder / 'PUBLICATION_MANIFEST.json')}

def main():
    results=[]
    results.append(build('b_work/b16_interval_continuation_publication_v1',
        'b16_interval_terminal_continuation_v1', 'INPUT_MANIFEST.json',
        '0c8dc46bb00053660535704b72b664f58326de4dcc7d7c86a3784f0f19e7f88d', {}, [
            ('d_work/B16_INTERVAL_CONTINUATION_ROOT_PUBLICATION_REVIEW.json','ROOT_PUBLICATION_REVIEW.json'),
            ('b_work/B16_INTERVAL_CONTINUATION_PUBLICATION_VERIFICATION_RECEIPT.json','PACKET_VERIFICATION_RECEIPT.json')],
        '''# B16 exact interval-terminal continuation

Fourteen more leaves are excluded in the retained 45-node I21/I22 cover.
The full fresh independent replay checks all 21 rounds, 2,324 deductions,
7,865 rows and every complete child union. It reports 16 excluded and 14 OPEN
leaves. Root observed replay session16960 exit0. The independent source and
physical review, exact byte/cover audit and fresh byte materialization pass.

Only fourteen zero-round terminal payloads change. Every other payload,
initial state, old round and complete proxy/angle alternative is retained.
Thirteen terminals have empty necessary center intervals; one has an empty
F/I vertical-difference intersection. These are unchanged accepted rules.

[The complete evidence and reproduction guide](native_checkpoint/README.md)
preserves the raw report, log, constructor, screen and exact 31 published
payload aliases. The regional parent remains only the merged I21/I22 part
of original negative-16a2fc93c8d133f0. The separate fourteen-quarter proofs
remain unchanged. No whole original or mask is closed, and totals remain
222/231 originals and 8/32 masks CLOSED. No numerical search, Lean, Lake or CI.
'''))
    results.append(build('global_work/strict011_strengthened_discovery_v1',
        'strict_011_strengthened_discovery_preparation_v1', 'SOURCE_FREEZE.json',
        '9df42998d72dc39e358883fc44582e9dc69152f4f5dd20cc1de42d4e5e039ab3',
        {'HELD_PILOT_LAUNCH.json':'84ba95ee37a7b03aa19119589de768f7fd09f105b271e81780d9cf69fcf8a693'}, [
            ('d_work/STRICT011_STRENGTHENED_DISCOVERY_ROOT_REVIEW.json','ROOT_SOURCE_REVIEW.json'),
            ('ac_work/recovery_20261105_reset2/STRICT011_STRENGTHENED_DISCOVERY_V1_INDEPENDENT_REVIEW.json','INDEPENDENT_SOURCE_REVIEW.json'),
            ('ac_work/recovery_20261105_reset2/STRICT011_STRENGTHENED_DISCOVERY_V1_INDEPENDENT_REVIEW.md','INDEPENDENT_SOURCE_REVIEW.md'),
            ('d_work/prepare_strict011_strengthened_when_slot_ready_v1.py','prepare_pilot_when_slot_ready.py'),
            ('d_work/STRICT011_STRENGTHENED_CAPACITY_READINESS_V1.json','CAPACITY_READINESS.json')],
        '''# Reviewed strengthened strict 011/00 numerical preparation

This immutable preparation attaches the reviewed four-product corner rows
and strict C/H/I theorem guards to the unchanged accepted numerical core.
Exact dual/residual arithmetic, objective generation and complete atomic
4/8/2 storage retain their accepted source bytes. Root and independent source
reviews pass. No real numerical solve is claimed by this checkpoint.

The 69-member source freeze preserves the no-solver controls, fresh whole-root
seed and installed HiGHS option readback. The held pilot uses one whole-root
node, one round, 108 objectives, two cut passes and a two-second LP limit.
A complete independent replay and a new positive real-LP corner weight are
required for its actual-use result. Exit3 preserves valid OPEN evidence when
that positive use is absent. A first true theorem guard requires fresh scalar
replay; synthetic controls do not discharge that gate.

[Native source, controls and held argv](native_checkpoint/README.md) retain
explicit dependencies on the published foundation, complete reader, corner
layer and guard packets. The separate capacity launcher rehashes all450 input
members and both source reviews, then checks the process inventory immediately
before launch. It starts no job while eight numerical jobs or unclassified
Python workers are present. Publication does not itself start the waiter.

All nine originals, 36 corners, 36 pairs, exact five marked links and strict
radius remain in the whole representative caller. The current checkpoint
adds no original or mask credit. No Lean, Lake or CI was run.
'''))
    results.append(build('global_work/strict011_c_height_complement_note_v1',
        'strict_011_c_height_complement_preparation_v1', 'PREMISE_BINDINGS.json',
        '06aba6fc518e44d1b859bccb9cc81b6ab57ef5b2df91970f654ba9fe8ab3fd79', {}, [
            ('d_work/STRICT011_C_HEIGHT_COMPLEMENT_ROOT_REVIEW.json','ROOT_PHYSICAL_AND_SOURCE_REVIEW.json'),
            ('ac_work/recovery_20261105_reset2/STRICT011_C_HEIGHT_COMPLEMENT_V1_INDEPENDENT_REVIEW.json','INDEPENDENT_PHYSICAL_AND_SOURCE_REVIEW.json'),
            ('ac_work/recovery_20261105_reset2/STRICT011_C_HEIGHT_COMPLEMENT_V1_INDEPENDENT_REVIEW.md','INDEPENDENT_PHYSICAL_AND_SOURCE_REVIEW.md')],
        '''# Prepared strict 011/00 original-C height cover

The complete physical caller and accepted C-label universal theorem imply
abs(yC-yB)+abs(yD-yC)>21/100. The exact maximum identity yields four closed
covering alternatives: yD-yB, 2yC-yB-yD, yB+yD-2yC or yB-yD is at least21/100.
All equality faces and overlaps remain present. The cover is justified on
physical strict callers; it does not claim to cover an arbitrary LP box.

[The full hand proof](native_checkpoint/C_HEIGHT_COMPLEMENT.md), independent
fixed-form reconstruction and symbolic all-quadrant proof are preserved.
Root and peer physical/source reviews pass; 94 damaged literal/caller/reuse
controls are rejected. The two exact caller documents retain every original,
all actual links and strict weak bits, with whole-caller symmetry unchanged.

This is a prepared consequence. First actual use still requires fresh scalar
replay and a separately reviewed complete ancestry adapter for the new union
kind. The existing 4/8/2 checker and frozen numerical driver are unchanged.
No scalar or optimizer is run by this packet; no original or mask is closed.
'''))
    register=ROOT/'repo/research/nine/gates/A2_00100_FIXED_FRONTIER.json'
    assert sha(register)=='3dfaff7a880ab358930fb0ea835a1fdbe9959711f3c08ac47ee9817e7c693dde'
    write(ROOT/'d_work/B16_STRICT011_PREPARATION_PACKAGING.json',
          {'status':'PASS_REVIEWED_EXACT_NATIVE_PUBLICATION_SELECTION','packets':results})
    print(json.dumps(results))

if __name__=='__main__':
    main()
