#!/usr/bin/env python3
"""Copy frozen discovery and completed pilot bytes into a new small packet."""
if not __debug__:
    raise RuntimeError('Publication preparation requires assertions.')
from pathlib import Path
from hashlib import sha256
import json

W = Path('/workspace/scratch/f9f48fcfb253')
HERE = Path(__file__).resolve().parent
OUT = W/'global_work/strict011_discovery_publication_v1'

def digest(path): return sha256(Path(path).read_bytes()).hexdigest()
def write(path, value):
    with path.open('x') as stream:
        json.dump(value,stream,indent=2,sort_keys=True)
        stream.write('\n')

assert not OUT.exists()
OUT.mkdir()
copies = []
def copy(source, relative, expected=None):
    source = Path(source)
    assert source.is_file() and not source.is_symlink()
    before = digest(source)
    if expected is not None:
        assert before == expected
    target = OUT/relative
    assert target.resolve().is_relative_to(OUT)
    target.parent.mkdir(parents=True,exist_ok=True)
    with target.open('xb') as stream:
        stream.write(source.read_bytes())
    assert digest(source) == digest(target) == before
    copies.append(dict(source=str(source),destination=str(relative),bytes=target.stat().st_size,sha256=before))

discovery = W/'global_work/strict_011_discovery_v1'
assert digest(discovery/'SOURCE_FREEZE.json') == 'ddfedb0223c21441359d9b23d1cf49c77c7a87800d9e4f61e1b8f016abf44965'
freeze = json.loads((discovery/'SOURCE_FREEZE.json').read_text())
assert len(freeze['files']) == 93
for relative, entry in freeze['files'].items():
    assert (discovery/relative).stat().st_size == entry['bytes']
    copy(discovery/relative,Path('discovery')/relative,entry['sha256'])
copy(discovery/'SOURCE_FREEZE.json','discovery/SOURCE_FREEZE.json')
pilot = W/'repo/research/nine/.runs/strict011_representative_first_real_phase_v1'
completion = json.loads((pilot/'DISCOVERY_COMPLETION.json').read_text())
assert completion['status'] == 'PASS_FRESH_EXACT_DISCOVERY_CHECKPOINT'
assert (completion['nodes'],completion['excluded_leaves'],completion['open_leaves']) == (5,1,3)
assert not completion['whole_mask_proved_by_exact_tree'] and completion['automatic_mask_credit'] == 0
assert digest(pilot/'manifest.json') == '94dacdafea838579c1bf81b74b64685a2729679549173ef47ee67a3310e84a78'
pilot_files = sorted(p for p in pilot.rglob('*') if p.is_file())
assert len(pilot_files) == 12
for source in pilot_files:
    copy(source,Path('actual_pilot')/source.relative_to(pilot))
copy(Path(str(pilot)+'.log'),'actual_pilot_run.log')
for name in ('ACTUAL_LP_FIRST_USE_HAND_REVIEW.md','ACTUAL_LP_FIRST_USE_REVIEW.json','audit_actual_lp_pilot.py'):
    copy(HERE/name,Path('first_use_review')/name)
for name in ('STRICT011_DISCOVERY_INDEPENDENT_SOURCE_REVIEW.md','STRICT011_DISCOVERY_INDEPENDENT_SOURCE_REVIEW.json'):
    copy(W/'ac_work/tree'/name,Path('reviews')/name)
copy(W/'d_work/STRICT011_DISCOVERY_ROOT_LAUNCH_REVIEW.json','reviews/STRICT011_DISCOVERY_ROOT_LAUNCH_REVIEW.json',
     '38e15afde89393b760d623a092b559ad59e6fbe3162ca5bf9a8bacad38d76ee7')
copy(HERE/'replay_first_real_use.py','replay_first_real_use.py')
copy(Path(__file__),'prepare_publication.py')
readme = '''# Fresh strict-011 discovery and first actual LP certificate

This checkpoint preserves the standalone numerical discovery implementation,
its independent exact and storage controls, and its first completed real LP
pilot. It adds no closed original cell or complete mask. The first pilot covers
the full representative root with one four-way proxy union: one conditional
branch is excluded and all three remaining branches are explicitly OPEN.

## Physical and proof scope

The root is the complete strict-radius `011/00` caller with all nine original
squares, 36 original corners, 36 physical pairs and five marked cones. Its
representative restrictions are justified by the separately reviewed whole-
caller reflection and H/I-swap equivalence. The published foundation is commit
`58bb59bac06714502b9438e795d61588a5a45671`, package
`strict_011_rebuilt_foundations_v3`, checkpoint manifest
`ac389f6184af6503294a13fb30c1da82e38d052a5d579bf43ccd4a0017b0485b`.
No legacy 001 original-cell root, large-gap normalization, actual BC link or
D/G guard is imported. No conditional two-link theorem is used in this pilot.

The numerical LP supplies candidate weights only. The independent rational
checker reconstructs every physical row, pays any coefficient residual using
proved absolute variable bounds, and accepts a contradiction only for a
strictly positive exact reserve. Bound proposals use the same exact residual
payment and outward rational rounding. All proxy, SAT and angle splits retain
their complete closed four-, eight- or two-way alternatives before search.
Content-addressed immutable records and an atomic manifest preserve the last
complete frontier if a write fails.

## First actual result

Root session 14074 was observed to exit 0. The exact pilot has five nodes,
one excluded leaf and three OPEN leaves. Its actual LP dual uses four nonzero
weights, each exactly `1/4`, on the two A/B inset tangents, the actual-AB mask
row and the negative-x AB proxy row. All 54 weighted coefficients are exactly
zero; the weighted right-hand side is `-1/2`. The exact reserve is `1/2` and
the residual payment is zero. This run does not exercise a nonzero residual.
The hand derivation is preserved in `first_use_review/`.

All twelve completed-pilot files are copied byte for byte, including the
unreferenced initial child record retained by the atomic checkpoint mechanism.
The live bounded search is deliberately outside this packet. Its eventual
progress must pass its own complete exact gate before being reported.

## Discovery and control provenance

`discovery/SOURCE_FREEZE.json` pins all 93 frozen source/control members. Its
historical status records that it was frozen before any real LP run; this
publication adds the separate actual-use evidence without editing that freeze.
The v2 numerical driver differs from v1 only by explicit HiGHS `threads=1`.
The no-solve option preflight checks the installed SciPy forwarding source and
actual HiGHS option readback. The front-end warning was not suppressed and is
preserved in `actual_pilot_run.log`.

The exact controls cover rational acceptance, rejected damaged duals, complete
4/8/2 pending alternatives, and injected failures before and after atomic
manifest replacement. Numerical results and recorded historical reports are
not substitutes for the independent arithmetic replay below.

## Clean exact replay

From a repository checkout with the already published foundation package:

```sh
python -B -S research/nine/computer_assisted/strict_011_discovery_first_use_v1/replay_first_real_use.py \\
  --foundation research/nine/computer_assisted/strict_011_rebuilt_foundations_v3/checkpoint \\
  --output /tmp/strict011_first_actual_lp_fresh_replay.json
```

The output path must be new and outside both immutable packages. The replay
rehashes both inventories, forbids numerical imports, freshly checks the full
five-node physical cover and whole-caller symmetry identities, independently
reconstructs the four literal rows and quarter-weight sum, then rehashes all
inputs. The historical absolute paths in source-copy receipts and old reports
are provenance strings; the fresh replay reads the supplied local packages.

## Acceptance accounting

This is a discovery-method and first-conditional-certificate checkpoint only.
The source snapshot follows the accepted 222 CLOSED / 9 OPEN original cells
and 8 CLOSED / 24 OPEN masks. Neither ledger changes here. Three pilot domains
remain OPEN, so `whole_mask_proved` is false.
'''
with (OUT/'README.md').open('x') as stream:stream.write(readme)
write(OUT/'SOURCE_COPY_RECEIPT.json',dict(status='PASS_BYTE_IDENTICAL_FROZEN_SOURCE_AND_COMPLETED_PILOT_COPY',
    copied_files=len(copies),copies=copies,live_bounded_output_read=False,
    original_cell_credit=0,whole_mask_credit=0))
files={str(p.relative_to(OUT)):dict(bytes=p.stat().st_size,sha256=digest(p))
       for p in sorted(OUT.rglob('*')) if p.is_file()}
manifest=dict(schema='strict011_discovery_first_actual_use_v1',
    status='FROZEN_SOURCE_AND_FIRST_ACTUAL_CONDITIONAL_CERTIFICATE',
    foundation_commit='58bb59bac06714502b9438e795d61588a5a45671',
    foundation_checkpoint_sha256='ac389f6184af6503294a13fb30c1da82e38d052a5d579bf43ccd4a0017b0485b',
    discovery_source_freeze_sha256=digest(discovery/'SOURCE_FREEZE.json'),
    pilot_manifest_sha256=digest(pilot/'manifest.json'),nodes=5,excluded_leaves=1,open_leaves=3,
    actual_lp_nonzero_weights=4,actual_exact_reserve='1/2',actual_residual_payment='0',
    whole_mask_proved=False,original_cell_credit=0,whole_mask_credit=0,files=files)
write(OUT/'PUBLICATION_MANIFEST.json',manifest)
for entry in copies:
    assert digest(entry['source']) == digest(OUT/entry['destination']) == entry['sha256']
print(json.dumps(dict(status='PASS_PREPARED_COMPACT_PUBLICATION',folder=str(OUT),
    files=len(files),bytes=sum(e['bytes'] for e in files.values()),
    manifest_sha256=digest(OUT/'PUBLICATION_MANIFEST.json'))))
