#!/usr/bin/env python3
"""Preserve completed bounded attempts and exact bytes, without a new replay."""
from pathlib import Path
import hashlib
import json
import shutil

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / 'repo/research/nine/computer_assisted'
A = ROOT / 'ac_work/recovery_20261105_reset2'


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def read(p):
    return json.loads(Path(p).read_text())


def write(p, value):
    with Path(p).open('x') as f:
        json.dump(value, f, indent=2, sort_keys=True)
        f.write('\n')


def copy(source, target, expected=None):
    source, target = Path(source), Path(target)
    assert source.is_file() and not source.is_symlink() and not target.exists()
    if expected is not None:
        assert sha(source) == expected, str(source)
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, target)
    assert source.read_bytes() == target.read_bytes()


def finish(folder, prose, evidence):
    with (folder/'README.md').open('x') as f:
        f.write(prose)
    copy(__file__, folder/'package_reviewed_evidence.py')
    members = {str(p.relative_to(folder)):dict(bytes=p.stat().st_size,sha256=sha(p))
               for p in sorted(folder.rglob('*')) if p.is_file()}
    write(folder/'PUBLICATION_MANIFEST.json',dict(
        schema='completed_bounded_exact_attempt_preservation_v1',files=members,
        evidence=evidence,source_bytes_unchanged=True,arithmetic_repeated_for_publication=False,
        external_published_dependencies_required=True,cold_self_contained_proof_claimed=False,
        new_original_cells=0,new_masks=0,lean_lake_ci_run=False))
    return dict(folder=str(folder.relative_to(ROOT/'repo')),files=len(members)+1,
                bytes=sum(p.stat().st_size for p in folder.rglob('*')if p.is_file()),
                publication_manifest_sha256=sha(folder/'PUBLICATION_MANIFEST.json'))


def main():
    ap = DEST/'a_c744_finite_existing_correlations_v2'
    bp = DEST/'b16_two_bounded_negative_screens_v1'
    assert not ap.exists() and not bp.exists()
    ap.mkdir(); bp.mkdir()
    ready = A/'A165_CORRELATED_NATIVE_DELTA_READY_V2.json'
    assert sha(ready) == '932aab328ba3154392b9c234f8644933f45ef1faedadafbdbf4bec571e6d5309'
    ar = read(ready)
    for name,e in ar['files'].items():
        p=A/name
        assert p.stat().st_size==e['bytes']
        copy(p,ap/'delta'/name,e['sha256'])
    copy(ready,ap/'delta'/ready.name)
    copy(A/'A165_CORRELATED_CUTOFF_SCOPE_NOTE.md',ap/'CUTOFF_SCOPE_NOTE.md',
         '08dae94e37f617c61e2502b1936c4b72354d59fb728ef40e67bd1739f5e0d664')
    for name in ['README.md','TREE_ASSEMBLY.json','DEPENDENCIES.json','INPUT_MANIFEST.json']:
        copy(A/'a165_existing_correlations_native_delta_v2'/name,ap/'readable_evidence'/name)
    for name in ['A165_CORRELATED_DELTA_ROOT_FRESH_EXTRACTION_V2.json',
                 'A165_CORRELATED_DELTA_ROOT_BYTE_AND_PREFIX_AUDIT_V2.json',
                 'A165_EXISTING_CORRELATED_ROWS_ROOT_SOURCE_REVIEW.json',
                 'A165_EXISTING_CORRELATED_ROWS_V2_ROOT_SOURCE_REVIEW.json']:
        copy(ROOT/'d_work'/name,ap/'root_review'/name)
    copy(ROOT/'b_work/A165_CORRELATED_DELTA_INDEPENDENT_SOURCE_REVIEW.json',
         ap/'peer_review/A165_CORRELATED_DELTA_INDEPENDENT_SOURCE_REVIEW.json',
         '996314429e4dd22504134fe8b42c3b26765aa2d6691f5332c01fec525d12c563')
    for p in (ROOT/'b_work').glob('A165_CORRELATED_DELTA_INDEPENDENT_SOURCE_REVIEW.md'):
        copy(p,ap/'peer_review'/p.name)
    exact = read(A/'A165_CORRELATED_EXISTING_CONTINUATION_EXACT_REPLAY_V2.json')
    observed = read(A/'A165_CORRELATED_EXISTING_OBSERVED_EXECUTION_V2.json')
    assert (exact['nodes'],exact['excluded_leaves'],exact['open_leaves'],exact['fresh_rounds'],exact['fresh_deductions'],exact['fresh_printed_rows_checked'])==(165,118,14,12,10,19)
    assert observed['independent_gate_session']==77810 and observed['independent_gate_exit']==0
    root_checks = [read(ROOT/'d_work'/name) for name in (
        'A165_CORRELATED_DELTA_ROOT_FRESH_EXTRACTION_V2.json',
        'A165_CORRELATED_DELTA_ROOT_BYTE_AND_PREFIX_AUDIT_V2.json')]
    assert all(x['status'].startswith('PASS_')for x in root_checks)
    a_summary=finish(ap,'''# A-c744: completed finite continuation with existing correlations

The retained 165-node cover has 118 excluded leaves and fourteen OPEN leaves,
unchanged by this bounded continuation. Six payloads receive twelve freshly
checked rounds with ten deductions and nineteen premises. All 159 other
payloads are identical. Every original initial state, prior round prefix,
closed face and all 33 complete unions are retained.

The deductions use the already accepted whole-original I64 height row,
certified Cartesian pair differences and coordinate endpoints. Three premises
use the height row and six use pair differences. All printed multipliers are
positive exact rationals and cancel with zero residual. The unchanged exact
core and complete status graph pass independently; the observed gate exits
zero. The prior full 165-node arithmetic is explicitly reused, not repeated.

The attempt allowed at most four rounds on each of fourteen leaves. Every
changed leaf stabilized within two rounds under the chosen minimum rounded
improvement of 1/2000. This is not a claim that smaller improvements are
impossible. CUTOFF_SCOPE_NOTE.md preserves that qualification without editing
the frozen source, report, archive or earlier preparation prose. No additional
exclusion was found; this A tactic is stopped under the Bf14-first directive.

The 44-member compact archive preserves all six changed payloads, the complete
new tree manifest, 159 exact prior aliases, source v1/v2, the complete fresh
report, raw logs and observed exits. It also preserves the initial preparation
failure: the constructor used bound_hi_ instead of the existing bound_up_
name, before creating a changed leaf or new manifest. The corrected v2 changes
only those names and protocol paths; the original row-count assertions remain.

Root independently extracted the archive to a fresh directory and verified
every member, all 165 prior payloads, the six exact round-prefix extensions and
the full new manifest. A separate peer source/byte review passes. To reproduce,
first restore the published prior A165 tree from
`a_c744_i64_retained_cover_continuation_v1` and its A1 base; then use the included
transport and byte-only materializer. Native aliases are still needed for
arithmetic. This is not a cold standalone proof.

The whole original and mask remain OPEN. The fixed totals remain 222/231
originals and 8/32 masks CLOSED. No LP, new split, new row family, Lean, Lake,
compilation or CI was run for this continuation or publication.
''',dict(exact_report_sha256=sha(A/'A165_CORRELATED_EXISTING_CONTINUATION_EXACT_REPLAY_V2.json'),
         observed_exact_gate_exit=0,archive_sha256=ar['files']['a165_existing_correlations_native_delta_v2.tar.xz']['sha256'],
         archive_members=44,unchanged_payloads=159,changed_payloads=[151,152,154,156,157,163],
         continued_manifest_sha256=exact['continued_manifest_sha256'],nodes=165,excluded_leaves=118,open_leaves=14,
         proposal_cutoff='1/2000 after outward2^-20 rounding',tactic_stopped=True))

    source=ROOT/'b_work/b16_bounded_negative_screens_v1'
    assert sha(source/'MEMBER_MANIFEST.json')=='c1eab31c452ccabef78cc6577569fb73f05cae40b3df609f79d2d94a375da520'
    for p in sorted(source.iterdir()):
        assert p.is_file() and not p.is_symlink()
        copy(p,bp/'native_evidence'/p.name)
    archive=ROOT/'b_work/B16_BOUNDED_NEGATIVE_SCREENS_V1.tar.xz'
    copy(archive,bp/'B16_BOUNDED_NEGATIVE_SCREENS_V1.tar.xz',
         'e4da09d43629719f64d46f4fafb3fe0fc963bd1d559c845edc550e30c3411e19')
    copy(ROOT/'d_work/B16_BOUNDED_NEGATIVE_SCREENS_ROOT_ARCHIVE_AUDIT.json',
         bp/'root_review/B16_BOUNDED_NEGATIVE_SCREENS_ROOT_ARCHIVE_AUDIT.json',
         '85a1d27d04c76eb6612792db9f6522de95eb85c843aa7cccbe9a941605cae842')
    b_summary=finish(bp,'''# B16: two completed bounded screens

These preserved attempts found no whole-leaf or whole-original closure. Their
full exact inputs, reports, bounds, source snapshots and observed exits are
retained in a seventeen-member archive. Root independently read every archived
regular member and checked it against the inventory and original source bytes.
The archive and its frozen explanatory record are unchanged.

The first screen constructs all eight physical D/G alternatives at every one
of the fourteen OPEN leaves in the accepted 45-node merged I21/I22 cover.
The unchanged exact core checks the complete alternatives and excludes 45
immediately, leaving 67 survivors across all fourteen parents. At most four
further ordinary propagation steps produce no additional exclusion. No parent
is closed. The bounded process exits zero and is stopped.

The second screen intersects the stronger accepted regional root bounds with
the thirteen OPEN final states of a separately frozen 127-node candidate over
the same closed merged region. Six states gain sixteen intervals; seven are
unchanged. No existing interval or accepted row-guard terminal is reached in
at most four propagation steps. This process also exits zero and is stopped.
Its source arithmetic was still pending when the screen ran, and that exact
historical qualification is preserved. Its later complete replay is separate
evidence; this archive does not silently promote candidate ancestry.

The first screen's forty-five excluded D/G children are not new original
cells. The fourteen OPEN parents are also distinct from B16's fourteen already
proved I quarters. The merged I21/I22 region and the whole B16 original remain
OPEN. Neither screen installs a tree, numerical state or new row family.

Reproduction needs the cited accepted B16 ancestry and frozen external inputs
listed in native_evidence/README.md. This compact negative-result record is not
a cold standalone proof. It prevents repeating exhausted bounded tactics while
preserving their useful exact deductions and complete complement accounting.
Totals remain 222/231 originals and 8/32 masks CLOSED. No LP, Lean, Lake,
compilation or CI was run.
''',dict(archive_sha256=sha(archive),archive_members=17,
         exact_DG_alternatives=112,immediate_DG_exclusions=45,DG_survivors=67,
         no_complete_DG_parent_excluded=True,second_screen_open_states=13,
         second_screen_improved_intervals=16,no_second_screen_terminal=True,
         observed_screen_exits=[0,0],both_tactics_stopped=True))
    out=dict(status='PASS_BYTE_IDENTICAL_COMPLETED_BOUNDED_ATTEMPT_PUBLICATION_SELECTION',
             packets=[a_summary,b_summary],new_original_cells=0,new_masks=0)
    write(ROOT/'d_work/A165_CORRELATIONS_B16_NEGATIVE_PACKAGING.json',out)
    print(json.dumps(out),flush=True)


if __name__=='__main__':
    main()
