#!/usr/bin/env python3
"""Independent original-row relabeling and exact closed-complement audit.

The accepted geometric theorem and polynomial table are inherited. This is
an independent caller/equality review and exact identity audit, not a second
polynomial replay and not an exclusion of any remaining full mask.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
G = ROOT / 'global_theorem'
SPEC = G / 'FULL_MASK_TRANSFER_AND_ORIGINAL_ROW_REDUCTION_v2.json'
HAND = G / 'FULL_MASK_TRANSFER_AND_ORIGINAL_ROW_REDUCTION_v2.md'
DEPENDENCIES = G / 'ORIGINAL_ROW_SPECIALIZATION_DEPENDENCY_AUDIT.json'
PINS = {
    SPEC: 'e9090ecd6aeac9de625e6bc44f7cdef049cc9720a05b108c3783a468937cddf3',
    HAND: '6d95730bd97d4a69e6f3028b06b8c5bdb1605334f6f86f92e5c599f9bc09ec50',
    DEPENDENCIES: '563be496bd3e65958f2cbe4a3125ed7c923d2c384cd2de1a9fdfab8a1ca25136',
}
digest = lambda path: sha256(Path(path).read_bytes()).hexdigest()


def main():
    for path, expected in PINS.items():
        assert digest(path) == expected
    spec = json.loads(SPEC.read_bytes())
    dep = json.loads(DEPENDENCIES.read_bytes())
    sources = {str(path): value for path, value in PINS.items()}
    for mapping in (spec['source_sha256'], dep['source_sha256']):
        for path, expected in mapping.items():
            assert path not in sources or sources[path] == expected
            assert digest(path) == expected
            sources[path] = expected
    theorem = ROOT / 'c887_whole_eight_checkpoint_package/opposite_tilt_theorem/HAND_PROOF.md'
    assert sources[str(theorem)] == 'db830ffbebdc807b0e05f78766e0a0509d11418be31b9a7ef0623b212328831a'
    text = theorem.read_text()
    assert 'The three new row links\nneed not be actual projection links or original center-cone links.' in text
    assert text.index('## 6. Equality') < text.index('## 7. The strict original-nine caller')
    assert dep['section_7_actual_AB_BC_attachment_used'] is False
    assert dep['literal_label_substitution'] == dict(A='A', H='B', I='C', D='D', E='E', F='F', G='G')
    assert dep['actual_projection_pairs_required'] == [['E', 'F'], ['F', 'G']]
    assert dep['main_pairs_with_no_actual_projection_assumption'] == [['A', 'B'], ['B', 'C'], ['C', 'D']]
    assert dep['endpoint_cap_pairs'] == [['A', 'E'], ['D', 'G']]
    assert dep['physical_owner_pairs'] == [['A', 'B'], ['B', 'C'], ['C', 'D']]
    assert spec['original_row'] == ['A', 'B', 'C', 'D']
    assert spec['actual_short_chain'] == ['E', 'F', 'G']
    assert spec['complete_domains_without_proved_sign_guard'] == 10
    assert spec['complete_domains_with_proved_opposite_sign_guard'] == 8
    assert spec['closed_same_sign_escape_domains'] == [['theta_A>=0', 'theta_D>=0'], ['theta_A<=0', 'theta_D<=0']]
    assert spec['new_original_cells'] == spec['new_masks'] == 0
    rows = spec['signed_height_escape_rows']
    assert len(rows) == 8
    signs = list(product((-1, 1), repeat=3))
    for row, (s, t, u) in zip(rows, signs):
        assert row['signs'] == [s, t, u]
        assert row['coefficient_order'] == ['y_A', 'y_B', 'y_C', 'y_D']
        assert row['coefficients'] == [-s, s-t, t-u, u]
        assert row['relation'] == '>=' and F(row['rhs']) == F(23, 100)
    expression_checks = max_checks = complement_checks = reflection_checks = 0
    increments = [F(-1), -F(23, 100), F(0), F(23, 100), F(1)]
    angles = [F(-1), -F(1, 2), F(0), F(1, 2), F(1)]
    for ds in product(increments, repeat=3):
        ys = [F(7, 19)]
        for delta in ds:
            ys.append(ys[-1] + delta)
        values = []
        for row, eps in zip(rows, signs):
            value = sum(F(a)*y for a, y in zip(row['coefficients'], ys))
            assert value == sum(F(s)*delta for s, delta in zip(eps, ds))
            expression_checks += 1
            values.append(value)
        variation = sum(map(abs, ds))
        assert max(values) == variation
        max_checks += 1
        for left, right in product(angles, repeat=2):
            guarded = left*right <= 0 and variation <= F(23, 100)
            same_sign = (left >= 0 and right >= 0) or (left <= 0 and right <= 0)
            height_escape = any(value >= F(23, 100) for value in values)
            assert guarded or same_sign or height_escape
            if not guarded and left*right <= 0:
                assert height_escape
            complement_checks += 1
            assert ((left >= 0 and right <= 0) or (left <= 0 and right >= 0)) == (left*right <= 0)
            assert (-left)*(-right) == left*right
            assert sum(abs(-delta) for delta in ds) == variation
            reflection_checks += 1
    threshold_faces = []
    for eps in signs:
        ds = [F(s)*F(23, 300) for s in eps]
        ys = [F(0), ds[0], ds[0]+ds[1], sum(ds)]
        values = [sum(F(a)*y for a, y in zip(row['coefficients'], ys)) for row in rows]
        assert max(values) == F(23, 100)
        assert values[signs.index(eps)] == F(23, 100)
        threshold_faces.append(list(eps))
    # The closed cap identity and strict owner-slope slack are the two exact
    # constants used after the unchanged source theorem is specialized.
    assert 2*F(211, 4) == 2*F(46) + F(27, 2)
    assert F(231, 1000)-F(23, 100) == F(1, 1000)
    assert 2*F(23, 100)**2 < 1
    frontier_path = ROOT / 'pr11/research/nine/gates/A2_MASK_FRONTIER.json'
    frontier = json.loads(frontier_path.read_bytes())
    assert frontier['mask_count'] == 32
    opened = {row['id'] for row in frontier['rows'] if row['status'] == 'OPEN'}
    assert len(opened) == spec['open_mask_count'] == 24
    reverse = lambda mask: mask.split('/')[0][::-1] + '/' + mask.split('/')[1][::-1]
    expected_classes, remaining = [], set(opened)
    while remaining:
        mask = min(remaining)
        pair = sorted({mask, reverse(mask)})
        assert set(pair) <= remaining
        expected_classes.append(pair)
        remaining -= set(pair)
    assert expected_classes == spec['open_reversal_classes'] and len(expected_classes) == 14
    reversal_identities = 0
    for xs in product((F(-2), F(0), F(3, 2)), repeat=4):
        transformed = [-x for x in reversed(xs)]
        assert [transformed[i+1]-transformed[i] for i in range(3)] == [xs[i+1]-xs[i] for i in reversed(range(3))]
        reversal_identities += 1
    for mask in [''.join(main)+'/'+''.join(short) for main in product('01', repeat=3) for short in product('01', repeat=2)]:
        assert reverse(reverse(mask)) == mask
    for path, expected in sources.items():
        assert digest(path) == expected
    report = dict(schema='independent_original_ABCD_full_angle_specialization_and_mask_transfer_review_v1',
        status='PASS_ORIGINAL_ROW_RELABELING_STRICT_AND_EQUALITY_CLOSED_ESCAPE_COVER',
        reviewer_sha256=digest(__file__), source_sha256=sources,
        accepted_geometric_sections=[1, 2, 3, 4, 5, 6], source_001_only_section7_unused=True,
        literal_label_substitution=dep['literal_label_substitution'], actual_projection_pairs_required=[['E', 'F'], ['F', 'G']],
        endpoint_physical_cap_pairs=[['A', 'E'], ['D', 'G']], all_nine_original_constraints_retained=True,
        independently_rebuilt_signed_height_rows=8, expression_identity_checks=expression_checks,
        max_variation_identity_checks=max_checks, sign_height_complete_union_checks=complement_checks,
        common_reflection_sign_and_variation_checks=reflection_checks, exact_threshold_faces=threshold_faces,
        exact_closed_cap_and_slope_slack_identities_checked=True,
        all32_reversal_involutions_checked=True, four_label_coordinate_reversal_identities=reversal_identities,
        open_mask_reversal_classes=expected_classes, original_mask_denominator=32,
        theorem_input_hashes_rechecked=dep['theorem_immutable_inputs_checked'], polynomial_arithmetic_repeated=False,
        manual_geometric_findings=[
            'The seven theorem labels specialize bijectively to A,B,C,D,E,F,G. Physical disjointness and disk containment are inherited for these originals, while the two unused originals H,I remain physical caller conjuncts.',
            'Only EF and FG require actual horizontal projection. AB,BC,CD supply original cone order and physical owned separation; their actual or strictly weak bit values are not assumptions of source Sections1-6.',
            'All actual separator owners and signed internal angles are covered by the inherited scalar theorem. Common vertical reflection covers the reversed endpoint-sign orientation without changing horizontal supports, exact bits or cone comparisons.',
            'At strict radius the unchanged weighted cap sum is strict. At closed Q, its positive owner-slope slack forces all actual owners aligned; actual row projections are then conclusions, all row halfwidths become1/2, and all three gaps become1.',
            'Any retained strictly weak original main bit contradicts its own now-unit gap and unit support sum. No original001 Section7 attachment, actual AB/BC premise, normalized CD height, shoulder order or G-height condition is used.',
            'Negating the closed guarded theorem gives strict same-sign or height failure. Two closed same-sign conjunctions plus eight closed signed-height halfspaces cover this failure. Zero-angle and threshold overlaps are retained; none is automatically an exclusion.',
            'If opposite endpoint signs are proved on the whole parent, height failure alone follows. This is not a claim that the oversized closed same-sign domains, including zero-angle faces, are separately empty.',
            'The explicit chain-and-frame reversal preserves all original data and transfers only the stated reversed full masks. No implication001-to011 or missing actual short link is inferred.'
        ],
        documentation_note='The final Section4 companion filename omits the v2 suffix; this review binds the explicitly listed v2 JSON and its normative hand/dependency references.',
        scope='Conditional original-row theorem and necessary complete escape cover only; every escape domain remains a separate proof obligation.',
        new_original_cells=0, new_masks=0, numerical_discovery_run=False, lean_lake_ci_run=False)
    output = HERE / 'ORIGINAL_ABCD_OPPOSITE_TILT_SPECIALIZATION_INDEPENDENT_REVIEW.json'
    assert not output.exists()
    output.write_text(json.dumps(report, indent=2) + '\n')
    note = HERE / 'ORIGINAL_ABCD_OPPOSITE_TILT_SPECIALIZATION_INDEPENDENT_REVIEW.md'
    assert not note.exists()
    note.write_text('''# Independent review: original ABCD full-angle specialization

**PASS, with zero full-mask or original-cell credit.** This review binds the
v2 note and companion JSON, the accepted source hand proof, the original mask
contract, and every declared theorem dependency. The adjacent exact review
records their hashes and all algebraic checks. It does not repeat the accepted
878,125 polynomial coefficient checks.

The label substitution is `(A,H,I,D) -> (A,B,C,D)` with E,F,G unchanged.
These are seven distinct physical original squares. The other originals H,I
remain constrained in the nine-square caller. The actual-short-link premises
are exactly EF and FG. Each main pair AB,BC,CD supplies its original cone order
and one actual physical owned separator; no actual horizontal main link is
assumed. This is precisely the input of source Sections1–6.

The positive1/1000 slope surplus is unchanged. At strict radius, the cap sum
is strict and contradicts the row lower bound. At closed Q, equality forces
the actual owners aligned, then actual row projection separation, then all
four main frames aligned and each of their three horizontal gaps equal to1.
The support sum on each such pair is also1. Any one retained strictly weak
main bit therefore contradicts equality. The source's separate001 Section7
argument is unnecessary and is not imported.

The accepted common vertical reflection negates all signed angles and heights
and preserves the original cone and bit comparisons. Thus both opposite-sign
orientations, including zero angles and folded endpoints, are covered.

For surviving nonzero-main/00 callers at closed Q, failure of the theorem's
guards gives either two strictly same-sign endpoint angles or total main-row
variation greater than23/100. The two same-sign conjunctions and eight signed
height halfspaces are complete closed supersets of those failures. Their
zero-angle and threshold intersections are retained. On a parent already
known to have opposite signs, only the eight height domains are necessary;
one must not instead assert that both closed same-sign domains are empty.

The exact audit independently rebuilt all eight affine height expressions,
verified their maximum is total variation, tested all sign/height equality
faces, and checked the explicit chain/frame reversal and14 current open
reversal classes. These identities support the continuous hand argument;
finite sample checks are not substitutes for it.

The note's final Section4 companion filename omits the v2 suffix. The JSON
review explicitly binds `FULL_MASK_TRANSFER_AND_ORIGINAL_ROW_REDUCTION_v2.json`
and its normative hand and dependency references. This is a documentation
pointer issue, not a geometric or cover defect.
''')
    print(json.dumps(dict(status=report['status'], report_sha256=digest(output), hand_review_sha256=digest(note),
        reviewer_sha256=digest(__file__), expression_checks=expression_checks, complement_checks=complement_checks), indent=2))


if __name__ == '__main__':
    main()
