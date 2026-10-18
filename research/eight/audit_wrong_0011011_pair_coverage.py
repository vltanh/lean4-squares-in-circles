#!/usr/bin/env python3
"""Finite, exact coverage audit; this does not check analytic pair inequalities."""
from __future__ import annotations

import hashlib
import itertools
import json
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).with_name("wrong_0011011_pair_coverage_audit.json")
P = "proof_integration/"
M = "m5_agent/hand_conversion/"
G = "global_attack/hand_conversion/"
PREFIX = "WRONG_0011011_"


def proof(directory, stem):
    return directory + PREFIX + stem + "_HAND_PROOF.md"


def digest(path):
    p = ROOT / path
    assert p.is_file(), f"missing bound source: {path}"
    return hashlib.sha256(p.read_bytes()).hexdigest()


label_path = P + "wrong_0011011_labels.json"
data = json.loads((ROOT / label_path).read_text())
assert data["word"] == [0, 0, 1, 1, 0, 1, 1]
assert Fraction(data["Q"]) == Fraction(9789, 2500)
assert Fraction(data["gamma"]) == Fraction(17953, 20000)
assert data["denominator"] == 100000
assert data["features"] == ["1", "a", "b", "b^2", "a*b"]

word = tuple(data["word"])
labels = {int(i): row for i, row in data["independent_roles"].items()}


def opposite(s):
    return "+" if s == "-" else "-"


for i, row in list(labels.items()):
    j = (2 - i) % 7
    reflected = {k + s: row[k + opposite(s)]
                 for k in "CO" for s in "+-"}
    if j in labels:
        assert labels[j] == reflected
    else:
        labels[j] = reflected
assert set(labels) == set(range(7))
for i in range(7):
    for k in "CO":
        for s in "+-":
            assert labels[(2-i) % 7][k+s] == labels[i][k+opposite(s)]
    assert word[i] == word[(1-i) % 7]


def sign_character(s):
    return "+" if s == 1 else "-"


# These conditions follow analytically in the accompanying note.
sign_assignments = [s for s in itertools.product((-1, 1), repeat=7)
                    if s[0] == 1 and s[2] == -1
                    and all(not (word[i] == 0 and s[i] == -1
                                 and s[(i+1) % 7] == 1)
                            for i in range(7))]
assert len(sign_assignments) == 24
edge_signs = {(i, sign_character(s[i])+sign_character(s[(i+1) % 7]))
              for s in sign_assignments for i in range(7)}
expected_signs = {
    0: {"++", "+-"}, 1: {"+-", "--"}, 2: {"--", "-+"},
    3: {"++", "+-", "-+", "--"}, 4: {"++", "+-", "--"},
    5: {"++", "+-", "-+", "--"}, 6: {"++", "-+"},
}
assert edge_signs == {(i, s) for i, ss in expected_signs.items() for s in ss}
assert len(edge_signs) == 19

cases = {(i, ss, kinds) for i, ss in edge_signs
         for kinds in ("CC", "CO", "OC", "OO")}
assert len(cases) == 76


def reflect(case):
    i, ss, kinds = case
    return ((1-i) % 7, opposite(ss[1])+opposite(ss[0]), kinds[::-1])


sign_order = {"++": 0, "+-": 1, "-+": 2, "--": 3}


def ordering(case):
    i, ss, kinds = case
    return i, sign_order[ss], kinds


def canonical(case):
    return min((case, reflect(case)), key=ordering)


for c in cases:
    assert reflect(c) in cases
    assert reflect(reflect(c)) == c
orbits = {}
for c in cases:
    orbits.setdefault(canonical(c), set()).add(c)
fixed = {c for c in cases if reflect(c) == c}
assert fixed == {(4, "+-", "CC"), (4, "+-", "OO")}
assert len(orbits) == 39
assert sum(c[2] == "CC" for c in orbits) == 10
assert sum(c[2] == "OO" for c in orbits) == 10
assert sum(c[2] in ("CO", "OC") for c in orbits) == 19

# Four signed projections: source +f, target +e, target +f, source -e.
axis_reflection = {1: 3, 2: 4, 3: 1, 4: 2}
axis_cases = {(c, a) for c in cases for a in range(1, 5)}
axis_orbits = {frozenset(((c, a), (reflect(c), axis_reflection[a])))
               for c, a in axis_cases}
assert len(axis_cases) == 304 and len(axis_orbits) == 152
assert all(len(orb) == 2 for orb in axis_orbits)

cc = proof(P, "ALL_CORE_CORE")
same_mixed = proof(P, "SAME_SIGN_MIXED_ZERO")
opp_mixed = proof(P, "OPPOSITE_MIXED_ZERO")
same_outer = proof(P, "SAME_OUTER_ZERO")
four_mixed = proof(M, "EDGE3_FOUR_WHOLE_MIXED_FAMILIES")
pair_proofs = {}
for case in orbits:
    i, ss, kinds = case
    if kinds == "CC":
        pair_proofs[case] = [cc]
    elif word[i] == 0 and kinds in ("CO", "OC"):
        pair_proofs[case] = [same_mixed if ss == "++" else opp_mixed]
    elif kinds == "OO" and word[i] == 0:
        if ss == "++":
            pair_proofs[case] = [same_outer]
        elif i == 0:
            pair_proofs[case] = [proof(P, "ASYMMETRIC_OPPOSITE_OUTER_ZERO")]
        else:
            assert (i, ss) == (4, "+-")
            pair_proofs[case] = [proof(P, "SYMMETRIC_OUTER_WHOLE_ANGLE")]

pair_proofs.update({
    (2, "--", "CO"): [proof(M, "EDGE2_NEGATIVE_CORE_TO_OUTER")],
    (2, "--", "OC"): [proof(M, "EDGE2_NEGATIVE_CORE_SIDE"),
                         proof(M, "EDGE2_NEGATIVE_CORE_CORNER")],
    (2, "-+", "CO"): [proof(M, "EDGE2_CORE_TO_POSITIVE_OUTER")],
    (2, "-+", "OC"): [proof(M, "EDGE2_OUTER_TO_POSITIVE_CORE")],
    (2, "--", "OO"): [proof(P, "NEGATIVE_OUTER_QUARTER")],
    (2, "-+", "OO"): [proof(P, "OPPOSITE_OUTER_EDGE2_QUARTER")],
    (3, "++", "CO"): [proof(M, "EDGE3_POSITIVE_CORE_TO_POSITIVE_OUTER")],
    (3, "++", "OC"): [four_mixed],
    (3, "+-", "CO"): [four_mixed],
    (3, "+-", "OC"): [four_mixed],
    (3, "-+", "CO"): [proof(M, "EDGE3_NEGATIVE_CORE_TO_POSITIVE_OUTER")],
    (3, "-+", "OC"): [proof(M, "EDGE3_OUTER_TO_POSITIVE_CORE")],
    (3, "--", "CO"): [four_mixed],
    (3, "--", "OC"): [proof(M, "EDGE3_OUTER_TO_NEGATIVE_CORE")],
    (3, "++", "OO"): [proof(M, "EDGE3_POSITIVE_OUTER_PAIR")],
    (3, "+-", "OO"): [proof(P, "POSITIVE_NEGATIVE_OUTER_QUARTER")],
    (3, "-+", "OO"): [proof(P, "EDGE3_OPPOSITE_AXES12"),
                         proof(P, "EDGE3_OPPOSITE_AXES34")],
    (3, "--", "OO"): [proof(P, "EDGE3_NEGATIVE_OUTER_QUARTER")],
})
assert set(pair_proofs) == set(orbits)
assert all(pair_proofs[c] for c in cases if c in orbits)

# The point of this audit is to bind a full analytic cover, not to substitute
# a count for the independent mathematical reading of any cited manuscript.
bound_paths = {label_path}
for paths in pair_proofs.values():
    bound_paths.update(paths)
import_paths = {
    proof(M, "ALIGNED_MIXED_QUARTER"),
    proof(M, "EDGE2_MIXED_QUARTER_STRIP"),
    proof(P, "SYMMETRIC_ALIGNED_OUTER"),
}
bound_paths.update(import_paths)
hashes = {path: digest(path) for path in sorted(bound_paths)}

# Check the exact role-label reflection in every individual cost, without
# relying merely on the previously checked polynomial identity.
records = []
for c in sorted(orbits, key=ordering):
    i, ss, kinds = c
    reflected = reflect(c)
    j, rr, rk = reflected
    source = labels[i][kinds[0]+ss[0]]
    target = labels[(i+1) % 7][kinds[1]+ss[1]]
    assert labels[j][rk[0]+rr[0]] == target
    assert labels[(j+1) % 7][rk[1]+rr[1]] == source
    records.append({
        "canonical_pair": list(c), "quarter": word[i],
        "source_unsigned_label_numerators": source,
        "target_unsigned_label_numerators": target,
        "label_denominator": 100000,
        "orbit": [list(x) for x in sorted(orbits[c], key=ordering)],
        "proof_manuscripts": pair_proofs[c],
        "retained_axes_covered": [1, 2, 3, 4],
    })

gamma = Fraction(data["gamma"])
twice_pi_upper = Fraction(710, 113)
assert 7 * gamma - twice_pi_upper == Fraction(823, 2260000) > 0

result = {
    "status": "PASS_FINITE_COVERAGE",
    "scope": "Exact sign/label/reflection/manuscript cover only; component inequalities require their mathematical proofs and independent reviews.",
    "Q": data["Q"], "word": list(word), "gamma": data["gamma"],
    "conditional_cycle_bound": str(7 * gamma),
    "twice_pi_upper": str(twice_pi_upper),
    "conditional_rational_surplus": str(7 * gamma - twice_pi_upper),
    "admissible_sign_assignments": len(sign_assignments),
    "admissible_edge_sign_classes": len(edge_signs),
    "directed_pair_cases": len(cases), "canonical_pair_cases": len(orbits),
    "canonical_kind_counts": {"CC": 10, "mixed": 19, "OO": 10},
    "reflection_fixed_pair_cases": [list(c) for c in sorted(fixed, key=ordering)],
    "directed_axis_cases": len(axis_cases),
    "axis_reflection_orbits": len(axis_orbits),
    "axis_reflection": axis_reflection,
    "edge_sign_classes": {str(i): sorted(ss, key=sign_order.get)
                           for i, ss in expected_signs.items()},
    "label_file": label_path,
    "manuscript_hashes": hashes,
    "explicit_import_manuscripts": sorted(import_paths),
    "canonical_cover": records,
}
OUT.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({k: result[k] for k in
                 ("status", "admissible_edge_sign_classes", "directed_pair_cases",
                  "canonical_pair_cases", "canonical_kind_counts",
                  "directed_axis_cases", "axis_reflection_orbits",
                  "conditional_rational_surplus")}, indent=2))
