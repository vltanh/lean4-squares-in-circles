#!/usr/bin/env python3
"""Independent rational domain/charge audit of the 13/50 to 1/10 mismatch gate.

No discovery routines or JavaScript arithmetic are imported.  The state-angle
enclosures use atan(t)=atan(1/2)+atan((2t-1)/(t+2)), not the production
square-root half-angle transformation.  A complete compact coefficient report
is bound to its fixed input and to the previously reviewed kernel.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--prepare', metavar='PROVISIONAL_DATA',
                    help='Check geometric unions and rational contraction only; never issue a table PASS.')
args = parser.parse_args()
PREPARATORY = args.prepare is not None
# Independently read after the complete frozen all-row replay passed.
EXPECTED_FULL_REPLAY_SHA256 = '13a7dc18a78aaa4bbdeef9dc0d83b8f0098ba6c0e6e68ba55401d41849ef0f24'
names = {
    "data": "MISMATCH_026_TO_01_AFFINE_HAND_DATA.json",
    "report": "MISMATCH_026_TO_01_AFFINE_HAND_COMPACT_REPORT.json",
    "kernel": "verify_mismatch_026_to_01_affine_hand.js",
    "theorem": "MISMATCH_026_TO_01_AFFINE_HAND_THEOREM.md",
}
if PREPARATORY:
    data_path = Path(args.prepare).resolve()
    kernel_path = HERE.parent/'verify_conditional_affine_arc_hand.js'
    report_path = None
    output_path = HERE/'MISMATCH_026_TO_01_PREPARATORY_REVIEW.json'
    bound_paths = [data_path, kernel_path]
else:
    if EXPECTED_FULL_REPLAY_SHA256 is None:
        raise SystemExit('Final audit locked: the complete frozen coefficient replay has not yet been supplied.')
    data_path, report_path, kernel_path = (HERE/names[k] for k in ("data", "report", "kernel"))
    output_path = HERE/"MISMATCH_026_TO_01_INDEPENDENT_ASSEMBLY.json"
    bound_paths = [HERE/name for name in names.values()]


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


before = {path: digest(path) for path in bound_paths}
assert before[kernel_path] == "6af3d41fe7d404da7dd286c46644160f5444edd3028d864701266e9a4cd18697"
d = json.loads(data_path.read_text())
c = None if PREPARATORY else json.loads(report_path.read_text())
word = [0, 1, 0, 1, 0, 1, 1]
gamma = [F(897582, 10**6)]*7
beta = F(1, 400)
charged = [0, 2, 3, 4, 5]
assert F(d["Q"]) == F(3915534138, 10**9)
assert d["word"] == word
cuts = {"0": ["1/2", "1"], "1": ["-4/5", "-1/20"],
        "2": ["-1", "1"], "3": ["-1", "1"],
        "4": ["1/20", "4/5"], "5": ["-1", "-1/2"], "6": ["-1", "0"]}
assert d["cuts"] == cuts
assert list(map(F, d["gamma"])) == gamma
assert list(map(F, d["beta"])) == [beta if i in charged else F(0) for i in range(7)]
ranges = {str(i): ["-13/50", "13/50"] if i in charged else ["-7/10", "7/10"]
          for i in range(7)}
assert d["difference_ranges"] == ranges
assert "axis_domains" not in d
if not PREPARATORY:
    assert c["hypotheses"] == {"word": word,
                               "difference_ranges": [ranges[str(i)] for i in range(7)],
                               "axis_domains": [[1, 2, 3, 4] for _ in range(7)]}
    assert c["status"] == c["cover"]["status"] == "PASS"
    assert not c["failures"] and not c["cover"].get("errors", [])
    assert c["rows"] == c["passed"] == len(d["rows"])
    assert c["sha256"][data_path.name] == before[data_path]
    assert c["sha256"][kernel_path.name] == before[kernel_path]

arcs = {a["id"]: a for a in d["arcs"]}
assert len(arcs) == len(d["arcs"])
for a in arcs.values():
    assert a["role"] in range(7) and a["kind"] in ("C", "O")
    assert a["sign"] in (-1, 1)
    lo, hi = F(a["lo"]), F(a["hi"])
    assert 0 <= lo < hi <= 1
    if a["kind"] == "C":
        assert hi <= F(6, 7) or lo >= F(6, 7)
    for name in ("c", "p", "q"):
        F(a[name])
    left, right = map(F, cuts[str(a["role"])])
    signed = (lo, hi) if a["sign"] == 1 else (-hi, -lo)
    assert left <= signed[0] < signed[1] <= right


def covers(intervals, lo, hi):
    if lo > hi:
        return True
    reach = lo
    for left, right in sorted(intervals):
        if right < reach:
            continue
        if left > reach:
            return False
        reach = max(reach, right)
        if reach >= hi:
            return True
    return False


state_domains = 0
for role in range(7):
    left, right = map(F, d["cuts"].get(str(role), ["-1", "1"]))
    assert left < right
    for kind in ("C", "O"):
        for sign in (-1, 1):
            lo, hi = (left, right) if sign == 1 else (-right, -left)
            lo, hi = max(F(0), lo), min(F(1), hi)
            if lo >= hi:
                continue
            pieces = [(F(a["lo"]), F(a["hi"])) for a in arcs.values()
                      if (a["role"], a["kind"], a["sign"]) == (role, kind, sign)]
            assert covers(pieces, lo, hi), (role, kind, sign)
            state_domains += 1


def atan_series(z, n):
    return sum(((-1)**j*z**(2*j+1)/F(2*j+1) for j in range(n+1)), F(0))


def signed_atan(z):
    assert abs(z) <= F(1, 2)
    lo, hi = atan_series(abs(z), 61), atan_series(abs(z), 60)
    return (lo, hi) if z >= 0 else (-hi, -lo)


def outward(x, upper=False):
    scale = 10**26
    v = x.numerator*scale//x.denominator
    if upper and F(v, scale) < x:
        v += 1
    return F(v, scale)


half = signed_atan(F(1, 2))
atan_cache = {}


def angle(t):
    t = F(t)
    assert 0 <= t <= 1
    if t not in atan_cache:
        z = (2*t-1)/(t+2)
        lo, hi = signed_atan(z)
        atan_cache[t] = outward(half[0]+lo), outward(half[1]+hi, True)
    return atan_cache[t]


def add(a, b):
    return a[0]+b[0], a[1]+b[1]


def negative(a):
    return -a[1], -a[0]


def subtract(a, b):
    return add(a, negative(b))


def point(x):
    return F(x), F(x)


def alpha(a):
    lo, hi = angle(a["lo"]), angle(a["hi"])
    return (lo, hi) if a["sign"] == 1 else (negative(hi), negative(lo))


p5, p239 = signed_atan(F(1, 5)), signed_atan(F(1, 239))
pi = (16*p5[0]-4*p239[1], 16*p5[1]-4*p239[0])
assert 2*pi[1] < F(710, 113)
p2 = outward(pi[0]/2), outward(pi[1]/2, True)
domain_cache = {}


def required(s, t, k, r):
    key = s["id"], t["id"], k, r
    if key not in domain_cache:
        sl, sh = alpha(s)
        tl, th = alpha(t)
        fl = add(subtract(point(F(19, 25)), sh), tl)
        fh = add(subtract(point(F(710, 113)-F(114, 25)), sl), th)
        base = p2 if k else point(0)
        lo, hi = ((subtract(fl, base), subtract(fh, base)) if r == 1
                  else (subtract(base, fh), subtract(base, fl)))
        lower, upper = map(F, ranges[str(s["role"])])
        if r == -1:
            lower, upper = -upper, -lower
        domain_cache[key] = max(F(0), lo[0], lower), min(F(7, 10), hi[1], upper)
    return domain_cache[key]


groups = defaultdict(list)
for row in d["rows"]:
    edge = row["edge"]
    assert edge in range(7)
    s, t = arcs[row["source"]], arcs[row["target"]]
    assert s["role"] == edge and t["role"] == (edge+1) % 7
    assert row["axis"] in (1, 2, 3, 4)
    assert row["k"] == word[edge] and row["r"] in (-1, 1)
    assert F(row["lambda"]) >= 0
    lo, hi = F(row["lo"]), F(row["hi"])
    assert 0 <= lo <= hi <= F(7, 10)
    assert row["mode"] in ("lower", "upper", "endpoints", "circle")
    if row["mode"] == "circle":
        assert F(row["h"]) > 0
        target = s if row["axis"] in (2, 3) else t
        assert target["kind"] == "O" or F(target["lo"]) >= F(6, 7)
    assert F(row.get("gamma", d["gamma"][edge])) >= gamma[edge]
    groups[edge, s["id"], t["id"], row["axis"], row["r"]].append((lo, hi))

chains = 0
chains_by_edge = [0]*7
point_chains = 0
missing_chains = []
for edge, k in enumerate(word):
    sources = [a for a in arcs.values() if a["role"] == edge]
    targets = [a for a in arcs.values() if a["role"] == (edge+1) % 7]
    for s in sources:
        for t in targets:
            for r in (-1, 1):
                lo, hi = required(s, t, k, r)
                if lo > hi:
                    continue
                for axis in (1, 2, 3, 4):
                    key = edge, s["id"], t["id"], axis, r
                    if not covers(groups[key], lo, hi):
                        missing_chains.append({'edge': edge, 'source': s['id'], 'target': t['id'],
                                               'axis': axis, 'r': r,
                                               'required': [str(lo), str(hi)]})
                    chains += 1
                    chains_by_edge[edge] += 1
                    point_chains += (lo == hi)
assert state_domains == 18
if not PREPARATORY:
    assert not missing_chains, missing_chains
polynomials = coefficients = 0
cost_min = None
if not PREPARATORY:
    assert chains == c["cover"]["angle_chains"]
    assert len(c["row_records"]) == len(d["rows"])
    for premises, costs in c["row_records"]:
        assert costs
        for records, strict in ((premises, False), (costs, True)):
            for degree, lower in records:
                assert isinstance(degree, int) and degree >= 0
                lower = F(lower)
                assert lower > 0 if strict else lower >= 0
                polynomials += 1
                coefficients += degree+1
                if strict:
                    cost_min = lower if cost_min is None else min(cost_min, lower)
    assert polynomials == c["polynomials"] and coefficients == c["coefficients"]
    assert F(c["minimum_cost_coefficient"]) == cost_min

# For actual separating pairs, consistency of vertex markers gives
# 2*pi > Gamma + beta*sum(h(abs(d_i))).  This implication requires the
# final fixed pair-table proof; the preparation mode does not assert it.
# Concavity and h(0)=0 on [0,13/50] give sum h(abs(d_i)) >= h(S).
# If S >= 1/10, increasing h and its cubic strict lower bound contradict
# the following exact rational budget.
gamma_sum = sum(gamma, F(0))
assert gamma_sum == F(3141537, 500000)
x = F(1, 10)
h_lower = x/2-x*x/4-x**3/12
assert h_lower == F(569, 12000)
pi_upper = F(710, 113)
assert 2*pi[1] < pi_upper
reserve = gamma_sum+beta*h_lower-pi_upper
assert reserve == F(18173, 2712000000) > 0
assert 1-F(13, 50)**2/2-F(13, 50) > 0  # h is increasing on the entire input range
if not PREPARATORY:
    assert F(c["gamma_sum"]) == gamma_sum
    full_name = "MISMATCH_026_TO_01_AFFINE_HAND_ARITHMETIC.json"
    assert c["sha256"][full_name] == EXPECTED_FULL_REPLAY_SHA256
assert all(digest(path) == expected for path, expected in before.items())

result = {
    "status": ("PREPARATORY_GEOMETRIC_UNIONS_AND_CONTRACTION_ONLY_NOT_A_TABLE_PROOF"
               if PREPARATORY else "PASS_INDEPENDENT_CONDITIONAL_DOMAIN_AND_MISMATCH_ASSEMBLY"),
    "scope": "Candidate boundary cycle with explicit H/G/T/D/E tangent cuts, both A/B signs, all four original forward SAT axes, and input S<=13/50. The claimed S<1/10 contraction requires the complete fixed pair table.",
    "exact_pair_table_bound_and_reviewed": not PREPARATORY,
    "Q": d["Q"], "word": word, "cuts": cuts,
    "difference_ranges": ranges, "original_axis_domains": [[1, 2, 3, 4] for _ in range(7)],
    "arcs": len(arcs), "state_domains": state_domains,
    "angle_chains": chains, "angle_chains_by_edge": chains_by_edge,
    "nonempty_point_angle_chains": point_chains,
    "complete_geometric_cover": not missing_chains,
    "uncovered_angle_chains": missing_chains,
    "fixed_rows": len(d["rows"]),
    "charged_edges": charged, "beta": str(beta), "gamma": list(map(str, gamma)),
    "gamma_sum": str(gamma_sum), "input_S_upper": "13/50", "conditional_strict_output_S_upper": "1/10",
    "h_lower_at_output": str(h_lower), "twice_pi_upper": str(pi_upper),
    "contraction_reserve": str(reserve),
    "atan_method": "atan(t)=atan(1/2)+atan((2t-1)/(t+2)); independent alternating terms0..60/61, outward denominator10^26; no square-root mesh or author imports",
    "sha256": {p.name: value for p, value in before.items()},
    "independent_checker_sha256": digest(Path(__file__)),
    "unchanged_inputs": True,
}
if not PREPARATORY:
    result.update({
        "polynomials": polynomials, "coefficient_bounds": coefficients,
        "least_strict_cost_coefficient": str(cost_min),
        "coefficient_replay_scope": "Completed frozen full replay and previously independently reviewed identical kernel; this audit independently reconstructs state/range/axis unions and contraction, not a second full coefficient expansion.",
        "full_coefficient_output_sha256": EXPECTED_FULL_REPLAY_SHA256,
    })
output_path.write_text(json.dumps(result, indent=2)+"\n")
print(json.dumps(result, indent=2))
