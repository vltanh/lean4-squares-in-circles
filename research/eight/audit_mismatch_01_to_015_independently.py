#!/usr/bin/env python3
"""Independent rational domain/charge audit of the 1/10 to 3/200 mismatch gate.

No discovery routines or JavaScript arithmetic are imported.  The state-angle
enclosures use atan(t)=atan(1/2)+atan((2t-1)/(t+2)), not the production
square-root half-angle transformation.  A complete compact coefficient report
is bound to its fixed input and to the previously reviewed kernel.
"""
from collections import defaultdict
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
names = {
    "data": "MISMATCH_01_TO_015_AFFINE_HAND_DATA.json",
    "report": "MISMATCH_01_TO_015_AFFINE_HAND_COMPACT_REPORT.json",
    "kernel": "verify_mismatch_01_to_015_affine_hand.js",
    "theorem": "MISMATCH_01_TO_015_AFFINE_HAND_THEOREM.md",
    "replay": "replay_mismatch_01_to_015_hand.py",
    "author_assembly": "audit_mismatch_01_to_015_hand_assembly.py",
    "author_report": "MISMATCH_01_TO_015_AFFINE_HAND_ASSEMBLY_AUDIT.json",
}
data_path, report_path, kernel_path = (HERE/names[k] for k in ("data", "report", "kernel"))
output_path = HERE/"MISMATCH_01_TO_015_INDEPENDENT_ASSEMBLY.json"


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


before = {HERE/name: digest(HERE/name) for name in names.values()}
assert before[kernel_path] == "6af3d41fe7d404da7dd286c46644160f5444edd3028d864701266e9a4cd18697"
d = json.loads(data_path.read_text())
c = json.loads(report_path.read_text())
word = [0, 1, 0, 1, 0, 1, 1]
gamma = [F(8975928, 10**7)]*5+[F(89759275, 10**8), F(8975917, 10**7)]
beta = F(1, 200)
charged = [0, 2, 3, 4, 5]
assert F(d["Q"]) == F(3915534138, 10**9)
assert d["word"] == word
cuts = {"0": ["0", "1"], "1": ["-4/5", "-1/20"],
        "2": ["0", "1"], "3": ["-1", "0"],
        "4": ["1/20", "4/5"], "5": ["-1", "0"], "6": ["-1", "0"]}
assert d["cuts"] == cuts
assert list(map(F, d["gamma"])) == gamma
assert list(map(F, d["beta"])) == [beta if i in charged else F(0) for i in range(7)]
ranges = {str(i): ["-1/10", "1/10"] if i in charged else ["-7/10", "7/10"]
          for i in range(7)}
assert d["difference_ranges"] == ranges
assert "axis_domains" not in d
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
                    assert covers(groups[key], lo, hi), key
                    chains += 1
                    chains_by_edge[edge] += 1
                    point_chains += (lo == hi)
assert chains == c["cover"]["angle_chains"] == 101280
assert state_domains == 14 and len(arcs) == 335 and len(d["rows"]) == 107196

assert len(c["row_records"]) == len(d["rows"])
polynomials = coefficients = 0
cost_min = None
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

# The sum uses each selected vertex marker once with each sign.  The
# original-axis bound is therefore 2*pi > Gamma + beta*sum(h(abs(d_i))).
# Concavity and h(0)=0 on [0,1/10] give sum h(abs(d_i)) >= h(S).
# At S >= 3/200 use increasing h and its cubic strict lower bound.
gamma_sum = sum(gamma, F(0))
assert gamma_sum == F(125662969, 20000000)
x = F(3, 200)
h_lower = x/2-x*x/4-x**3/12
assert h_lower == F(238191, 32000000)
pi_upper = F(628318531, 100000000)
machin_upper = 32*atan_series(F(1, 5), 6)-8*atan_series(F(1, 239), 3)
assert 2*pi[1] < machin_upper < pi_upper
reserve = gamma_sum+beta*h_lower-pi_upper
assert reserve == F(2287, 6400000000) > 0
assert 1-F(1, 10)**2/2-F(1, 10) > 0  # cos(x)-sin(x)>0 throughout the input range
assert polynomials == 292119 and coefficients == 2468184
assert cost_min == F(576987, 25000000000000)
assert c["minimum_cost_coefficient"] == str(cost_min)
assert c["gamma_sum"] == str(gamma_sum)
full_name = "MISMATCH_01_TO_015_AFFINE_HAND_ARITHMETIC.json"
full_hash = "014c06a9373077acb965a78690669b863214eb42dc650f30619eb63553e60df3"
assert c["sha256"][full_name] == full_hash

# Bind the author assembly's independently reported totals and the exact
# frozen kernel.  Its domain routines and coefficient replay are not imported.
author = json.loads((HERE/names["author_report"]).read_text())
assert author["status"] == "PASS"
assert author["arcs"] == len(arcs) and author["state_unions"] == state_domains
assert author["angle_chains"] == chains and author["rows"] == len(d["rows"])
assert author["polynomials"] == polynomials
assert author["printed_nonnegative_coefficients"] == coefficients
assert F(author["strict_contraction_reserve"]) == reserve
assert author["full_coefficient_replay_sha256"] == full_hash
for name, expected in author["sha256"].items():
    assert digest(HERE/name) == expected
assert all(digest(path) == expected for path, expected in before.items())

result = {
    "status": "PASS_INDEPENDENT_CONDITIONAL_DOMAIN_AND_MISMATCH_ASSEMBLY",
    "scope": "S<=1/10 implies S<3/200 for the stated boundary cycle; G/T cuts and zero-edge signs only; every original forward SAT axis is covered, with no H/D half-tangent or selected-owner premise.",
    "Q": d["Q"], "word": word, "cuts": cuts,
    "difference_ranges": ranges, "original_axis_domains": [[1, 2, 3, 4] for _ in range(7)],
    "arcs": len(arcs), "state_domains": state_domains,
    "angle_chains": chains, "angle_chains_by_edge": chains_by_edge,
    "nonempty_point_angle_chains": point_chains,
    "fixed_rows": len(d["rows"]), "polynomials": polynomials,
    "coefficient_bounds": coefficients, "least_strict_cost_coefficient": str(cost_min),
    "charged_edges": charged, "beta": str(beta), "gamma": list(map(str, gamma)),
    "gamma_sum": str(gamma_sum), "input_S_upper": "1/10", "strict_output_S_upper": "3/200",
    "h_lower_at_output": str(h_lower), "twice_pi_upper": str(pi_upper),
    "contraction_reserve": str(reserve),
    "atan_method": "atan(t)=atan(1/2)+atan((2t-1)/(t+2)); independent alternating terms 0..60/61, outward denominator10^26; no square-root mesh or author imports",
    "sha256": {p.name: value for p, value in before.items()},
    "independent_checker_sha256": digest(Path(__file__)),
    "unchanged_inputs": True,
    "coefficient_replay_scope": "Existing complete frozen replay and previously independently reviewed identical kernel; this audit independently reconstructs all state/range/axis unions and contraction, not a second full coefficient expansion.",
    "full_coefficient_output_sha256": full_hash,
}
output_path.write_text(json.dumps(result, indent=2)+"\n")
print(json.dumps(result, indent=2))
