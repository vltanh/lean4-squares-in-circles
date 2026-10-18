#!/usr/bin/env python3
"""Independent rational domain/charge audit of the first mismatch budget.

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

ap = argparse.ArgumentParser()
ap.add_argument("data")
ap.add_argument("report")
ap.add_argument("kernel")
ap.add_argument("--out", required=True)
args = ap.parse_args()
data_path, report_path, kernel_path, output_path = map(
    lambda s: Path(s).resolve(), (args.data, args.report, args.kernel, args.out))


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


before = {p: digest(p) for p in (data_path, report_path, kernel_path)}
assert before[kernel_path] == "6af3d41fe7d404da7dd286c46644160f5444edd3028d864701266e9a4cd18697"
d = json.loads(data_path.read_text())
c = json.loads(report_path.read_text())
word = [0, 1, 0, 1, 0, 1, 1]
gamma = F(89727, 100000)
beta = F(99, 5000)
charged = [0, 2, 3, 4, 5]
assert F(d["Q"]) == F(3915534138, 10**9)
assert d.get("word", word) == word
assert d["cuts"] == {"1": ["-4/5", "-1/20"],
                     "4": ["1/20", "4/5"], "6": ["-1", "0"]}
assert list(map(F, d["gamma"])) == [gamma]*7
assert list(map(F, d["beta"])) == [beta if i in charged else F(0) for i in range(7)]
assert all(list(map(F, bounds)) == [F(-7, 10), F(7, 10)]
           for bounds in d.get("difference_ranges", {}).values())
assert all(set(axes) == {1, 2, 3, 4}
           for axes in d.get("axis_domains", {}).values())
assert c["status"] == c["cover"]["status"] == "PASS"
assert not c["failures"] and not c["cover"]["errors"]
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
        domain_cache[key] = max(F(0), lo[0]), min(F(7, 10), hi[1])
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
    assert F(row.get("gamma", d["gamma"][edge])) >= gamma
    groups[edge, s["id"], t["id"], row["axis"], row["r"]].append((lo, hi))

chains = 0
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
assert chains == c["cover"]["angle_chains"]

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

# h is concave on [0,.7] and h(0)=0.  S7 and C6 are lower Taylor
# polynomials there.  Their endpoint reserve proves h(x) >= .29*x.
x = F(7, 10)
s7 = x-x**3/6+x**5/120-x**7/5040
c6 = 1-x*x/2+x**4/24-x**6/720
kappa = F(29, 100)
endpoint_reserve = (s7+c6-1)/2-kappa*x
assert endpoint_reserve == F(22020061, 14400000000) > 0
reserve = 7*gamma+beta*kappa*F(2, 5)-F(710, 113)
assert reserve == F(271, 282500000) > 0

# The imported zero-quarter owner corollary can also be reconstructed directly.
# Core avoidance gives a >= 1/2+sqrt(2)/24 > 447/800.  Containment
# gives a < 283/200.  For x <= .4, cos(x)-sin(x) is positive, so b<=a
# gives the same upper bound for either primary margin, without a radial-kind
# or sign restriction.
assert F(141, 100)**2 < 2
a_lower, a_upper = F(447, 800), F(283, 200)
assert F(1, 2)+F(141, 100)/24 == a_lower
assert (a_upper+F(1, 2))**2+F(1, 4) > F(d["Q"])
cos_lower, sin_upper = 1-F(2, 5)**2/2, F(2, 5)
assert cos_lower-sin_upper > 0
primary_upper = (a_upper-F(1, 2)
                 -(a_lower+F(1, 2))*cos_lower
                 +(a_lower-F(1, 2))*sin_upper)
assert primary_upper == F(-711, 20000) < 0
zero_edges = [i for i, k in enumerate(word) if k == 0]
assert zero_edges == [0, 2, 4] and set(zero_edges) <= set(charged)
assert all(digest(path) == value for path, value in before.items())

result = {"status": "PASS_INDEPENDENT_DOMAIN_AND_CHARGE_ASSEMBLY",
          "scope": "Full-SAT first mismatch budget, with only G/T/E tangent cuts; no H/D tangent, small-mismatch or selected-owner premise.",
          "Q": d["Q"], "word": word, "cuts": d["cuts"],
          "arcs": len(arcs), "state_domains": state_domains,
          "angle_chains": chains, "fixed_rows": len(d["rows"]),
          "polynomials": polynomials, "nonnegative_coefficient_bounds": coefficients,
          "least_strict_cost_coefficient": str(cost_min),
          "charged_edges": charged, "beta": str(beta), "gamma": str(gamma),
          "width_chord_coefficient": str(kappa),
          "width_endpoint_reserve": str(endpoint_reserve),
          "resulting_S_upper": "2/5", "contraction_reserve": str(reserve),
          "zero_quarter_edges": zero_edges,
          "excluded_primary_axes": [2, 4],
          "universal_primary_margin_upper": str(primary_upper),
          "atan_method": "atan(t)=atan(1/2)+atan((2t-1)/(t+2)); direct alternating series with terms 0..60/61 and outward denominator 10^26",
          "sha256": {p.name: value for p, value in before.items()},
          "unchanged_inputs": True,
          "full_coefficient_output_hashes": {name: value for name, value in c["sha256"].items()
                                              if name not in (data_path.name, kernel_path.name)}}
output_path.parent.mkdir(parents=True, exist_ok=True)
output_path.write_text(json.dumps(result, indent=2)+"\n")
print(json.dumps(result, indent=2))
