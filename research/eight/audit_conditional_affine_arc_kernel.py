#!/usr/bin/env python3
"""Independent finite interface audit for conditional angle/axis coverage."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import itertools
import json
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent


def source(name):
    local = HERE / name
    return local if local.is_file() else ROOT / "candidate_hand" / name


BASE = source("verify_affine_arc_hand.js")
COND = source("verify_conditional_affine_arc_hand.js")
EXPECTED_BASE = "1bd04b7b8890f7008108489da6fdf24b947e472eb4873f7523994ce4b81b85ee"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


assert sha(BASE) == EXPECTED_BASE
conditional_sha = sha(COND)
tmp = Path(tempfile.mkdtemp(prefix="m5_conditional_arc_audit_"))


def atan_sum(x, n):
    x = F(x)
    return sum(((-1)**j*x**(2*j+1)/F(2*j+1) for j in range(n+1)), F(0))


def atan_point(x):
    # Direct series, not the production half-angle transformation.
    x = F(x)
    assert 0 <= x <= F(".7")
    return atan_sum(x, 121), atan_sum(x, 120)


def add(x, y):
    return x[0]+y[0], x[1]+y[1]


def neg(x):
    return -x[1], -x[0]


def sub(x, y):
    return add(x, neg(y))


def point(x):
    return F(x), F(x)


pi = (16*atan_sum(F(1,5), 61)-4*atan_sum(F(1,239), 60),
      16*atan_sum(F(1,5), 60)-4*atan_sum(F(1,239), 61))
p2 = pi[0]/2, pi[1]/2

cuts = {
    "0": ["-.5", "-.1"], "1": ["-.3", ".4"],
    "2": [".2", ".5"], "3": ["-.6", "-.2"],
    "4": ["-.2", ".2"], "5": [".1", ".3"],
    "6": ["-.7", "-.4"],
}
differences = {
    "0": ["-.4", "-.2"], "1": [".15", ".35"],
    "2": ["-.1", ".6"], "3": ["0", "0"],
    "4": ["-.7", ".7"], "5": ["-.3", ".1"],
    "6": ["-.65", "-.45"],
}
axes = {"0": [1], "1": [2], "2": [3], "3": [4],
        "4": [1,3], "5": [2,4], "6": [1,2,3,4]}
word = [0,1,0,1,0,1,1]
arcs = []
for role in range(7):
    l, h = map(F, cuts[str(role)])
    assert -1 <= l < h <= 1
    for kind, sign in itertools.product(("C", "O"), (-1, 1)):
        lo, hi = (l, h) if sign == 1 else (-h, -l)
        lo, hi = max(lo, F(0)), min(hi, F(1))
        if lo >= hi:
            continue
        arcs.append({"id": f"r{role}_{kind}_{sign}", "role": role,
                     "kind": kind, "sign": sign, "lo": str(lo), "hi": str(hi),
                     "c": "0", "p": "0", "q": "0"})

fixture = {"Q": "9789/2500", "word": word, "cuts": cuts,
           "arcs": arcs, "gamma": ["0"]*7, "rows": [],
           "difference_ranges": differences, "axis_domains": axes}


def invoke(kernel, payload, name, valid=True):
    inp = tmp / (name+".json")
    inp.write_text(json.dumps(payload)+"\n")
    run = subprocess.run(["node", str(kernel), str(inp)], capture_output=True)
    if not valid:
        assert run.returncode != 0, name
        return {"case": name, "rejected": True}
    assert run.returncode == 0 and not run.stderr, (name, run.stderr.decode())
    out = json.loads(run.stdout)
    (tmp/(name+"_output.json")).write_bytes(run.stdout)
    return out


got = invoke(COND, fixture, "restricted_interface")
assert got["status"] == "INCOMPLETE" and got["failures"] == []
assert got["cover"]["status"] == "INCOMPLETE"
assert all(e["type"] == "angle chain gap" for e in got["cover"]["errors"])


def alpha_ends(arc):
    lo, hi = atan_point(arc["lo"]), atan_point(arc["hi"])
    return (lo, hi) if arc["sign"] == 1 else (neg(hi), neg(lo))


expected = {}
for edge in range(7):
    ss = [a for a in arcs if a["role"] == edge]
    tt = [a for a in arcs if a["role"] == (edge+1) % 7]
    for s, t, axis, r in itertools.product(ss, tt, axes[str(edge)], (-1,1)):
        sl, sh = alpha_ends(s)
        tl, th = alpha_ends(t)
        phi_lo = add(sub(point(F(19,25)), sh), tl)
        phi_hi = add(sub(point(F(710,113)-F(114,25)), sl), th)
        base = (word[edge]*p2[0], word[edge]*p2[1])
        dlo, dhi = map(F, differences[str(edge)])
        if r == 1:
            lo, hi, qlo, qhi = sub(phi_lo, base), sub(phi_hi, base), dlo, dhi
        else:
            lo, hi, qlo, qhi = sub(base, phi_hi), sub(base, phi_lo), -dhi, -dlo
        lo = max(F(0), lo[0], qlo), max(F(0), lo[1], qlo)
        hi = min(F(".7"), hi[0], qhi), min(F(".7"), hi[1], qhi)
        if lo[0] > hi[1]:
            continue
        assert lo[1] <= hi[0], "undecided fixture boundary"
        expected[(edge, s["id"], t["id"], axis, r)] = lo, hi

actual = {(r["edge"], r["source"], r["target"], r["axis"], r["r"]): r
          for r in got["cover"]["chains"]}
assert set(actual) == set(expected)
endpoint_comparisons = 0
point_chains = 0
for key, (lo, hi) in expected.items():
    row = actual[key]
    assert F(row["required_lower"]) <= lo[0]
    assert F(row["required_upper"]) >= hi[1]
    endpoint_comparisons += 2
    if lo == hi == (F(0), F(0)):
        point_chains += 1
        assert row["rows"] == 0
assert point_chains > 0
assert len(got["cover"]["errors"]) == len(expected)
assert got["hypotheses"]["axis_domains"] == [axes[str(i)] for i in range(7)]
assert got["hypotheses"]["difference_ranges"] == [list(map(lambda x: str(F(x)), differences[str(i)])) for i in range(7)]

# With new declarations omitted, the entire old result other than its prose
# scope and the new explicit hypotheses must be identical.
unrestricted = {k: v for k, v in fixture.items()
                if k not in ("difference_ranges", "axis_domains")}
old = invoke(BASE, unrestricted, "base_defaults")
new = invoke(COND, unrestricted, "conditional_defaults")
for key in ("status", "rows", "passed", "failures", "cover", "results"):
    assert old[key] == new[key], key

invalid = []
for name, overrides in (
    ("unknown_range_edge", {"difference_ranges": {"7": ["0", ".1"]}}),
    ("reversed_range", {"difference_ranges": {"0": [".2", ".1"]}}),
    ("outside_frame_range", {"difference_ranges": {"0": ["-.8", ".1"]}}),
    ("empty_axis_list", {"axis_domains": {"0": []}}),
    ("duplicate_axis", {"axis_domains": {"0": [1,1]}}),
    ("unknown_axis", {"axis_domains": {"0": [5]}}),
):
    invalid.append(invoke(COND, dict(fixture, **overrides), name, valid=False))

assert sha(BASE) == EXPECTED_BASE and sha(COND) == conditional_sha
result = {
    "status": "PASS_CONDITIONAL_INTERFACE",
    "base_sha256": EXPECTED_BASE, "conditional_sha256": conditional_sha,
    "base_source": BASE.name,
    "conditional_source": COND.name,
    "scope": "Independent difference-range/original-axis coverage audit on valid positive-length state domains. No analytic pair table is claimed by the deliberately empty-row fixture.",
    "required_angle_chains": len(expected),
    "independent_outward_endpoint_comparisons": endpoint_comparisons,
    "isolated_zero_angle_chains_retained": point_chains,
    "empty_row_fixture_correctly_incomplete": True,
    "default_full_domain_matches_base": True,
    "invalid_declarations_rejected": invalid,
    "fixture": fixture,
}
(HERE/"conditional_affine_arc_kernel_independent_audit.json").write_text(json.dumps(result, indent=2)+"\n")
print(json.dumps({k: result[k] for k in ("status", "required_angle_chains",
                  "independent_outward_endpoint_comparisons",
                  "isolated_zero_angle_chains_retained",
                  "default_full_domain_matches_base")}, indent=2))
