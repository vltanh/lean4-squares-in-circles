#!/usr/bin/env python3
"""Independent fixed arithmetic and source binding for the symmetric row."""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
SCALE = 10**18


class I:
    def __init__(self, lo=0, hi=None):
        if isinstance(lo, I):
            self.lo, self.hi = lo.lo, lo.hi
        else:
            self.lo = F(lo)
            self.hi = F(lo if hi is None else hi)
        assert self.lo <= self.hi

    def __add__(self, other):
        q = I(other)
        return I(self.lo+q.lo, self.hi+q.hi)
    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -I(other)

    def __rsub__(self, other):
        return I(other) + -self

    def __mul__(self, other):
        q = I(other)
        v = [x*y for x in (self.lo, self.hi) for y in (q.lo, q.hi)]
        return I(min(v), max(v))
    __rmul__ = __mul__

    def __truediv__(self, other):
        q = I(other)
        assert q.lo*q.hi > 0
        return self * I(1/q.hi, 1/q.lo)

    def __rtruediv__(self, other):
        return I(other) / self

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        z = I(1)
        for _ in range(n):
            z = z*self
        return z


def root(x):
    x = I(x)
    assert x.lo >= 0
    def bounds(t):
        k = isqrt(t.numerator*SCALE*SCALE//t.denominator)
        assert k*k*t.denominator <= t.numerator*SCALE*SCALE
        assert (k+1)**2*t.denominator > t.numerator*SCALE*SCALE
        h = k if k*k*t.denominator == t.numerator*SCALE*SCALE else k+1
        return F(k, SCALE), F(h, SCALE)
    return I(bounds(x.lo)[0], bounds(x.hi)[1])


checks = []


def gt(name, value, threshold=0):
    v, t = I(value), I(threshold)
    assert v.lo > t.hi, (name, v.lo, t.hi)
    checks.append({"name": name, "lower": str(v.lo), "upper": str(v.hi),
                   "threshold": str(t.hi), "strict_reserve": str(v.lo-t.hi)})


Q = F(9789, 2500)
half = F(1, 2)
d = root(Q/2)-half
a0 = root(Q-F(1, 4))-half


def a(b):
    return root(Q-(I(b)+half)**2)-half


def label(b):
    b = I(b)
    return F(".03965")+F("3.85510")*b-F("1.49748")*b*b-F("1.89442")*a(b)*b


def D(b):
    b = I(b)
    u = a(b)+half
    return F("3.85510")-F("2.99496")*b-F("1.89442")*(a(b)-b*(b+half)/u)


def Dp(b):
    b = I(b)
    u = a(b)+half
    return -F("2.99496")+F("1.89442")*(2*(b+half)/u+b*Q/u**3)


def ratio(B, z):
    B, z = I(B), I(z)
    R, q = a(B)+half, Q-2*B
    return (Q-B-half)/(R*q)+z/(q*root(q-z*z))


# Reconstruct the quartic from the eliminated radical identity rather than
# loading its coefficients from either author's program.
R = Q-1
p, g, gamma = F("1.49748"), F("1.89442"), F(".89765")
C = 2*F(".03965")+F("3.85510")-p/2+g/2-gamma
quartic = [4*C, g*(4*R-2), C-2*p*R, -3*g/2, p/2]
printed = list(map(F, ["161761/12500", "572020119/31250000",
                       "-42944417/7812500", "-284163/100000", "37437/50000"]))
assert quartic == printed
assert C == F("3.23522")


def derivative(coefficients):
    return [k*v for k, v in enumerate(coefficients) if k]


def evaluate(coefficients, x):
    z = F(0)
    for q in reversed(coefficients):
        z = z*x+q
    return z


p1 = derivative(quartic)
p2 = derivative(p1)
p3 = derivative(p2)
gt("quartic third derivative at3.28", evaluate(p3, F("3.28")))
gt("quartic curvature at3.28", evaluate(p2, F("3.28")), 29)
u0 = F("3.3974")
gt("quartic reference value", evaluate(quartic, u0), ".001948")
gt("quartic reference derivative lower", evaluate(p1, u0), "-.0015")
gt("quartic reference derivative upper", -evaluate(p1, u0), "-.0015")
gt("quartic square completion", F(".001948")-F(".0015")**2/58, ".0019")
gt("left radical bracket", Q-F("1.4")**2-F("1.398")**2)
gt("right radical bracket", Q-F(".6")**2-F("1.885")**2)
gt("upper radical-sum bracket", F("3.42")**2-4*R)
gt("aligned strict reserve", F(".0019")/(F("3.42")**2+4), ".00012")

gt("label third derivative floor", 3*F("1.8")*F("3.9")/8, 2)
gt("global D minimum completion", F(".6248")-F(".0311")**2/4, ".6245")
gt("D at half", D(".5"), ".6248")
gt("Dprime half lower", Dp(".5"), "-.0311")
gt("Dprime half upper", -Dp(".5"))
gt("D at diagonal upper", -D(d), "-1.176")
gt("D at diagonal lower", D(d), "1.16")

for b, v in ((".15", ".94"), (".3", ".84"), ("0", "1.05")):
    gt("positive contact speed at"+b, F(v)**2-(Q-2*(a(b)+F(b))))
for x, y in (("1.176", ".84"), ("1.02", ".94"), (".85", "1.05")):
    gt("positive derivative product"+x+"*"+y, 1-F(x)*F(y))

c = F(400, 391)
gt("small B chord", label(".15")-label(0)-c*F(".15"))
gt("small B concavity endpoint", -Dp(".15"))
gt("scalar derivative at .6", c-D(".6"))
gt("scalar curvature at .6", Dp(".6"), ".5")
gt("scalar reference .85", label(".85")-c*F(".85"), "-.15954")
gt("scalar reference derivative lower", D(".85")-c, "-.005")
gt("scalar reference derivative upper", c-D(".85"), "-.005")
gt("small positive rectangle reserve", c+F(".03965")-F(".15957"), ".903")

gt("no low target middle stationary", F(".6245")**2*(Q-F("1.34")-F(".01")), 1)
gt("no low target exterior stationary", F(".649")**2*(Q-F("1.34")-F(".16")), 1)
gt("speed derivative .56", F(".29")*(Q-F("1.4")-F(".16"))-F("1.176")*F(".4"))
gt("speed derivative .66", F(".93")*(Q-F("1.8")-F(".16"))-F("1.176")*F(".4"))
gt("no stationary at .56", F(".63268")**2*(Q-F("1.4")-F(".06")**2), 1)
gt("no stationary at .66", F(".6933")**2*(Q-F("1.8")-F(".16")**2), 1)
gt("ratio at .7,.06", -ratio(".7", ".06"), "-.702")
gt("ratio at .7,.16", -ratio(".7", ".16"), "-.727")
gt("D at .67", D(".67"), ".703")
gt("D at .7", D(".7"), ".7365")
gt("Dprime at .7", Dp(".7"), "1.2")
qm = Q-F("1.8")
Rm = root(Q-F("1.4")**2)
vm = root(qm-F(".16")**2)
jp = (Q-1)/(Rm*qm**2)+(Q-F("1.2"))*F("1.4")/(Rm**3*qm)
jp += F(".16")*(2/(qm**2*vm)+1/(qm*vm**3))
gt("global ratio derivative", -jp, "-1.2")
gt("source diagonal boundary speed", F("1.16")**2*(Q-F("1.8")-F(".16")), 1)
gt("negative .7 contact impossible", F(".5")-F(".4")*F(".765")+F("1.399")*F(".644"), ".9")

label_file = ROOT / "proof_integration/wrong_0011011_labels.json"
labels = json.loads(label_file.read_text())
assert labels["independent_roles"]["4"]["O+"] == [3965, 0, 385510, -149748, -189442]

sources = [
    "proof_integration/WRONG_0011011_SYMMETRIC_ALIGNED_OUTER_HAND_PROOF.md",
    "proof_integration/verify_wrong_0011011_symmetric_aligned_hand.py",
    "proof_integration/wrong_0011011_symmetric_aligned_hand_arithmetic.json",
    "proof_integration/WRONG_0011011_SYMMETRIC_OUTER_WHOLE_ANGLE_HAND_PROOF.md",
    "proof_integration/verify_wrong_0011011_symmetric_outer_whole_angle.js",
    "proof_integration/wrong_0011011_symmetric_outer_whole_angle_arithmetic.json",
    "proof_integration/wrong_0011011_labels.json",
]


def sha(b):
    return hashlib.sha256(b).hexdigest()


bindings = {p: sha((ROOT/p).read_bytes()) for p in sources}
temp = Path(tempfile.mkdtemp(prefix="m5_symmetric_outer_independent_"))
replays = []
for executable, checker, expected in (
    ("python", sources[1], sources[2]),
    ("node", sources[4], sources[5]),
):
    copied = temp / Path(checker).name
    shutil.copy2(ROOT/checker, copied)
    run = subprocess.run([executable, str(copied)], cwd=temp,
                         capture_output=True, check=True)
    assert not run.stderr, run.stderr
    expected_bytes = (ROOT/expected).read_bytes()
    # The restored whole-angle JSON has one extra final LF. Preserve it;
    # require exact equality after removing final LFs and also parse equality.
    assert run.stdout.rstrip(b"\n") == expected_bytes.rstrip(b"\n"), expected
    assert json.loads(run.stdout) == json.loads(expected_bytes), expected
    obj = json.loads(run.stdout)
    assert obj["status"] == "PASS"
    n = obj["strict_comparisons"] if "strict_comparisons" in obj else obj["checks"]
    replays.append({"checker": checker, "expected_json": expected,
                    "comparisons": n, "byte_identical": run.stdout == expected_bytes,
                    "identical_except_final_lfs": True,
                    "exact_json_value_match": True,
                    "stdout_sha256": sha(run.stdout), "exit_code": run.returncode})
    (temp/Path(expected).name).write_bytes(run.stdout)

result = {
    "status": "PASS",
    "scope": "Independent review and binding of the symmetric edge4 OO(+,-) whole-angle proof and its aligned quartic import.",
    "independent_strict_comparisons": len(checks),
    "quartic_coefficient_identities": 5,
    "quartic_coefficients": list(map(str, quartic)),
    "role_label_exact_match": True,
    "source_hashes": bindings,
    "author_replays": replays,
    "checks": checks,
}
(HERE/"wrong_0011011_symmetric_outer_independent_audit.json").write_text(json.dumps(result, indent=2)+"\n")
print(json.dumps({"status": "PASS", "independent_strict_comparisons": len(checks),
                  "author_comparisons": [r["comparisons"] for r in replays],
                  "all_replays_identical_except_final_lfs": True}, indent=2))
