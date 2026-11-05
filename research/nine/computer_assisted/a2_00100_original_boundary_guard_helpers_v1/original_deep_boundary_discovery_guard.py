"""Pure rational discovery guard for the existing all-nine strict cylinder."""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import json
HERE = Path(__file__).resolve().parent / "deep_boundary"
BINDING_SHA = "3887265c54e663e9cde32de02288b6e6a7ba0251c143dc5f55d65439a4101f67"
KIND = "accepted_original_all_nine_deep_boundary_cylinder"
RADIUS = F(1,64)
CENTERS = tuple(map(F, ("-3/2","-1/16","-1/2","-17/16","1/2","-17/16","3/2","-1/16","-1","15/16","0","15/16","1","15/16","-1/2","-1/16","1/2","-1/16")))

@lru_cache(maxsize=1)
def registered():
    assert hashlib.sha256((HERE / "BINDING.json").read_bytes()).hexdigest() == BINDING_SHA
    raw = (HERE / "original_register.json").read_bytes()
    assert hashlib.sha256(raw).hexdigest() == "ea000e84c04675fe22424e5c20d3df9d735d659065349800aef2699170bff604"
    r = json.loads(raw)
    assert r["target_mask"] == "001/00" and r["target_q"] == "1105/256" and r["coverage_certified"] is True
    return {entry["id"]: entry["path"] for entry in r["cells"]}

def evaluate(state):
    roots = registered()
    if state["id"] not in roots or state["path"][:len(roots[state["id"]])] != roots[state["id"]]:
        return None
    assert len(state["angles"]) == 9 and len(state["positions"]) == 18 and len(state["scalar"]) == 36
    if any(not -RADIUS <= lo <= hi <= RADIUS for lo, hi in state["angles"]):
        return None
    if any(not CENTERS[k]-RADIUS <= lo <= hi <= CENTERS[k]+RADIUS
           for k, (lo,hi) in enumerate(state["positions"]) if k not in (10,11)):
        return None
    return dict(kind=KIND, radius="1/64", proof_binding_sha256=BINDING_SHA)
