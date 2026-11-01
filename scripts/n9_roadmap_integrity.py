#!/usr/bin/env python3
"""Static roadmap schema integrity ONLY, not a mathematical proof."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[1]/"research/nine"
j=json.loads((root/"gates/ACTIVE_ROADMAP.json").read_text())
g=j["gates"]; d={x["id"]:x for x in g}
assert len(d)==len(g)
assert j["schema"]=="n9_proof_only_v2"
assert j["target_q"]=="1105/256"
assert j["current_active_gate"] in d
assert d[j["current_active_gate"]]["status"]=="OPEN"
for x in g:
    assert x["parent"] is None or x["parent"] in d
    seen=set(); p=x["parent"]
    while p:
        assert p not in seen; seen.add(p); p=d[p]["parent"]
    assert x["status"] in {"OPEN","AVAILABLE_INPUT","BLOCKED","DEFERRED","CERTIFIED"}
print("One proof-only roadmap is structurally consistent; NO mathematical theorem has been checked.")
