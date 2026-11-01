#!/usr/bin/env python3
"""Static integrity check for the ONE active n=9 deep roadmap (no Lean/CI).

Run explicitly from the repository root:
    python scripts/n9_roadmap_integrity.py

This checks bookkeeping, dependencies and source evidence pointers, NOT the
mathematical truth of a research gate or a numerical proof certificate.
"""
import json
from pathlib import Path
from collections import Counter

ROOT = Path(__file__).resolve().parents[1]
PREFIX = ROOT / "research" / "nine"
def need(ok, why):
    if not ok:
        raise AssertionError(why)
j = json.loads((PREFIX/"gates/ACTIVE_ROADMAP.json").read_text())
overlay = json.loads((PREFIX/"gates/ACCEPTED_UPDATES.json").read_text())
gates = j["gates"]
by_id = {g["id"]:g for g in gates}
need(len(by_id)==len(gates)==j["gate_count"], "gate IDs not distinct")
need(j["active_gate"] in by_id, "missing active gate")
need(by_id[j["active_gate"]]["status"]=="OPEN", "active gate not OPEN")
need([g["id"] for g in gates if g["parent"] is None]==
     ["G00","G10","G20","G30","G40","G50","G60","G70","G80"], "stage roots have changed")
allowed = {"OPEN","DONE","DEFERRED","BLOCKED"}
for g in gates:
    need(g["status"] in allowed,"unknown status "+g["id"])
    if g["parent"] is not None:
        need(g["parent"] in by_id,"unknown parent "+g["id"])
    need(all(dep in by_id for dep in g["depends"]), "unknown dependency "+g["id"])
    need(g["id"] not in g["depends"], "self dependency "+g["id"])
    if g["status"]=="DONE":
        need(bool(g["links"]),"done but no evidence "+g["id"])
    seen=set()
    p=g["parent"]
    while p is not None:
        need(p not in seen,"parent cycle "+g["id"])
        seen.add(p)
        p=by_id[p]["parent"]
    seen={g["id"]}
    def visit(node):
        need(node not in seen, "dependency cycle "+g["id"])
        seen.add(node)
        for dep in by_id[node]["depends"]:
            visit(dep)
        seen.remove(node)
    for dep in g["depends"]:
        visit(dep)
original=j["original_open_coarse"]
need(len(original)==17 and len(set(original))==17,"17 original open parents")
need(sum(z.startswith("C1.") for z in original)==10,"one-block count")
need(sum(z.startswith("C2.") for z in original)==7,"two-block count")
cases={g["id"].split("CASE.",1)[1] for g in gates if g["kind"]=="original_parent"}
need(cases==set(original),"original parent not covered or phantom caller")
for case in original:
    prefix=("G30" if case.startswith("C1.") else "G40")+".CASE."+case
    need(all(prefix+"."+s in by_id for s in ("D","C","V","J")),
         "missing four original gates "+case)
rows=j["original_open_six_body_exterior"]
need(len(rows)==20 and len(set(rows))==20,"20 exterior rows")
need({"G30.6.EXT."+s for s in rows}<=set(by_id),"missing exterior gate")
b=j["canonical_baseline"]
need((b["coarse_closed"],b["coarse_total"],b["fine_checked"],b["fine_total"],
      b["six_body_exterior_closed"],b["six_body_exterior_total"])==
     (41,58,2373,2513,18,38),"baseline modified by planning")
need(overlay["baseline_fine_total"]==2513 and
     overlay["baseline_fine_checked"]==2373,"bad fine baseline overlay")
need(overlay["baseline_source_blob_sha"]=="207ad5250b25fd479d5208211cc66bbaaacf9069",
     "archived canonical fine source blob mismatch")
changes=overlay["accepted_new_original_fine_closures"]
ids=[r["original_id"] for r in changes]
need(len(ids)==len(set(ids)),"duplicate original fine closure")
need(all(r.get("proof_source") and r.get("independent_review") for r in changes),
     "fine changes require independent proof sources")
need(len(changes)<=2513-2373,"too many fine updates")
need((PREFIX/"history/roadmap_replacement_2026_11_01/LEGACY_DEEP_GATED_ROADMAP.md").exists(),
     "legacy original 2,513-ID source not preserved")
need(j["target_q"]=="1105/256","sharp target changed")
need((PREFIX/"DEEP_GATED_ROADMAP.md").exists(),"missing readable roadmap")
print(json.dumps({"verified_roadmap_structure":True,"gate_records_not_progress_units":len(gates),
 "active_gate":j["active_gate"],"original_open_coarse":len(original),
 "nested_open_exterior":len(rows),"historical_fine_checked":2373,
 "new_accepted_fine_updates":len(changes),"mathematical_proof_verified":False},indent=2))
