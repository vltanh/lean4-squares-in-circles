#!/usr/bin/env python3
"""Validate and render the frozen strict-lower-bound proof-family ledger."""
from collections import Counter
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
MANIFEST_SHA256 = "a2da052af028a24e3ef785e65e7f599e459744c8db42bb32028efced1a1de3d6"


def render_master(data, cycles, cycle_status, fraction_bar):
    manifest = json.loads((ROOT / "master_cases.json").read_text())
    digest = hashlib.sha256(json.dumps(manifest, sort_keys=True,
                                      separators=(",", ":")).encode()).hexdigest()
    if digest != MANIFEST_SHA256:
        raise ValueError("Frozen master manifest changed; do not silently change its obligations")
    entries = manifest["entries"]
    ids = {e["id"] for e in entries}
    if len(entries) != 336 or len(ids) != 336:
        raise ValueError("Master ledger must retain its 336 unique IDs")
    top = {c["id"]: c for c in data["cases"]}
    words = {c["id"]: c["word"] for f in cycles["families"]
             for c in f["transmitter_cases"]}
    branches = {(k, b) for k in range(2, 8) for b in range(11-k)} - {(2, 0)}
    assert {e["id"] for e in entries if e["kind"] == "terminal"} == set(top) - {"C05", "C20"}
    assert {e["id"]: e["word"] for e in entries if e["kind"] == "cycle"} == words
    assert {(e["loaded_count"], e["unloaded_retained_count"])
            for e in entries if e["kind"] == "branching"} == branches
    progress = json.loads((ROOT / "master_progress.json").read_text())["case_status"]
    branch_ids = {e["id"] for e in entries if e["kind"] == "branching"}
    if not progress.keys() <= branch_ids:
        raise ValueError("Only branching closures belong in master_progress.json")
    records = []
    for entry in entries:
        if entry["kind"] == "terminal":
            status = top[entry["id"]]
        elif entry["kind"] == "cycle":
            status = cycle_status.get(entry["id"], {"status": "open"})
        else:
            status = progress.get(entry["id"], {"status": "open"})
        if status["status"] not in ("hand", "computer", "open"):
            raise ValueError(f"Invalid master status: {entry['id']}")
        if status["status"] != "open" and not (ROOT / status["evidence"]).is_file():
            raise ValueError(f"Missing master evidence: {entry['id']}")
        records.append((entry, status))
    counts = Counter(s["status"] for _, s in records)
    closed = counts["hand"] + counts["computer"]
    summary = (
        f"**Fixed strict-lower-bound master ledger:** `{fraction_bar(closed, 336)}` "
        f"**{closed}/336 closed; {counts['open']} open.** "
        f"({counts['hand']} hand; {counts['computer']} computer-only.) "
        "[All stable IDs and the exact remaining obligations](MASTER_CASES.md).\n\n"
        "The denominator is frozen: 19 other terminal families + 38 branching families + "
        "279 cycle signatures. A branching family includes every permitted graph and continuous "
        "realization for its fixed `(k,b)`. These are proof-family counts, **not a percentage of "
        "effort or of the full n=10 deliverable**. Equality and Lean verification have separate gates."
    )
    rows = ["# Fixed master ledger for the strict n=10 lower bound", "", summary, "",
            "## Exhaustive coverage and fixed meaning", "",
            manifest["scope"], "", manifest["selection_convention"], "",
            manifest["partition_rule"], "",
            "The original ordered tree makes its terminal families disjoint. In C05, k and b "
            "are uniquely determined by the whole positive graph: k counts positive circle-loaded "
            "bodies, and b counts unloaded bodies of degree at least three. The earlier reductions "
            "give 2<=k<=7 and 0<=b<=10-k. With k=2,b=0 there are only two retained vertices; "
            "the seven-symbol alphabet permits at most two parallel paths, hence only a tree "
            "or a whole simple cycle, not C05. The remaining 38 pairs exhaust C05. The eight "
            "k=2 families are all closed by one universal theorem. The remaining 30 families "
            "include b=0, b=1, and every larger allowed b; no further strata will be added.", "",
            "For each branching pair, retain all labels and circular loaded orders. Each pair "
            "of retained vertices receives one of absent/direct/S/double-S/D/SS/double-SS, "
            "with body costs 0/0/1/2/1/2/4. The sum is at most 10-k-b. Thus even the unpruned "
            "labeled code space is bounded by 7^45 edge assignments per labeling/order. "
            "Graph connectivity, degrees, cuts, geometry and force balance further restrict it. "
            "We need not materialize this enormous finite space to prove a theorem covering it. "
            "A leaf still permits infinitely many coordinates and forces; it is a universally "
            "quantified proof obligation, not a single combinatorial code.", "",
            "C20's 279 signatures use the independently checked canonical cycle inventory. "
            "Loaded-star and transmitter reductions are part of the coverage proof; the inventory "
            "does not assert feasibility. Choosing a different component of one packing may give "
            "a different entry: the partition is of selected-component instances, not of packings "
            "with their component forgotten.", "", manifest["closure_rule"], "",
            "The b=0 and b=1 raw catalogs remain optional drilldowns. Their exclusions do not "
            "increase this master bar unless an entire fixed family is proved. New shared lemmas "
            "may close many existing IDs together. No research subcase creates a new master ID.", "",
            "| Fixed group | Hand closed | Computer-only | Open | Total |",
            "| --- | ---: | ---: | ---: | ---: |"]
    for kind, label in (("terminal", "Other terminal families"),
                        ("branching", "All branching families"), ("cycle", "All cycle signatures")):
        c = Counter(s["status"] for e, s in records if e["kind"] == kind)
        rows.append(f"| {label} | {c['hand']} | {c['computer']} | {c['open']} | {sum(c.values())} |")
    work_groups = Counter()
    for entry, status in records:
        if status["status"] != "open":
            continue
        if entry["kind"] == "branching":
            group = "Branching components"
        elif entry["kind"] == "cycle":
            word = entry["word"]
            group = ("Cycles containing SS" if "SS" in word + word else
                     "Cycles containing D, without SS" if "D" in word else
                     "Cycles with only single S transmissions")
        else:
            group = "Other terminal obligations"
        work_groups[group] += 1
    rows += ["", "## Shared arguments covering the remaining list", "",
             "The following work groups partition the open IDs by a fixed structural feature. "
             "They are research targets, not additional progress denominators or claimed theorems. "
             "Every open entry is included; one argument may still cover several groups.", "",
             "| Shared target | Open IDs covered | Missing common argument |", "| --- | ---: | --- |"]
    routes = {
        "Branching components": "Use the three-interior-body and two-terminal patch reductions to control regions with at least three terminals or bound their completion capacity.",
        "Cycles containing SS": "Prove a uniform barrier or capacity bound across all endpoint ownership and transmitter slides.",
        "Cycles containing D, without SS": "Extend D-endpoint geometry or completion bounds across the full signatures, retaining every loaded support type.",
        "Cycles with only single S transmissions": "Use loaded-run force/torque restrictions and completion capacity uniformly over S slides.",
        "Other terminal obligations": "Discharge the exact terminal obligation recorded below.",
    }
    for group, route in routes.items():
        if work_groups[group]:
            rows.append(f"| {group} | {work_groups[group]} | {route} |")
    rows += ["", "A general tool for these routes is [finite center-cover capacity](FINITE_CENTER_COVER_CAPACITY.md). "
             "Its hypotheses must be established for every realization of the entry before it can close that entry.",
             "", "## Remaining obligations", "",
             "Each row below requires exclusion of **every** realization stated in the full ledger. "
             "A completion-capacity theorem is enough; the component itself need not be impossible.", "",
             "| Stable ID | Full family still to exclude |", "| --- | --- |"]
    for entry, status in records:
        if status["status"] == "open":
            rows.append(f"| {entry['id']} | {entry['scope']} |")
    rows += ["", "## All 336 fixed entries", "",
             "| Stable ID | Status / evidence | Exact proof obligation |", "| --- | --- | --- |"]
    for entry, status in records:
        state = status["status"]
        label = "OPEN" if state == "open" else f"[{state.upper()} CLOSED]({status['evidence']})"
        rows.append(f"| {entry['id']} | {label} | {entry['scope']} |")
    rows += ["", "The immutable obligations are in [master_cases.json](master_cases.json). "
             "Branching closures are in [master_progress.json](master_progress.json); the other "
             "statuses are derived from the existing terminal and cycle status files. "
             "[render_master_cases.py](render_master_cases.py) verifies the frozen manifest hash, "
             "ID coverage, evidence paths and totals. Run `python update_case_roadmap.py` to "
             "regenerate all visible summaries. This bookkeeping check is not a proof checker.", ""]
    (ROOT / "MASTER_CASES.md").write_text("\n".join(rows))
    print(f"Fixed master: {counts['hand']} hand + {counts['computer']} computer + {counts['open']} open = 336.")
    return summary

