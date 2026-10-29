#!/usr/bin/env python3
"""Render the n=10 proof ledger. Counts are case bookkeeping, not proof effort."""
from collections import Counter
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
START = "<!-- CASE_PROGRESS_START -->"
END = "<!-- CASE_PROGRESS_END -->"


def fraction_bar(done, total):
    ticks = done * 24 * 8 // total
    full, part = divmod(ticks, 8)
    partial = " ▏▎▍▌▋▊▉"[part] if part else ""
    return "█" * full + partial + "░" * (24-full-bool(part))


def replace_region(path, content):
    text = path.read_text()
    if text.count(START) != 1 or text.count(END) != 1:
        raise ValueError(f"Expected one progress region in {path.name}")
    before, rest = text.split(START)
    _, after = rest.split(END)
    path.write_text(before + START + "\n" + content + "\n" + END + after)


def main():
    data = json.loads((ROOT / "case_progress.json").read_text())
    cycles = json.loads((ROOT / "cycle_cases.json").read_text())
    cycle_status = json.loads((ROOT / "cycle_progress.json").read_text())["case_status"]
    cycle_ids = {c["id"] for f in cycles["families"] for c in f["transmitter_cases"]}
    if not cycle_status.keys() <= cycle_ids:
        raise ValueError("Unknown cycle progress ID")
    for key, value in cycle_status.items():
        if value["status"] not in ("hand", "computer") or not (ROOT / value["evidence"]).is_file():
            raise ValueError(f"Invalid cycle closure: {key}")
    cycle_done = len(cycle_status)
    cycle_total = len(cycle_ids)
    cycle_bar = fraction_bar(cycle_done, cycle_total)
    branch = json.loads((ROOT / "branching_loaded_cap_angle_summary.json").read_text())
    branch_total = branch["initial_cases"]
    branch_done = branch["distinct_exclusions"]
    if (not 0 <= branch_done <= branch_total
            or branch_total - branch_done != branch["remaining_cases"]
            or sum(r["total"] for r in branch["by_loaded_count"]) != branch_total
            or sum(r["union"] for r in branch["by_loaded_count"]) != branch_done
            or not (ROOT / branch["proof"]).is_file()):
        raise ValueError("Invalid branching subclass totals or evidence")
    branch_bar = fraction_bar(branch_done, branch_total)
    cases = data["cases"]
    if len({c["id"] for c in cases}) != len(cases):
        raise ValueError("Duplicate case ID")
    for case in cases:
        if case["status"] not in data["statuses"]:
            raise ValueError(f"Unknown status: {case['id']}")
        if not (ROOT / case["evidence"]).is_file():
            raise ValueError(f"Missing evidence: {case['id']}")
    counts = Counter(c["status"] for c in cases)
    symbols = {"hand": "█", "computer": "▓", "open": "░"}
    labels = {"hand": "HAND CLOSED", "computer": "COMPUTER CLOSED", "open": "OPEN"}
    bar = "".join(symbols[s] * counts[s] for s in ("hand", "computer", "open"))
    gates = data["gates"]
    done = sum(g["closed"] for g in gates)
    summary = (
        f"**Main gates:** `{'█' * done}{'░' * (len(gates)-done)}` **{done}/{len(gates)} closed**.\n\n"
        f"**G3 lower-bound case ledger:** `{bar}`\n"
        f"**{counts['hand']} hand closed · {counts['computer']} computer closed · "
        f"{counts['open']} open / {len(cases)} terminal families.**\n\n"
        f"**C20 larger-cycle subcases:** `{cycle_bar}` **{cycle_done}/{cycle_total} closed; "
        f"{cycle_total-cycle_done} open.**\n\n"
        f"**C05 branching subclass, all branch vertices loaded:** `{branch_bar}` "
        f"**{branch_done:,}/{branch_total:,} excluded; {branch_total-branch_done:,} remain.** "
        f"[Catalog and certificates]({branch['proof']}). "
        "Unloaded branching vertices remain outside this subledger.\n\n"
        "`█` reviewed hand deduction; `▓` reviewed computer-assisted result; `░` open. "
        "These are counts of the fixed ledger entries, **not a percentage of the proof or remaining effort**. "
        + ("For the requested hand proof, each computer-assisted family also needs a hand replacement."
           if counts['computer'] else "Every currently closed family has a reviewed hand deduction; imported dependencies remain as stated in each proof.")
    )
    gate_table = ["| Gate | Obligation | Status |", "| --- | --- | --- |"]
    gate_table += [f"| {g['id']} | {g['name']} | {'CLOSED' if g['closed'] else 'OPEN'} |" for g in gates]
    case_table = ["| ID | Status | Exact family and current evidence |", "| --- | --- | --- |"]
    case_table += [f"| {c['id']} | {labels[c['status']]} | **{c['title']}.** {c['scope']} [Proof / reduction]({c['evidence']}). |" for c in cases]
    content = summary + "\n\n" + "\n".join(gate_table) + "\n\n" + "\n".join(case_table)
    replace_region(ROOT / "CASE_ROADMAP.md", content)
    replace_region(ROOT / "README.md", summary + "\n\n[Open the full case tree and remaining obligations](CASE_ROADMAP.md). "
                   "[Browse all 279 larger-cycle cases](CYCLE_CASES.md).")
    rows = ["# Finite inventory of the larger mixed simple cycles", "",
            "This is the complete current **graph/transmitter overclassification** for C20. "
            "It covers whole positive components of lengths 6–10, modulo cyclic rotation and reflection. "
            "The inventory itself does not assert geometric feasibility or classify contact ownership. "
            "Separately proved exclusions are tracked below.", "",
            f"**Exclusion progress:** `{cycle_bar}` **{cycle_done}/{cycle_total} transmitter cases closed; {cycle_total-cycle_done} open.**", "",
            "| Length | Binary load families | S/D cases | Excluded |", "| --- | ---: | ---: | ---: |"]
    for r in cycles["counts_by_length"]:
        closed = sum(c["id"] in cycle_status for f in cycles["families"]
                     if f["cycle_length"] == r["cycle_length"] for c in f["transmitter_cases"])
        rows.append(f"| {r['cycle_length']} | {r['binary_families']} | {r['transmitter_cases']} | {closed} |")
    rows += ["", "`L` means loaded; `S` and `D` are unloaded side and diagonal transmitters. "
             "The labels retain boundary contact. Two consecutive unloaded bodies must both be S; "
             "three consecutive unloaded bodies are impossible. The loaded-star exclusion is applied "
             "only when one body touches every other loaded body.", "",
             "The independent enumerations and Burnside count in [check_cycle_cases.py](check_cycle_cases.py) agree on "
             "[cycle_cases.json](cycle_cases.json). They enumerate all ternary words and, separately, "
             "all cyclic loaded-vertex gap compositions. This is a coverage check, not a packing proof.", "",
             "| Stable ID | Canonical cyclic word | Status |", "| --- | --- | --- |"]
    for family in cycles['families']:
        for c in family["transmitter_cases"]:
            record = cycle_status.get(c["id"])
            status = f"[{labels[record['status']]}]({record['evidence']})" if record else "OPEN"
            rows.append(f"| {c['id']} | `{c['word']}` | {status} |")
    rows += ["", "Update the ledger only after a proof covers every physical realization of the entry. "
             "A conditional core lemma or an infeasible numerical sample does not close an entry.", ""]
    (ROOT / "CYCLE_CASES.md").write_text("\n".join(rows))
    print(f"Rendered {done}/{len(gates)} gates; {dict(counts)} across {len(cases)} case families; {cycle_done}/{cycle_total} cycle cases closed.")
    print(f"Branching b=0: {branch_done}/{branch_total} excluded; {branch_total-branch_done} remain; b>0 unclassified.")


if __name__ == "__main__":
    main()
