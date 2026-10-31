#!/usr/bin/env python3
"""Finite exact six-body EXTERIOR-HEXAGON graph/load table.

This checks only discrete necessity. It does NOT prove any geometric
exclusion, decide circle-contact masks, or certify the unrestricted n=9
packing theorem. Uses Python standard library, no floating arithmetic.

Run: python scripts/n9_six_body_table.py [--markdown | --json]
"""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from itertools import combinations
from pathlib import Path

N = 6
RIM = frozenset(tuple(sorted((i, (i + 1) % N))) for i in range(N))

# Exactly the nine original noncrossing hexagon chord graph classes.
GRAPH_CLASSES = (
    ("none", ()),
    ("02", ("02",)),
    ("03", ("03",)),
    ("02+03", ("02", "03")),
    ("02+04", ("02", "04")),
    ("02+35", ("02", "35")),
    ("02+03+04", ("02", "03", "04")),
    ("02+03+35", ("02", "03", "35")),
    ("02+04+24", ("02", "04", "24")),
)

# Independently transcribed representatives from SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md.
# There are 40 here before two separate *complete geometric* bare-cycle exits.
LITERAL_COVER = {
    "none": {3: ("013", "024"), 4: ("0123", "0124", "0134"), 5: ("01234",)},
    "02": {3: ("014", "134", "135"), 4: ("0134", "0135", "0145", "1345"), 5: ("01345",)},
    "03": {3: ("014", "024", "124"), 4: ("0124", "0125", "0134", "1245"), 5: ("01245",)},
    "02+03": {3: ("124", "125"), 4: ("1234", "1235", "1245"), 5: ("12345",)},
    "02+04": {3: ("125", "135"), 4: ("0135", "1235", "1245"), 5: ("12345",)},
    "02+35": {3: (), 4: ("0134", "0145"), 5: ()},
    "02+03+04": {3: (), 4: (), 5: ("12345",)},
    "02+03+35": {3: (), 4: ("1245",), 5: ()},
    "02+04+24": {3: ("135",), 4: ("0135",), 5: ()},
}

# These two are excluded by complete bare-cycle geometry, not by the
# elementary graph filters implemented here. They remain in LITERAL_COVER.
BARE_GEOMETRIC_EXITS = frozenset({"013", "0123"})

# Previously documented *whole original load-orbit* exits.  "Proven"
# here means a complete published hand manuscript is named; it does not
# claim that its earlier independent review is itself Lean verification.
# This is intentionally a conservative allowlist, not an exhaustive audit.
WHOLE_HAND_EXITS = {
    ("none", "01234"): "SIX_CYCLE_FIVE_LOAD_CENTRAL_CAPACITY_ONE.md (later complete join)",
    ("02", "014"): "ADOPTION_COMPLETE_D02_L014_AND_FULL_STAR_CONE_ROOT_2026_10_29.md",
    ("02", "134"): "ADOPTION_TWO_RECOVERED_D02_ROWS_AND_UNIFORM_SUPPORT_GEOMETRY_2026_10_29.md",
    ("02", "0134"): "ADOPTION_TWO_RECOVERED_D02_ROWS_AND_UNIFORM_SUPPORT_GEOMETRY_2026_10_29.md",
    ("02", "0135"): "D02_L0134_AND_L0135_COMPLETE_ORIGINAL_DOMAIN_CLOSURE.md",
    ("02", "0145"): "ADOPTION_TWO_RECOVERED_D02_ROWS_AND_UNIFORM_SUPPORT_GEOMETRY_2026_10_29.md",
    ("02", "01345"): "D02_FIVE_LOAD_COMPLETE_ORIGINAL_DOMAIN_EXCLUSION.md (prior published exit)",
    ("03", "01245"): "CHORDED_HEXAGON_THREE_FIVE_LOAD_FAMILIES_CLOSED.md",
    ("02+03", "12345"): "CHORDED_HEXAGON_THREE_FIVE_LOAD_FAMILIES_CLOSED.md",
    ("02+04", "12345"): "CHORDED_HEXAGON_THREE_FIVE_LOAD_FAMILIES_CLOSED.md",
    ("02+03+04", "12345"): "CHORDED_HEXAGON_FAN_COMPLETE_EXCLUSION.md",
}

# Literal reconciliation with the original roadmap at this immutable input.
# This is evidence bookkeeping, NOT a proof of the checked statements.
STATUS_INPUT_SHA = "71d385e75adc1f5183d35a92dbe18c208dc32f2a"
STATUS_ROADMAP_BLOB = "77cf80fd377d7f6a400a15a00fe22e9b66d4b355"
GRAPH_GATE_NAMES = {
    "02": "D02", "03": "D03", "02+03": "D0203", "02+04": "D0204",
    "02+35": "D0235", "02+03+04": "FAN", "02+03+35": "CHORD_PATH",
    "02+04+24": "CENTRAL_TRIANGLE",
}
BARE_GATE_NAMES = {
    "024": "THREE_ALTERNATING", "0124": "FOUR_ZERO_DISTANCE2",
    "0134": "FOUR_ZERO_DISTANCE3", "01234": "FIVE",
}
ADDITIONAL_CHECKED = frozenset({
    ("none", "024"), ("none", "0124"), ("none", "0134"),
    ("03", "0134"), ("02+03", "125"), ("02+04", "125"),
    ("02+35", "0145"),
})
LEDGER_CHECKED = frozenset(WHOLE_HAND_EXITS) | ADDITIONAL_CHECKED
KNOWN_OPEN = frozenset({
    ("02", "135"), ("02", "1345"),
    ("03", "014"), ("03", "024"), ("03", "124"),
    ("03", "0124"), ("03", "0125"), ("03", "1245"),
    ("02+03", "124"), ("02+03", "1234"),
    ("02+03", "1235"), ("02+03", "1245"),
    ("02+04", "135"), ("02+04", "0135"),
    ("02+04", "1235"), ("02+04", "1245"),
    ("02+35", "0134"), ("02+03+35", "1245"),
    ("02+04+24", "135"), ("02+04+24", "0135"),
})


def original_gate(label: str, load: str) -> str:
    if label == "none":
        return "M6.B6.C6." + BARE_GATE_NAMES[load]
    return "M6.B6.HEXAGON." + GRAPH_GATE_NAMES[label] + ".L" + load


def check_roadmap(rows: list[dict[str, object]], path: Path) -> None:
    """Match literal original flags, without modifying or trusting their proofs."""
    original: dict[str, bool] = {}
    for flag, gate in re.findall(r"^- \[([ x])\] \*\*([^*]+)\*\*", path.read_text(), re.MULTILINE):
        if gate in original:
            raise AssertionError(f"Repeated original ID: {gate}")
        original[gate] = flag == "x"
    for row in rows:
        gate = str(row["original_gate"])
        assert gate in original, ("Missing original gate", gate)
        assert original[gate] == row["original_checked"], (
            "Original flag differs from the pinned snapshot; reconcile before updating", gate)


def edges(chords: tuple[str, ...]) -> frozenset[tuple[int, int]]:
    return RIM | frozenset(tuple(sorted((int(s[0]), int(s[1])))) for s in chords)


def nbrs(i: int, e: frozenset[tuple[int, int]], subset: set[int]) -> set[int]:
    return {b if a == i else a for a, b in e if (a == i or b == i) and a in subset and b in subset}


def is_connected(v: set[int], e: frozenset[tuple[int, int]]) -> bool:
    if not v:
        return True
    reached = {next(iter(v))}
    while True:
        following = set(reached)
        for i in reached:
            following |= nbrs(i, e, v)
        if following == reached:
            return reached == v
        reached = following


def is_forest(v: set[int], e: frozenset[tuple[int, int]]) -> bool:
    # On each connected component, edges = vertices - 1.
    visited: set[int] = set()
    for seed in v:
        if seed in visited:
            continue
        frontier = {seed}
        component = {seed}
        while frontier:
            following = set()
            for i in frontier:
                following |= nbrs(i, e, v)
            following -= component
            component |= following
            frontier = following
        visited |= component
        num_edges = sum(1 for a, b in e if a in component and b in component)
        if num_edges != len(component) - 1:
            return False
    return True


def forced_loaded(e: frozenset[tuple[int, int]]) -> set[int]:
    out: set[int] = set()
    for i in range(N):
        near = nbrs(i, e, set(range(N)))
        touching_neighbors = sum(tuple(sorted(ab)) in e for ab in combinations(near, 2))
        if (len(near) == 2 and touching_neighbors >= 1) or (len(near) == 3 and touching_neighbors >= 2):
            out.add(i)
    return out


def dihedral_stabilizer(e: frozenset[tuple[int, int]]) -> list[tuple[int, ...]]:
    out = []
    for sign in (1, -1):
        for off in range(N):
            perm = tuple((sign * i + off) % N for i in range(N))
            shifted = frozenset(tuple(sorted((perm[a], perm[b]))) for a, b in e)
            if shifted == e:
                out.append(perm)
    assert out
    return out


def representative(load: set[int], perms: list[tuple[int, ...]]) -> str:
    return min("".join(str(i) for i in sorted(p[v] for v in load)) for p in perms)


def necessary_masks(chords: tuple[str, ...]) -> set[str]:
    e = edges(chords)
    auto = dihedral_stabilizer(e)
    forced = forced_loaded(e)
    candidates: set[str] = set()
    for k in (3, 4, 5):
        for bits in combinations(range(N), k):
            loaded = set(bits)
            if not forced <= loaded:
                continue
            inside = frozenset((a, b) for a, b in e if a in loaded and b in loaded)
            if not is_forest(loaded, inside):
                continue
            if any(len(nbrs(i, inside, loaded)) > 2 for i in loaded):
                continue
            complement = frozenset(tuple(sorted(pair)) for pair in combinations(loaded, 2) if tuple(sorted(pair)) not in e)
            if not is_connected(loaded, complement):
                continue
            if chords == ("02", "35") and (not (loaded & {0, 2}) or not (loaded & {3, 5})):
                continue
            # The unique original unit-bypass exit for the short-chord
            # loads013 is applied here only in this literal graph.
            if chords == ("02",) and representative(loaded, auto) == representative({0, 1, 3}, auto):
                continue
            candidates.add(representative(loaded, auto))
    return candidates



def bounded_faces(chords: tuple[str, ...]) -> list[tuple[int, ...]]:
    """Exact combinatorial face split; chords never cross by construction."""
    faces = [tuple(range(N))]
    for label in chords:
        a, b = int(label[0]), int(label[1])
        for pos, polygon in enumerate(faces):
            if a not in polygon or b not in polygon:
                continue
            i, j = polygon.index(a), polygon.index(b)
            if i > j:
                i, j = j, i
            if j == i + 1 or (i == 0 and j == len(polygon) - 1):
                continue
            first = polygon[i:j + 1]
            second = polygon[j:] + polygon[:i + 1]
            faces[pos:pos + 1] = [first, second]
            break
        else:
            raise AssertionError(f"Chord {label} could not split an actual bounded face")
    assert len(faces) == 1 + len(chords)
    assert sum(len(f) - 2 for f in faces) == N - 2
    return faces


def geometric_screens(chords: tuple[str, ...], loaded: set[int]) -> dict[str, object]:
    """Only cite previously established *necessary* face/pocket capacity lemmas.

    A triangle (positive contact ring) has hole capacity zero. A
    quadrilateral with >=3 genuinely loaded/boundary square vertices
    also has zero by FOUR_CYCLE_THREE_BOUNDARY_HOLE_EMPTY.md. Other
    faces are not pronounced empty. A directly touching boundary pair
    has no exterior square when both endpoints are physically boundary.
    """
    faces = bounded_faces(chords)
    possible_faces = ["".join(map(str, f)) for f in faces if len(f) > 4 or (len(f) == 4 and len(set(f) & loaded) < 3)]
    possible_pockets = [f"{i}{(i + 1) % N}" for i in range(N) if not (i in loaded and (i + 1) % N in loaded)]
    return {"bounded_faces": ["".join(map(str, f)) for f in faces],
            "bounded_faces_not_known_empty": possible_faces,
            "candidate_outer_pockets": possible_pockets}


def build_table() -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for label, chord_data in GRAPH_CLASSES:
        e = edges(chord_data)
        perms = dihedral_stabilizer(e)
        listed = {representative(set(map(int, item)), perms) for group in LITERAL_COVER[label].values() for item in group}
        computed = necessary_masks(chord_data)
        assert computed == listed, (label, "missing", sorted(listed - computed), "extra", sorted(computed - listed))
        assert sum(len(group) for group in LITERAL_COVER[label].values()) == len(listed), label
        for load in sorted(listed, key=lambda x: (len(x), x)):
            if label == "none" and load in BARE_GEOMETRIC_EXITS:
                continue
            assert ((label, load) in LEDGER_CHECKED) != ((label, load) in KNOWN_OPEN)
            checked = (label, load) in LEDGER_CHECKED
            status = "LEDGER-CHECKED" if checked else "OPEN"
            gate = original_gate(label, load)
            source = WHOLE_HAND_EXITS.get((label, load), "DEEP_GATED_ROADMAP.md: " + gate)
            screens = geometric_screens(chord_data, set(map(int, load)))
            rows.append({"graph": label, "loads": load, "count": len(load), "status": status,
                         "source": source, "original_gate": gate, "original_checked": checked,
                         "bounded_faces": screens["bounded_faces"],
                         "bounded_faces_not_known_empty": screens["bounded_faces_not_known_empty"],
                         "candidate_outer_pockets": screens["candidate_outer_pockets"]})
    assert len(rows) == 38
    assert Counter(r["count"] for r in rows) == Counter({3: 12, 4: 20, 5: 6}), Counter(r["count"] for r in rows)
    assert len({(r["graph"], r["loads"]) for r in rows}) == 38
    assert len({r["original_gate"] for r in rows}) == 38
    assert sum(r["status"] == "LEDGER-CHECKED" for r in rows) == 18
    assert sum(r["status"] == "OPEN" for r in rows) == 20
    assert all(r["original_checked"] for r in rows if r["count"] == 5)
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    grp = parser.add_mutually_exclusive_group()
    grp.add_argument("--markdown", action="store_true")
    grp.add_argument("--json", action="store_true")
    parser.add_argument("--check-roadmap", type=Path,
                        help="Validate the 38 status flags against this original roadmap file")
    args = parser.parse_args()
    rows = build_table()
    if args.check_roadmap:
        check_roadmap(rows, args.check_roadmap)
    if args.json:
        print(json.dumps({"verified_rows": len(rows), "status_input_sha": STATUS_INPUT_SHA,
                          "status_roadmap_blob": STATUS_ROADMAP_BLOB,
                          "count_by_load": dict(Counter(r["count"] for r in rows)),
                          "count_by_status": dict(Counter(r["status"] for r in rows)),
                          "rows": rows}, indent=2))
    elif args.markdown:
        print("| Chords | Loaded vertices | Loads | Unresolved bounded faces | Candidate outer edges | Original gate | Original flag |")
        print("| --- | --- | ---: | --- | --- | --- | --- |")
        for r in rows:
            fs = ", ".join(r["bounded_faces_not_known_empty"]) or "none"
            pockets = ", ".join(r["candidate_outer_pockets"]) or "none"
            print(f"| `{r['graph']}` | `{r['loads']}` | {r['count']} | {fs} | {pockets} | `{r['original_gate']}` | {r['status']} |")
    else:
        print("PASS: 9 graph types, 40 necessary load orbits, 2 previously excluded bare-cycle orbits, 38 survivors")
        print("PASS: 12 three-load, 20 four-load, 6 five-load representatives")
        print("PASS: all 38 original IDs reconciled: 18 ledger-checked, 20 open")
        print("PASS: previous 25 UNRECONCILED rows = 7 already checked + 18 already open")
        print("PASS: all six five-load representatives have named hand exits")
        clear = [r for r in rows if not r["bounded_faces_not_known_empty"]]
        print(f"PASS: {len(clear)} representatives have no bounded face left after only triangle/three-loaded-quadrilateral screens")
        for label, chord_data in GRAPH_CLASSES:
            print(f"  {label}: faces {','.join(''.join(map(str,f)) for f in bounded_faces(chord_data))}")
        if args.check_roadmap:
            print("PASS: all 38 literal original flags match the supplied roadmap")
        print("CAUTION: status reconciliation changes no original flag and proves no new geometric case")
        print("CAUTION: no mathematical packing inequality is certified by this graph-only test")


if __name__ == "__main__":
    main()

