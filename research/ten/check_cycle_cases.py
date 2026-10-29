#!/usr/bin/env python3
"""Exact finite inventory of whole mixed simple-cycle positive components.

This checks combinatorial coverage, not geometric feasibility or exclusion.
The geometric implications used to prune the inventory are proved in
CYCLIC_STRESS_REDUCTIONS.md.  No floating-point arithmetic is used.

By default, independently enumerate all ternary words and verify cycle_cases.json.
Pass --write to regenerate it by the different construction of cyclic loaded
vertices separated by unloaded runs of lengths zero, one, or two.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from itertools import product
import json
from pathlib import Path

MANIFEST = Path(__file__).with_name("cycle_cases.json")
CODE = {"L": 0, "S": 1, "D": 2, "U": 1}


def canonical(word: str) -> str:
    """Canonical representative under all rotations and reflections."""
    n = len(word)
    orbit = [orientation[i:] + orientation[:i]
             for orientation in (word, word[::-1]) for i in range(n)]
    return min(orbit, key=lambda text: (tuple(0 if c == "L" else 1 for c in text),
                                        tuple(CODE[c] for c in text)))


def direct_admissible(word: str) -> bool:
    """Necessary conditions, tested directly on the labeled cycle graph."""
    n = len(word)
    loaded = [i for i, c in enumerate(word) if c == "L"]
    if not 6 <= n <= 10 or not 3 <= len(loaded) <= min(7, n - 1):
        return False
    # Exclude a loaded body touching every other loaded body. In a simple
    # cycle this can occur only for exactly three loads; it does NOT forbid
    # every LLL substring when the component has four or more loaded bodies.
    if any(all(j in ((i - 1) % n, (i + 1) % n)
               for j in loaded if j != i) for i in loaded):
        return False
    for i in range(n):
        a, b, c = (word[(i + j) % n] for j in range(3))
        if all(letter != "L" for letter in (a, b, c)):
            return False  # Three unloaded widths already sum to at least 3.
        if a != "L" and b != "L" and (a != "S" or b != "S"):
            return False  # Two consecutive unloaded bodies must both be S.
    return True


def direct_words() -> set[str]:
    """Independent verification route: enumerate all 3^n vertex labelings."""
    result: set[str] = set()
    for n in range(6, 11):
        for letters in product("LSD", repeat=n):
            word = "".join(letters)
            if direct_admissible(word):
                result.add(canonical(word))
    return result


def burnside_count(n: int, alphabet: str) -> int:
    """Orbit count without canonicalization, by fixed words of each symmetry."""
    fixed_sum = 0
    for letters in product(alphabet, repeat=n):
        word = "".join(letters)
        if not direct_admissible(word.replace("U", "S")):
            continue
        fixed_sum += sum(word == orientation[i:] + orientation[:i]
                         for orientation in (word, word[::-1])
                         for i in range(n))
    quotient, remainder = divmod(fixed_sum, 2 * n)
    if remainder:
        raise AssertionError("Burnside fixed-word sum is not divisible by group size")
    return quotient


def run_construction() -> set[str]:
    """Generation route: cyclic loaded vertices with bounded intervening runs."""
    result: set[str] = set()
    for n in range(6, 11):
        for k in range(3, min(7, n - 1) + 1):
            for gaps in product((0, 1, 2), repeat=k):
                if sum(gaps) != n - k:
                    continue
                if k == 3 and any(gaps[(i - 1) % k] == gaps[i] == 0
                                  for i in range(k)):
                    continue
                options = [(("",) if gap == 0 else ("S", "D")
                            if gap == 1 else ("SS",)) for gap in gaps]
                for runs in product(*options):
                    result.add(canonical("".join("L" + run for run in runs)))
    return result


def make_manifest(words: set[str]) -> dict:
    grouped: dict[tuple[int, int, str], list[str]] = defaultdict(list)
    for word in words:
        binary = canonical(word.replace("S", "U").replace("D", "U"))
        grouped[len(word), word.count("L"), binary].append(word)
    families = []
    per_pair: Counter = Counter()
    for (n, k, binary), assignments in sorted(grouped.items()):
        per_pair[n, k] += 1
        family_id = f"C20-M{n:02d}-L{k:02d}-B{per_pair[n, k]:02d}"
        assignments.sort(key=lambda word: tuple(CODE[c] for c in word))
        families.append({
            "id": family_id,
            "cycle_length": n,
            "loaded_count": k,
            "loaded_word": binary,
            "transmitter_cases": [
                {"id": f"{family_id}-T{i:02d}", "word": word,
                 "side_count": word.count("S"),
                 "diagonal_count": word.count("D")}
                for i, word in enumerate(assignments, start=1)
            ],
        })
    counts = []
    for n in range(6, 11):
        at_n = [family for family in families if family["cycle_length"] == n]
        counts.append({
            "cycle_length": n,
            "binary_families": len(at_n),
            "transmitter_cases": sum(len(family["transmitter_cases"])
                                     for family in at_n),
        })
    return {
        "schema_version": 1,
        "scope": "whole positive components whose body-pair graph is a mixed simple cycle",
        "radius_scope": "hypothetical strictly subcritical ten-square packing; 79/40 <= R < 3/sqrt(2)",
        "meaning": "finite overclassification; entries need not be geometrically realizable and none is marked excluded by this inventory",
        "labels": {"L": "positive circle load", "U": "unloaded (binary words only)",
                   "S": "unloaded degree-two side transmitter, width 1",
                   "D": "unloaded degree-two diagonal transmitter, width sqrt(2)"},
        "equivalence": "all cycle rotations and reversals; transmitter types preserved",
        "necessary_restrictions": [
            "cycle length 6 through 10; five-cycles are tracked separately",
            "3 <= loaded count <= min(7, cycle length - 1)",
            "no loaded vertex adjacent to every other loaded vertex",
            "no unloaded run longer than two",
            "an unloaded run of length two consists of two side transmitters",
        ],
        "dependencies": ["CYCLIC_STRESS_REDUCTIONS.md", "CENTER_RADIUS_REDUCTION.md"],
        "not_classified": [
            "branching positive components or cycles that are only blocks of such components",
            "loaded-body contact ownership, circle-vertex multiplicity, force magnitudes, and geometric parameters",
            "physical feasibility, completion capacity, or the unrestricted packing optimum",
        ],
        "totals": {"binary_families": len(families),
                   "transmitter_cases": len(words)},
        "counts_by_length": counts,
        "families": families,
    }


def verify(manifest: dict) -> None:
    expected_words = direct_words()
    generated_words = run_construction()
    if generated_words != expected_words:
        raise AssertionError("Independent direct-word and run constructions disagree")
    expected = make_manifest(expected_words)
    if manifest != expected:
        raise AssertionError("Manifest differs from the complete independently enumerated inventory")
    for row in expected["counts_by_length"]:
        n = row["cycle_length"]
        if burnside_count(n, "LU") != row["binary_families"]:
            raise AssertionError("Independent Burnside binary count disagrees")
        if burnside_count(n, "LSD") != row["transmitter_cases"]:
            raise AssertionError("Independent Burnside transmitter count disagrees")
    totals = expected["totals"]
    print(f"PASS: {totals['binary_families']} binary families and "
          f"{totals['transmitter_cases']} transmitter cases modulo cycle rotations/reflections")
    for row in expected["counts_by_length"]:
        print(f"m={row['cycle_length']}: {row['binary_families']} binary families, "
              f"{row['transmitter_cases']} transmitter cases")
    print("Coverage only: geometric feasibility and completion exclusions remain separate.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate the finite manifest")
    args = parser.parse_args()
    if args.write:
        manifest = make_manifest(run_construction())
        MANIFEST.write_text(json.dumps(manifest, indent=2) + "\n")
    verify(json.loads(MANIFEST.read_text()))


if __name__ == "__main__":
    main()
