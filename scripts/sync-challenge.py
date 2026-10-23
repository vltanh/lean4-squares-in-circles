#!/usr/bin/env python3
"""Synchronize the pure Challenge definitions by copying source text only.

The bodies of Geometry.lean, StatementEight.lean, StatementEightGeometric.lean,
and Optimal.lean are copied in that order beneath one shared noncomputable
section and namespace. The Challenge header, Mathlib imports, and theorem
region are preserved verbatim.

With --write this materializes the mirror.  Without --write it reports only
textual drift, retaining the previous comparator script's synchronization
behavior.  This helper does not invoke Lean, lake, a compiler, CI, a proof
checker, or any other program.
"""

import argparse
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCES = (
    "SquaresInCircles/Geometry.lean",
    "SquaresInCircles/StatementEight.lean",
    "SquaresInCircles/StatementEightGeometric.lean",
    "SquaresInCircles/Optimal.lean",
)
SECTION = "noncomputable section\n"
NAMESPACE = "namespace SquaresInCircles\n"
NAMESPACE_END = "end SquaresInCircles"
THEOREMS = "/-! ### The theorems -/"


def definition_body(path: Path) -> str:
    """Remove only the source file's outer section and namespace framing."""
    source = path.read_text()
    section_start = source.index(SECTION) + len(SECTION)
    namespace_start = source.index(NAMESPACE, section_start)
    if source[section_start:namespace_start].strip():
        raise ValueError(
            f"{path.relative_to(ROOT)}: put section commands inside "
            "namespace SquaresInCircles so their order is retained in the mirror"
        )
    body_start = namespace_start + len(NAMESPACE)
    body_end = source.rindex(NAMESPACE_END)
    return source[body_start:body_end].strip()


def definition_region() -> str:
    bodies = [definition_body(ROOT / source) for source in SOURCES]
    return SECTION + NAMESPACE + "\n" + "\n\n".join(bodies) + "\n\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--write", action="store_true",
        help="write the copied pure definitions into Challenge.lean; never build",
    )
    args = parser.parse_args()
    challenge_path = ROOT / "Challenge.lean"
    challenge = challenge_path.read_text()
    first = challenge.index(SECTION)
    last = challenge.index(THEOREMS, first)
    definitions = definition_region()
    if args.write:
        challenge_path.write_text(challenge[:first] + definitions + challenge[last:])
        print(
            "Challenge.lean: copied the primitive, stationary, geometric, and "
            "registry definition bodies; no build or proof checking invoked"
        )
        return 0
    if challenge[first:last] != definitions:
        parser.exit(
            1,
            "error: Challenge.lean differs from the pure definition sources; "
            "run python3 scripts/sync-challenge.py --write\n",
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
