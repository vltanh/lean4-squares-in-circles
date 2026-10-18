#!/usr/bin/env python3
"""Report source imports and finite proof inputs without invoking Lean.

This is a source inventory, not an elaboration, axiom, or performance check.
It deliberately does not expand the retained JSON tables or evaluate a
certificate. Run from any directory; --root can select another checkout.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess


IMPORT = re.compile(r"^(?:public\s+)?import\s+(\S+)", re.MULTILINE)
AFFINE = re.compile(
    r'affine_rows%\s+"([^"]+)"\s+rows\s+(\d+)'
    r'(?:\s+excluding_zero_core_primary\s+(\d+))?'
)


def inventory(root: Path, entry: str) -> dict:
    pending = [entry]
    reached: dict[str, str] = {}
    external: set[str] = set()
    while pending:
        module = pending.pop()
        if module in reached or module in external:
            continue
        path = root / (module.replace(".", "/") + ".lean")
        if not path.is_file():
            external.add(module)
            continue
        source = path.read_text()
        reached[module] = source
        pending.extend(IMPORT.findall(source))

    affine = []
    for module, source in sorted(reached.items()):
        for data_path, input_rows, retained_rows in AFFINE.findall(source):
            rows = int(retained_rows or input_rows)
            affine.append({
                "module": module,
                "rows": rows,
                "input_rows": int(input_rows),
                "excluded_by_geometry": int(input_rows) - rows,
                "input": data_path,
            })

    owner = {
        kind.lower(): sum(
            bool(re.fullmatch(r"SquaresInCircles\.Eight\.Generated\.Owner\." + kind + r"\d+", module))
            for module in reached
        )
        for kind in ("Quarter", "Mixed", "Tilt")
    }
    searches = []
    for module, source in sorted(reached.items()):
        for line, text in enumerate(source.splitlines(), 1):
            if ("certify " in text or "certify\n" in text) and "theorem" not in text:
                if "depth (problem" in text or "CompactRootCover.certify stationaryTargets" in text:
                    searches.append({"module": module, "line": line, "expression": text.strip()})

    try:
        head = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        head = None
    return {
        "kind": "source-only inventory; no Lean, CI, or certificate execution",
        "head": head,
        "entry": entry,
        "repository_modules": len(reached),
        "eight_modules": sum(module.startswith("SquaresInCircles.Eight.") for module in reached),
        "affine_tables": affine,
        "affine_rows": sum(table["rows"] for table in affine),
        "affine_input_rows": sum(table["input_rows"] for table in affine),
        "affine_geometric_exclusions": sum(table["excluded_by_geometry"] for table in affine),
        "stationary_root_cover_imported": "SquaresInCircles.Eight.ExactFamily.Generated.StationaryLocalization" in reached,
        "owner_bundle_modules": owner,
        "recursive_search_declarations": searches,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[3])
    parser.add_argument("--entry", default="SquaresInCircles.Eight.Theorem")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = json.dumps(inventory(args.root.resolve(), args.entry), indent=2) + "\n"
    if args.output:
        args.output.write_text(result)
    else:
        print(result, end="")


if __name__ == "__main__":
    main()
