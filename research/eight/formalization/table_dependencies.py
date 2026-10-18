#!/usr/bin/env python3
"""Report source imports and finite proof inputs without invoking Lean.

This is a source inventory, not an elaboration, axiom, or performance check.
It deliberately does not expand the retained JSON tables or evaluate a
certificate. Run from any directory; --root can select another checkout.
Use --revision to inspect a committed tree without checking it out, and
--details to include the individual source occurrences in the JSON report.
"""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import subprocess


IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(\S+)", re.MULTILINE)
AFFINE = re.compile(
    r'affine_rows%\s+"([^"]+)"\s+rows\s+(\d+)'
    r'(?:\s+(excluding_zero_core_primary|excluding_core_separators|excluding_core_pairs)\s+(\d+))?'
)
CERTIFY = re.compile(r"(?<![\w'])certify(?![\w'])")
DECLARATION = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:public|private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev|opaque|axiom)\s+([\w.']+)"
)


def lean_code(source: str) -> str:
    """Mask comments and strings, preserving offsets and line numbers."""
    result = list(source)
    pos = depth = 0
    quoted = False
    while pos < len(source):
        if depth:
            if source.startswith("/-", pos):
                depth += 1
                result[pos:pos + 2] = "  "
                pos += 2
            elif source.startswith("-/", pos):
                depth -= 1
                result[pos:pos + 2] = "  "
                pos += 2
            else:
                if source[pos] != "\n":
                    result[pos] = " "
                pos += 1
        elif quoted:
            if source[pos] == "\\" and pos + 1 < len(source):
                result[pos] = " "
                if source[pos + 1] != "\n":
                    result[pos + 1] = " "
                pos += 2
            else:
                if source[pos] == '"':
                    quoted = False
                if source[pos] != "\n":
                    result[pos] = " "
                pos += 1
        elif source.startswith("/-", pos):
            depth = 1
            result[pos:pos + 2] = "  "
            pos += 2
        elif source.startswith("--", pos):
            end = source.find("\n", pos)
            if end < 0:
                end = len(source)
            result[pos:end] = " " * (end - pos)
            pos = end
        elif source[pos] == '"':
            quoted = True
            result[pos] = " "
            pos += 1
        else:
            pos += 1
    return "".join(result)


def certify_occurrences(module: str, source: str) -> list[dict]:
    """Find literal source uses, without interpreting or evaluating Lean."""
    occurrences = []
    declaration = declaration_kind = None
    in_body = False
    for line, (raw, code) in enumerate(zip(source.splitlines(), lean_code(source).splitlines()), 1):
        named = DECLARATION.match(code)
        if named:
            declaration_kind, declaration = named.groups()
            in_body = False
        assignment = code.find(":=")
        for match in CERTIFY.finditer(code):
            if named and named.start(2) <= match.start() < named.end(2):
                kind = "definition"
            elif declaration and declaration.split(".")[-1] == "certify":
                kind = "recursive_body"
            elif declaration_kind in ("theorem", "lemma"):
                kind = "proof_reference" if in_body or (0 <= assignment < match.start()) else "certificate_statement"
            else:
                kind = "other_reference"
            occurrences.append({
                "module": module, "line": line, "kind": kind,
                "declaration": declaration, "expression": raw.strip(),
            })
        if assignment >= 0:
            in_body = True
    return occurrences


def inventory(root: Path, entry: str, revision: str | None = None,
              details: bool = False) -> dict:
    committed_files = None
    if revision is not None:
        revision = subprocess.check_output(
            ["git", "rev-parse", "--verify", revision + "^{commit}"], cwd=root, text=True
        ).strip()
        committed_files = set(subprocess.check_output(
            ["git", "ls-tree", "-r", "--name-only", revision], cwd=root, text=True
        ).splitlines())
    pending = [entry]
    reached: dict[str, str] = {}
    external: set[str] = set()
    while pending:
        module = pending.pop()
        if module in reached or module in external:
            continue
        relative_path = module.replace(".", "/") + ".lean"
        path = root / relative_path
        exists = relative_path in committed_files if committed_files is not None else path.is_file()
        if not exists:
            external.add(module)
            continue
        source = (subprocess.check_output(
            ["git", "show", revision + ":" + relative_path], cwd=root, text=True
        ) if revision is not None else path.read_text())
        reached[module] = source
        pending.extend(IMPORT.findall(lean_code(source)))

    affine = []
    for module, source in sorted(reached.items()):
        for data_path, input_rows, exclusion_rule, retained_rows in AFFINE.findall(source):
            rows = int(retained_rows or input_rows)
            affine.append({
                "module": module,
                "rows": rows,
                "input_rows": int(input_rows),
                "excluded_by_geometry": int(input_rows) - rows,
                "exclusion_rule": exclusion_rule or None,
                "input": data_path,
            })

    owner = {
        kind.lower(): sum(
            bool(re.fullmatch(r"SquaresInCircles\.Eight\.Generated\.Owner\." + kind + r"\d+", module))
            for module in reached
        )
        for kind in ("Quarter", "Mixed", "Tilt")
    }
    owner_sources = {
        module: source for module, source in reached.items()
        if re.fullmatch(r"SquaresInCircles\.Eight\.Generated\.Owner\.(?:Quarter|Mixed|Tilt)\d+", module)
    }
    owner_rows = Counter()
    for source in owner_sources.values():
        owner_rows.update(re.findall(r"^def (quarter|mixed|tilt)_\d+_\d+ : Row", lean_code(source), re.MULTILINE))
    searches = []
    search_counts = {}
    for module, source in sorted(reached.items()):
        occurrences = certify_occurrences(module, source)
        searches.extend(occurrences)
        if occurrences:
            search_counts[module] = {"total": len(occurrences), **dict(Counter(row["kind"] for row in occurrences))}

    try:
        head = revision or subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True
        ).strip()
        tree = subprocess.check_output(
            ["git", "rev-parse", head + "^{tree}"], cwd=root, text=True
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        head = tree = None
    word_counts = Counter()
    four_type_count = 0
    for row in searches:
        if row["kind"] != "certificate_statement":
            continue
        name = row["declaration"] or ""
        word = re.fullmatch(r"(common|short|second)_\d_\w+", name)
        if word and row["module"].endswith(".WordCertificates"):
            word_counts[word.group(1)] += 1
        if row["module"].endswith(".FourTypePairs") and re.fullmatch(
            r"(?:coreSide|coreCorner|low|middle|high)_(?:coreSide|coreCorner|low|middle|high)_certificates", name
        ):
            four_type_count += 1
    result = {
        "kind": "source-only inventory; no Lean, CI, or certificate execution",
        "head": head,
        "source_snapshot": "committed tree" if revision is not None else "working tree",
        "committed_tree": tree,
        "entry": entry,
        "repository_modules": len(reached),
        "eight_modules": sum(module.startswith("SquaresInCircles.Eight.") for module in reached),
        "affine_tables": affine,
        "affine_rows": sum(table["rows"] for table in affine),
        "affine_input_rows": sum(table["input_rows"] for table in affine),
        "affine_geometric_exclusions": sum(table["excluded_by_geometry"] for table in affine),
        "stationary_root_cover_imported": "SquaresInCircles.Eight.ExactFamily.Generated.StationaryLocalization" in reached,
        "owner_bundle_modules": owner,
        "owner_row_certificates": dict(owner_rows),
        "owner_generated_lines": sum(len(source.splitlines()) for source in owner_sources.values()),
        "owner_generated_bytes": sum(len(source.encode()) for source in owner_sources.values()),
        "word_individual_certificates": dict(word_counts),
        "word_individual_certificate_total": sum(word_counts.values()),
        "four_type_chart_certificate_declarations": four_type_count,
        "missing_repository_imports": sorted(module for module in external if module.startswith("SquaresInCircles")),
        "recursive_search_inventory_kind": (
            "literal certify tokens in source, excluding comments and strings; "
            "definitions, statements and proof/body references are distinguished; "
            "these are not executed searches, recursion-node counts, or runtime measurements"
        ),
        "recursive_search_source_occurrences": len(searches),
        "recursive_search_source_counts_by_kind": dict(Counter(row["kind"] for row in searches)),
        "recursive_search_source_counts_by_module": search_counts,
        "recursive_search_runtime_measurements": None,
    }
    if details:
        # Historical key, now a complete source occurrence list. The default
        # report keeps per-module counts instead of duplicating large sources.
        result["recursive_search_declarations"] = searches
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[3])
    parser.add_argument("--entry", default="SquaresInCircles.Eight.Theorem")
    parser.add_argument("--revision", help="Read this committed revision without checking it out")
    parser.add_argument("--details", action="store_true", help="Include individual certify source occurrences")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = json.dumps(inventory(args.root.resolve(), args.entry, args.revision, args.details), indent=2) + "\n"
    if args.output:
        args.output.write_text(result)
    else:
        print(result, end="")


if __name__ == "__main__":
    main()
