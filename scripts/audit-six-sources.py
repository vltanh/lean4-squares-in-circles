#!/usr/bin/env python3
"""Check the Six draft's source hygiene and, optionally, actual Lean axiom output.

Source checks alone are NOT Lean compilation or proof acceptance. This utility
never executes a certificate or manufactures compiler output.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
from typing import Iterable

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = frozenset({'propext', 'Classical.choice', 'Quot.sound'})
FORBIDDEN = re.compile(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|sorryAx)\b')


def code_only(text: str) -> str:
    """Remove nested Lean comments and string literals, preserving line numbers."""
    out: list[str] = []
    i, depth = 0, 0
    line_comment = string = False
    while i < len(text):
        ch, pair = text[i], text[i:i+2]
        if line_comment:
            out.append('\n' if ch == '\n' else ' ')
            line_comment = ch != '\n'
            i += 1
        elif depth:
            if pair == '/-':
                depth += 1
                out.append('  ')
                i += 2
            elif pair == '-/':
                depth -= 1
                out.append('  ')
                i += 2
            else:
                out.append('\n' if ch == '\n' else ' ')
                i += 1
        elif string:
            if ch == '\\' and i + 1 < len(text):
                out.extend((' ', '\n' if text[i+1] == '\n' else ' '))
                i += 2
            else:
                if ch == '"':
                    string = False
                out.append('\n' if ch == '\n' else ' ')
                i += 1
        elif pair == '--':
            line_comment = True
            out.append('  ')
            i += 2
        elif pair == '/-':
            depth = 1
            out.append('  ')
            i += 2
        elif ch == '"':
            string = True
            out.append(' ')
            i += 1
        else:
            out.append(ch)
            i += 1
    if depth or string:
        raise ValueError('unterminated Lean block comment or string')
    return ''.join(out)


def expected_axiom_declarations(root: Path = ROOT) -> list[str]:
    return re.findall(r'^#print\s+axioms\s+(\S+)\s*$',
                      (root / 'SixAxiomAudit.lean').read_text(), re.M)


def validate_axioms(text: str, expected: Iterable[str]) -> dict[str, list[str]]:
    """Fail on missing records, duplicate records, or any non-whitelisted axiom."""
    pattern = re.compile(
        r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
        re.S)
    found: dict[str, list[str]] = {}
    for match in pattern.finditer(text):
        name, raw = match.group(1), match.group(2)
        if name in found:
            raise ValueError(f'duplicate axiom record: {name}')
        axioms = [] if raw is None else [x.strip() for x in raw.split(',') if x.strip()]
        unknown = set(axioms) - ALLOWED_AXIOMS
        if unknown:
            raise ValueError(f'{name} has unapproved axioms: {sorted(unknown)}')
        found[name] = axioms
    expected_set = set(expected)
    if not expected_set or set(found) != expected_set:
        raise ValueError(f'axiom inventory mismatch: missing={sorted(expected_set-set(found))}, '
                         f'extra={sorted(set(found)-expected_set)}')
    return found


def source_report(root: Path = ROOT) -> dict:
    paths = sorted((root / 'SquaresInCircles/Six').rglob('*.lean'))
    paths += [root / 'SquaresInCircles/Six.lean', root / 'SixAxiomAudit.lean']
    if not paths or any(not p.is_file() for p in paths):
        raise ValueError('Six sources or audit entry point are missing')
    rows = []
    for path in paths:
        data = path.read_bytes()
        source = code_only(data.decode('utf-8'))
        bad = FORBIDDEN.search(source)
        if bad:
            line = source.count('\n', 0, bad.start()) + 1
            raise ValueError(f'{path}:{line}: forbidden construct {bad.group()}')
        if 'debug.skipKernelTC' in source:
            raise ValueError(f'{path}: kernel-check bypass option')
        if path.name == 'Goals.lean' and re.search(r'\b(?:theorem|lemma)\b', source):
            raise ValueError('Goals.lean must contain unproved Prop definitions, not theorem claims')
        rows.append({'path': str(path.relative_to(root)),
                     'sha256': hashlib.sha256(data).hexdigest(),
                     'lines': len(data.splitlines()),
                     'proof_declarations': len(re.findall(r'\b(?:lemma|theorem)\s+', source))})
    return {'scope': 'source hygiene only; not Lean compilation or theorem acceptance',
            'source_hygiene': 'PASS', 'files': rows,
            'lean_compilation_performed_by_this_check': False,
            'unrestricted_n6_theorem_proved': False}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json', type=Path)
    parser.add_argument('--axioms', type=Path, help='actual output of lake env lean SixAxiomAudit.lean')
    args = parser.parse_args()
    report = source_report()
    if args.axioms:
        report['kernel_axiom_records'] = validate_axioms(args.axioms.read_text(), expected_axiom_declarations())
        report['axiom_log_sha256'] = hashlib.sha256(args.axioms.read_bytes()).hexdigest()
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
