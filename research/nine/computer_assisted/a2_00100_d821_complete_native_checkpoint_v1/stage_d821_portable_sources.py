#!/usr/bin/env python3
"""Stage every D821 native input by SHA-256 before an independent portable replay.

This program freezes *bytes*, not a proof: it deliberately never returns a
portable-proof PASS status or changes a fixed closure ledger. Source discovery
is from the published native report and its graft plan; missing/altered inputs
are fatal. Use the stage to build a genuinely relocatable, source-isolated
replay, which remains a separate acceptance requirement.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import tempfile

ID = 'positive-821c9a2debeed0aa'
PATH = [['angle', 3, 1], ['angle_cut', [0, '0'], 1],
        ['alternate_four_escape', [1, 7], [3]]]
REPORT_SHA = 'c56785bc3953b85b2c3069bb8bf61ec655d3d174c652595cc6e25928ae0a53b4'
PLAN_SHA = '6fc6a6f3840b99f99ddec479c8a3ea1bae0e3c2d1dd6c7010318150a9a95a3a9'
AUDIT_SHA = '7f5c37538f6836f377c270fb346f5dbbfaa45174f1a69d3d3c49e55558326f1c'
HEX64 = re.compile(r'[0-9a-f]{64}\Z')
BLOCK = 1024 * 1024


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(BLOCK), b''):
            h.update(block)
    return h.hexdigest()


def require_sha(path: Path, expected: str) -> None:
    if not HEX64.fullmatch(expected) or digest(path) != expected:
        raise ValueError(f'wrong SHA-256: {path} expected={expected}')


def find_refs(obj):
    """Yield unambiguously hash-bound {path,sha256} source references."""
    if isinstance(obj, dict):
        if isinstance(obj.get('path'), str) and isinstance(obj.get('sha256'), str):
            yield obj['path'], obj['sha256']
        for value in obj.values():
            yield from find_refs(value)
    elif isinstance(obj, list):
        for item in obj:
            yield from find_refs(item)


def stage(root: Path, report_file: Path, plan_file: Path, audit_file: Path,
          ledger_file: Path, destination: Path, *, expected_report=REPORT_SHA,
          expected_plan=PLAN_SHA, expected_audit=AUDIT_SHA):
    root = root.resolve(strict=True)
    report_file = report_file.resolve(strict=True)
    plan_file = plan_file.resolve(strict=True)
    audit_file = audit_file.resolve(strict=True)
    ledger_file = ledger_file.resolve(strict=True)
    for p, hash_ in ((report_file, expected_report), (plan_file, expected_plan),
                     (audit_file, expected_audit)):
        require_sha(p, hash_)
    report = json.loads(report_file.read_text())
    plan = json.loads(plan_file.read_text())
    audit = json.loads(audit_file.read_text())
    register = json.loads(ledger_file.read_text())
    if (report.get('status') != 'PASS_COMPLETE_ORIGINAL_CELL'
        or report.get('original_id') != ID or report.get('original_path') != PATH
        or report.get('mask') != '001/00'
        or report.get('whole_original_proved') is not True
        or report.get('complete_closed_complement_domains') != 5
        or len(report.get('grafted_cover_nodes', [])) != 46):
        raise ValueError('not the accepted complete native D821 report')
    if (plan.get('schema') != 'D821_grafted_five_complement_complete_original_plan_v1'
        or plan.get('original_id') != ID
        or set(plan.get('component_trees', {})) != {'0', '1', '3', '4'}):
        raise ValueError('not the registered D821 graft plan')
    if (audit.get('report_sha256') != expected_report
        or audit.get('trees') != 46 or audit.get('nodes') != 650
        or len(audit.get('independent_affine_terminal_sums', [])) != 242):
        raise ValueError('native report and published table audit disagree')
    live = [c for c in register.get('cells', []) if c.get('id') == ID]
    if (len(live) != 1 or live[0].get('path') != PATH or live[0].get('status') != 'OPEN'
        or len(register['cells']) != 231):
        raise ValueError('the fixed original registration changed')

    # Both maps and structured refs matter; never infer an input solely from
    # its filename. Conflicting hashes for the same path are fatal.
    references = {}
    def add(path, sha, role):
        if not isinstance(path, str) or not isinstance(sha, str) or not HEX64.fullmatch(sha):
            raise ValueError(f'nonliteral source reference: {path!r}, {sha!r}')
        p = Path(path)
        if not p.is_absolute():
            raise ValueError(f'unanchored source reference: {path}')
        p = p.resolve(strict=True)
        try:
            rel = p.relative_to(root)
        except ValueError as e:
            raise ValueError(f'input outside frozen workspace root: {path}') from e
        if rel == Path('.'):
            raise ValueError('source reference is a directory')
        key = str(rel)
        previous = references.get(key)
        if previous is not None and previous['sha256'] != sha:
            raise ValueError(f'conflicting source digest: {key}')
        if previous is None:
            references[key] = {'source': p, 'sha256': sha, 'roles': set()}
        references[key]['roles'].add(role)

    for name in ('input_sha256', 'checker_sha256'):
        mapping = report.get(name)
        if not isinstance(mapping, dict) or not mapping:
            raise ValueError(f'missing populated native report hash map {name}')
        for p, h in mapping.items():
            add(p, h, name)
    for name, obj in (('graft_plan', plan), ('native_report', report)):
        for p, h in find_refs(obj):
            add(p, h, name)
    if len(references) < 46:
        raise ValueError('suspiciously incomplete D821 source inventory')

    destination = destination.absolute()
    if destination.exists():
        raise FileExistsError(f'destination exists; refusing overwrite: {destination}')
    destination.parent.mkdir(parents=True, exist_ok=True)
    temp = Path(tempfile.mkdtemp(prefix='.d821-stage-', dir=destination.parent))
    try:
        inventory = {}
        for rel, record in sorted(references.items()):
            src = record['source']
            if not src.is_file():
                raise ValueError(f'not a regular source file: {src}')
            dst = temp / 'sources' / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            h = hashlib.sha256()
            count = 0
            with src.open('rb') as inp, dst.open('xb') as out:
                for block in iter(lambda: inp.read(BLOCK), b''):
                    h.update(block)
                    out.write(block)
                    count += len(block)
                out.flush()
                os.fsync(out.fileno())
            if h.hexdigest() != record['sha256'] or digest(src) != record['sha256']:
                raise ValueError(f'source changed or mismatched: {src}')
            if digest(dst) != record['sha256']:
                raise ValueError(f'copy failed verification: {dst}')
            inventory[rel] = {'sha256': record['sha256'], 'bytes': count,
                              'roles': sorted(record['roles'])}
        for name, src in [('NATIVE_REPORT.json', report_file),
                          ('GRAFT_PLAN.json', plan_file),
                          ('PUBLISHED_AUDIT.json', audit_file),
                          ('FIXED_REGISTER_SNAPSHOT.json', ledger_file)]:
            shutil.copyfile(src, temp / name)
            if digest(temp / name) != digest(src):
                raise ValueError(f'attachment changed while copying: {name}')
        result = {'schema': 'D821_native_source_byte_staging_v1',
                  'status': 'PASS_HASH_PINNED_NATIVE_STAGING_ONLY',
                  'original_id': ID, 'original_path': PATH, 'mask': '001/00',
                  'native_report_sha256': expected_report,
                  'graft_plan_sha256': expected_plan,
                  'native_table_audit_sha256': expected_audit,
                  'fixed_register_sha256': digest(ledger_file),
                  'inputs': inventory, 'source_count': len(inventory),
                  'source_bytes': sum(v['bytes'] for v in inventory.values()),
                  'fresh_portable_replay_completed': False,
                  'independent_geometric_reconstruction_completed': False,
                  'new_original_cells': 0, 'new_masks': 0,
                  'lean_lake_ci_run': False}
        (temp / 'STAGING_MANIFEST.json').write_text(json.dumps(result, indent=2) + '\n')
        os.rename(temp, destination)
        return {'status': result['status'], 'inputs': len(inventory),
                'bytes': result['source_bytes'], 'original_cells_closed': 0,
                'portable_arithmetic_replay': 'REQUIRED'}
    except BaseException:
        shutil.rmtree(temp)
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('root', 'report', 'plan', 'audit', 'ledger', 'output'):
        parser.add_argument('--' + name, required=True, type=Path)
    args = parser.parse_args()
    result = stage(args.root, args.report, args.plan, args.audit,
                   args.ledger, args.output)
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
