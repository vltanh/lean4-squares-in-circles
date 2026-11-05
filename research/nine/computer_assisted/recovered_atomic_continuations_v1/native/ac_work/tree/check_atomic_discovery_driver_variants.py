#!/usr/bin/env python3
"""Exercise only the new I/O dispatch and handlers; never import numerical drivers."""
if not __debug__:
    raise RuntimeError('Assertions must be enabled.')
from pathlib import Path
from copy import deepcopy
from types import SimpleNamespace
from unittest import mock
import ast
import errno
import hashlib
import importlib.util
import json
import os
import re
import sys
import tempfile

HERE = Path(__file__).resolve().parent
OUT = HERE.parent/'recovery_064e4aa/atomic_driver_preparation'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    prepared_path = OUT/'PREPARATION.json'
    assert sha(prepared_path) == '8ee6b41a5cd52f3a6e21460f9090aeacc8435170693752d1d99aead402062b32'
    prepared = json.loads(prepared_path.read_text())
    source = HERE/'atomic_json_checkpoint.py'
    assert sha(source) == prepared['atomic_helper_sha256']
    spec = importlib.util.spec_from_file_location('atomic_driver_control_helper', source)
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    bspec = importlib.util.spec_from_file_location('atomic_driver_preparation_source',
                                                 HERE/'prepare_atomic_discovery_driver_variants.py')
    builder = importlib.util.module_from_spec(bspec)
    bspec.loader.exec_module(builder)
    checks = []
    for case in prepared['cases']:
        path = Path(case['new_driver'])
        assert sha(path) == case['new_driver_sha256']
        old = Path(case['recovered_baseline'])
        assert sha(old) == case['old_source_sha256']
        text = path.read_text()
        normalized = text.replace(builder.BLOCK, '', 1).replace(builder.NEW_DUMP, builder.OLD_DUMP, 1).replace(builder.PIN, '', 1)
        normalized = re.sub(r'^( +)except OSError:\n\1    raise\n', '', normalized, flags=re.M)
        assert normalized == old.read_text()
        checks.append(case['label']+': all non-I/O source bytes equal the exact recovered baseline')
        tree = ast.parse(text)
        dump = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'dump')
        namespace = {'ATOMIC':helper}
        exec(compile(ast.fix_missing_locations(ast.Module(body=[deepcopy(dump)], type_ignores=[])),
                     str(path)+':dump_only', 'exec'), namespace)
        with tempfile.TemporaryDirectory(prefix='atomic_driver_dispatch_controls_') as raw:
            root = Path(raw)
            original = root/'frozen_source.json'
            original.write_bytes(b'old complete checkpoint\n')
            original.chmod(0o640)
            destination = root/'next_node.json'
            os.link(original, destination)
            before = original.stat()
            value = {'rational':'1/3', 'proof': ['all', 'closed', 'faces']}
            namespace['dump'](destination, value)
            assert destination.read_bytes() == (json.dumps(value, indent=2)+'\n').encode()
            assert original.read_bytes() == b'old complete checkpoint\n'
            assert (original.stat().st_dev, original.stat().st_ino) == (before.st_dev, before.st_ino)
            assert destination.stat().st_ino != original.stat().st_ino
            assert destination.stat().st_mode & 0o777 == 0o640
            checks.append(case['label']+': actual dump dispatch atomically replaces one path and preserves its prior frozen hardlink')
            previous = destination.read_bytes()
            previous_inode = destination.stat().st_ino
            prior_paths = set(root.iterdir())
            with mock.patch.object(helper.os, 'replace', side_effect=OSError(errno.ENOSPC, 'injected driver replace failure')):
                try:
                    namespace['dump'](destination, {'next':'checkpoint'})
                except OSError as error:
                    assert error.errno == errno.ENOSPC
                else:
                    raise AssertionError('Driver dump swallowed OSError.')
            assert destination.read_bytes() == previous and destination.stat().st_ino == previous_inode
            assert len(set(root.iterdir())-prior_paths) == 1
            checks.append(case['label']+': injected ENOSPC escapes dump; old destination remains intact and diagnostic stage remains')
            tries = [n for n in ast.walk(tree) if isinstance(n, ast.Try) and
                     any(isinstance(h.type, ast.Name) and h.type.id == 'OSError' for h in n.handlers)]
            assert len(tries) == 2
            for number, statement in enumerate(tries):
                assert isinstance(statement.handlers[0].type, ast.Name)
                assert statement.handlers[0].type.id == 'OSError'
                probe = ast.FunctionDef(name='probe', args=ast.arguments(posonlyargs=[], args=[],
                    kwonlyargs=[], kw_defaults=[], defaults=[]), decorator_list=[],
                    body=[ast.Try(body=[ast.Raise(exc=ast.Name(id='PROBE_ERROR',ctx=ast.Load()))],
                        handlers=deepcopy(statement.handlers), orelse=[], finalbody=[])])
                writes = []
                error = OSError(errno.ENOSPC, 'injected outer-branch failure')
                scope = {'PROBE_ERROR':error, 'args':SimpleNamespace(output=root), 'index':17,
                         'dump':lambda *values:writes.append(values)}
                exec(compile(ast.fix_missing_locations(ast.Module(body=[probe], type_ignores=[])),
                             str(path)+':handlers_only', 'exec'), scope)
                try:
                    scope['probe']()
                except OSError as caught:
                    assert caught is error
                else:
                    raise AssertionError('Branch handler swallowed OSError.')
                assert not writes
                checks.append(case['label']+f': actual outer handler {number} rethrows the original OSError before diagnostic/branch continuation')
        assert sha(path) == case['new_driver_sha256'] and sha(old) == case['old_source_sha256']
    forbidden = ('numpy','scipy','highspy','physical_sat_engine_snapshot','physical_sat_diagonal_engine',
                 'ac_physical_context','ac_physical_context_diag')
    assert not any(name in sys.modules for name in forbidden)
    assert sha(source) == prepared['atomic_helper_sha256']
    result = dict(status='PASS_ATOMIC_DISCOVERY_DRIVER_DISPATCH_AND_FAILFAST_CONTROLS',
        checks=checks, count=len(checks), drivers=len(prepared['cases']),
        handler_probes=8, numerical_driver_modules_imported=False,
        proof_or_search_performed=False, prepared_manifest_sha256=sha(prepared_path),
        helper_sha256=sha(source), control_source_sha256=sha(__file__),
        source_bytes_unchanged=True, prior_source_hardlinks_preserved=True,
        multi_file_transaction_claimed=False)
    report = OUT/'DISPATCH_CONTROLS.json'
    assert not report.exists()
    helper.write_json(report, result)
    print(json.dumps(dict(status=result['status'], count=len(checks), report_sha256=sha(report))))


if __name__ == '__main__':
    main()
