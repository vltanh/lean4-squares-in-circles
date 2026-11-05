#!/usr/bin/env python3
"""Prepare I/O-only immutable variants from hash-identified recovered sources."""
if not __debug__:
    raise RuntimeError('Assertions must be enabled.')
from pathlib import Path
import ast
import difflib
import hashlib
import json
import re

WORK = Path('/workspace/scratch/f9f48fcfb253')
ARCHIVE = WORK/'d_work/reset_sources_d989c83'
PATHS_SHA = '87fa02855665f17f0375788b8d8a0f9372929fc34b695f01beb65d2d51045b05'
HERE = WORK/'ac_work/tree'
OUT = WORK/'ac_work/recovery_064e4aa/atomic_driver_preparation'
HELPER_SHA = '2f17219f8689b343f7f1c29e7a314272bd5ace8d25fbee11f58cd20b44543eb3'
CASES = (
    ('A3', 'd_work/resume_a_component3_direct_shared_round_tree_v13.py',
     '4848dd2f4327570ad21e0b92130047ebad4c0229aeee4a56c251311120e2662d',
     'd_work/resume_a_component3_direct_shared_atomic_tree_v14.py'),
    ('C887', 'ac_work/tree/resume_c887_direct_shared_height_each_round_lazy_tree_v3.py',
     'd674c59c7842884c8be9f74a96d153aa47bef40f00aa47d23113331f239286f1',
     'ac_work/tree/resume_c887_direct_shared_height_each_round_atomic_tree_v4.py'),
    ('Cb_prior_policy', 'd_work/cb882_shared_height_bounds/resume_cb882_shared_height_bounds_adaptive_lazy_tree.py',
     '05572344f495b69a05e9a525a25a5f5eeaf7c4f187a30480553a6fca331d2f99',
     'd_work/cb882_shared_height_bounds/resume_cb882_shared_height_bounds_adaptive_atomic_tree_v2.py'),
    ('Cb_prepared_each_round', 'ac_work/tree/resume_cb882_shared_height_direct_each_round_lazy_tree.py',
     '4c38151d1b6b6661957e1e4b43dda8bf1bf6d0bba5908033f9abe292992d5112',
     'ac_work/tree/resume_cb882_shared_height_direct_each_round_atomic_tree_v2.py'),
)
BLOCK = '''import atomic_json_checkpoint as ATOMIC
ATOMIC_SHA = '2f17219f8689b343f7f1c29e7a314272bd5ace8d25fbee11f58cd20b44543eb3'
if hashlib.sha256(Path(ATOMIC.__file__).read_bytes()).hexdigest() != ATOMIC_SHA:
    raise RuntimeError('Atomic checkpoint helper hash mismatch.')

'''
PIN = "    manifest['source_sha256'][str(Path(ATOMIC.__file__).resolve())]=ATOMIC_SHA\n"
OLD_DUMP = "def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\\n')"
NEW_DUMP = 'def dump(p,x):ATOMIC.write_json(p,x)'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    assert sha(ARCHIVE/'PATHS.json') == PATHS_SHA
    assert sha(HERE/'atomic_json_checkpoint.py') == HELPER_SHA
    entries = json.loads((ARCHIVE/'PATHS.json').read_text())['files']
    by_path = {entry['path']:entry for entry in entries}
    assert len(by_path) == len(entries)
    OUT.mkdir(parents=True, exist_ok=False)
    cases = []
    for label, old_relative, expected, new_relative in CASES:
        old_path = WORK/old_relative
        entry = by_path[str(old_path)]
        assert entry['sha256'] == expected
        content = ARCHIVE/'sources'/expected
        raw = content.read_bytes()
        assert sha(content) == expected and len(raw) == entry['bytes']
        old = raw.decode('utf-8')
        assert old.count(OLD_DUMP) == 1 and '\nimport atomic_json_checkpoint ' not in old
        backup = OUT/('BASELINE_'+label+'.py')
        with backup.open('xb') as stream:
            stream.write(raw)
        new = old.replace('\ndef sha(p):', '\n'+BLOCK+'def sha(p):', 1)
        new = new.replace(OLD_DUMP, NEW_DUMP, 1)
        anchor = "    manifest['source_sha256'][str(Path(__file__).resolve())]=sha(__file__)\n"
        assert new.count(anchor) == 1
        new = new.replace(anchor, anchor+PIN, 1)
        pattern = re.compile(r'^( +)except Exception as error:', re.M)
        matches = list(pattern.finditer(new))
        assert len(matches) == 2
        new = pattern.sub(lambda m: m[1]+'except OSError:\n'+m[1]+'    raise\n'+m[0], new)
        normalized = new.replace(BLOCK, '', 1).replace(NEW_DUMP, OLD_DUMP, 1).replace(PIN, '', 1)
        normalized = re.sub(r'^( +)except OSError:\n\1    raise\n', '', normalized, flags=re.M)
        assert normalized == old, 'A non-I/O byte was changed.'
        compile(new, new_relative, 'exec')
        tree = ast.parse(new)
        handlers = [node for node in ast.walk(tree) if isinstance(node, ast.ExceptHandler)
                    and isinstance(node.type, ast.Name) and node.type.id == 'OSError']
        assert len(handlers) == 2
        assert all(len(node.body) == 1 and isinstance(node.body[0], ast.Raise)
                   and node.body[0].exc is None for node in handlers)
        target = WORK/new_relative
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('x') as stream:
            stream.write(new)
        diff = OUT/(label+'_ATOMIC_FROM_BASELINE.diff')
        with diff.open('x') as stream:
            stream.writelines(difflib.unified_diff(old.splitlines(True), new.splitlines(True),
                fromfile=old_relative, tofile=new_relative))
        cases.append(dict(label=label, archive_original_path=str(old_path),
            old_source_sha256=expected, recovered_baseline=str(backup),
            new_driver=str(target), new_driver_sha256=sha(target),
            diff=str(diff), diff_sha256=sha(diff), exact_non_io_byte_equality=True,
            os_error_failfast_handlers=2, numeric_driver_imported=False, launched=False))
    result = dict(status='PREPARED_IMMUTABLE_ATOMIC_DISCOVERY_VARIANTS_NOT_LAUNCHED',
        builder_sha256=sha(__file__), source_archive_path_map_sha256=PATHS_SHA,
        atomic_helper_sha256=HELPER_SHA, cases=cases, original_sources_overwritten=False,
        numerical_search_started=False, checker_or_row_rule_changed=False,
        multi_file_transaction_claimed=False,
        Cb_shared_bound_variants_require_recovery_or_fresh_reproof_of_missing_source_record=True,
        source_record_gap_sha256='88fe0a11aed912184b29e8868fd1317e70b5c6dbd29a6107d3651d90a687e2d8')
    output = OUT/'PREPARATION.json'
    with output.open('x') as stream:
        json.dump(result, stream, indent=2); stream.write('\n')
    print(json.dumps(dict(status=result['status'], report_sha256=sha(output),
                          drivers=[dict(label=x['label'],sha256=x['new_driver_sha256']) for x in cases])))


if __name__ == '__main__':
    main()
