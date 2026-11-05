#!/usr/bin/env python3
"""One-for-one B continuation; arithmetic gate only for a complete original."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, subprocess, sys, time

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent/'b_family/source'
PRIOR = HERE.parent/'b_family/b16a_I32_complete_H_checkpoint'
ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('current', type=Path)
ap.add_argument('next', type=Path)
ap.add_argument('--difference', action='store_true')
ap.add_argument('--max-depth', type=int, required=True)
ap.add_argument('--max-new-nodes', type=int, default=384)
a = ap.parse_args()
current, following = a.current.resolve(), a.next.resolve()
log = current.with_suffix('.log')
receipt = following.with_name(following.name+'_MANAGER.json')
cancel = following.with_name(following.name+'_CANCEL')

def save(status, **fields):
    data = dict(status=status, current=str(current), next=str(following),
                updated=datetime.now(timezone.utc).isoformat(),
                numerical_jobs_added_in_parallel=0, new_original_cells=0,
                new_masks=0, **fields)
    temporary = receipt.with_suffix('.tmp.json')
    temporary.write_text(json.dumps(data, indent=2)+'\n')
    temporary.replace(receipt)

def sha(path):
    with Path(path).open('rb') as handle:
        return hashlib.file_digest(handle, 'sha256').hexdigest()

def manifest_at(folder):
    result = json.loads((folder/'manifest.json').read_text())
    assert result['completed'] is True
    for entry in result['nodes']:
        assert sha(folder/entry['file']) == entry['sha256']
    for group in ('sources','accepted_geometric_sources'):
        for path, digest in result[group].items():
            assert sha(path) == digest
    return result

def exact_if_complete(folder, manifest):
    if manifest['status'] not in ('CANDIDATE_CLOSED','CANDIDATE_COVER_CLOSED'):
        return False
    assert all(n['status'] != 'OPEN' for n in manifest['nodes'])
    report = folder.with_name(folder.name+'_COMPLETE_ORIGINAL_REPLAY.json')
    exact_log = folder.with_name(folder.name+'_COMPLETE_ORIGINAL_REPLAY.log')
    assert not report.exists()
    save('FRESH_WHOLE_ORIGINAL_ARITHMETIC_REPLAY_RUNNING', tree=str(folder))
    command = [sys.executable,'-B','-S',str(SOURCE/'verify_b_relative_support_chord_tree.py'),
               str(folder/'manifest.json'),str(report),'--packet',str(PRIOR)]
    with exact_log.open('w') as output:
        result = subprocess.run(command, stdout=output, stderr=subprocess.STDOUT)
    assert result.returncode == 0, f'Fresh exact gate failed; see {exact_log}'
    replay = json.loads(report.read_text())
    assert replay['status'] == 'PASS_COMPLETE_ORIGINAL_PHYSICAL_TREE'
    assert replay['complete'] is True and replay['whole_original_proved'] is True
    assert replay['open_leaves'] == 0
    save('FRESH_NATIVE_WHOLE_ORIGINAL_PASS_PORTABLE_GATE_STILL_REQUIRED',
         tree=str(folder), exact_report=str(report), exact_report_sha256=sha(report),
         original_id=replay['initial_original_id'], portable_replay_done=False)
    return True

try:
    save('WAITING_FOR_CURRENT_BATCH_NO_EXTRA_NUMERICAL_JOB')
    while True:
        if cancel.exists():
            save('CANCELLED_BEFORE_LAUNCH')
            sys.exit(0)
        tail = ''
        if log.exists():
            with log.open('rb') as handle:
                handle.seek(max(0, log.stat().st_size-12000))
                tail = handle.read().decode(errors='replace')
        if 'LAZY_CONTINUATION_RESULT' in tail:
            break
        if 'Traceback (most recent call last)' in tail:
            raise RuntimeError('Current driver failed; preserve its complete saved frontier.')
        time.sleep(5)
    before = manifest_at(current)
    if exact_if_complete(current, before):
        sys.exit(0)
    assert not following.exists()
    driver = ('resume_b_relative_support_difference_deferred_tree.py' if a.difference
              else 'resume_b_relative_support_cavity_tree.py')
    command = [sys.executable,'-B',str(SOURCE/driver),str(current),str(following),
               '--packet',str(PRIOR),'--rounds','1','--existing-rounds','1',
               '--proxy-rounds','0','--max-depth',str(a.max_depth),
               '--max-new-nodes',str(a.max_new_nodes)]
    if a.difference:
        command += ['--difference-rounds','1']
    save('ORDINARY_NEXT_WHOLE_BATCH_RUNNING', command=command,
         complete_previous_manifest_sha256=sha(current/'manifest.json'))
    with following.with_suffix('.log').open('w') as output:
        result = subprocess.run(command, stdout=output, stderr=subprocess.STDOUT)
    assert result.returncode == 0
    after = manifest_at(following)
    if not exact_if_complete(following, after):
        save('ORDINARY_NEXT_BATCH_FINISHED_OPEN', nodes=len(after['nodes']),
             manifest_sha256=sha(following/'manifest.json'))
except BaseException as error:
    if not isinstance(error, SystemExit):
        save('FAILED_OR_INTERRUPTED_NO_NEW_CREDIT', error=repr(error))
    raise
