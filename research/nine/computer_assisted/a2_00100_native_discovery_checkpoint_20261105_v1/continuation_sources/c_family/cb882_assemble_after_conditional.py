"""After node61 closes, graft it and continue the entire original Cb882 cover.

This waiter never imports a proof producer/checker and never changes active
sources. A full original arithmetic gate runs only after a whole candidate.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
CONDITIONAL = HERE / 'cb882_node61_cached_dfs'
WHOLE = HERE / 'cb882_dfs_cavity'
GRAFT = HERE / 'cb882_whole_after_complete_node61'
OUTPUT = HERE / 'cb882_whole_after_node61_continued'
RECEIPT = HERE / 'CB882_WHOLE_ASSEMBLY_MANAGER.json'
CANCEL = HERE / 'CB882_WHOLE_ASSEMBLY_CANCEL'
LOG = HERE / 'cb882_node61_cached_dfs.log'


def save(value):
    temporary = RECEIPT.with_suffix('.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(RECEIPT)


def run(command, log):
    status.update(command=command)
    with log.open('w') as output:
        process = subprocess.Popen(command, cwd=HERE, stdout=output, stderr=subprocess.STDOUT)
        status['pid'] = process.pid
        save(status)
        result = process.wait()
    if result:
        save(dict(status, status='ERROR', returncode=result, log=str(log)))
        sys.exit(result)


status = dict(status='WAITING_FOR_CURRENT_CONDITIONAL_BATCH', conditional=str(CONDITIONAL),
              whole=str(WHOLE), unchanged_active_sources=True,
              no_original_or_mask_credit=True)
save(status)
while True:
    if CANCEL.exists():
        save(dict(status, status='CANCELLED_BEFORE_ASSEMBLY'))
        sys.exit(0)
    if LOG.exists():
        with LOG.open('rb') as stream:
            stream.seek(max(0, LOG.stat().st_size - 8192))
            tail = stream.read().decode()
        if any(line.startswith('FINISHED ') for line in tail.splitlines()):
            break
    time.sleep(10)

raw = (CONDITIONAL / 'MANIFEST.json').read_bytes()
manifest = json.loads(raw)
status['conditional_manifest_sha256'] = hashlib.sha256(raw).hexdigest()
if not manifest['conditional_candidate_closed']:
    save(dict(status, status='CONDITIONAL_BATCH_REMAINS_OPEN', nodes=len(manifest['nodes']),
              pending=len(manifest['pending']), stopped=len(manifest['stopped'])))
    print('CONDITIONAL_BATCH_OPEN', len(manifest['pending']), len(manifest['stopped']), flush=True)
    sys.exit(0)
assert not manifest['pending'] and not manifest['stopped']

status['status'] = 'ASSEMBLING_COMPLETE_CONDITIONAL_DISCOVERY_TREE'
run([sys.executable, '-B', '-S', str(HERE / 'graft_complete_c_conditional.py'),
     str(WHOLE / 'MANIFEST.json'), str(CONDITIONAL / 'MANIFEST.json'), '61', str(GRAFT)],
    HERE / 'cb882_complete_node61_graft.log')
assembled = json.loads((GRAFT / 'MANIFEST.json').read_text())
finished = GRAFT
if not assembled['whole_candidate_closed']:
    status['status'] = 'CONTINUING_ENTIRE_ORIGINAL_COVER'
    run([sys.executable, '-B', str(HERE / 'c_dfs_resume_cached_cavity.py'), str(GRAFT),
         str(OUTPUT), '--nodes', '200', '--depth', '26', '--resume-stopped'],
        HERE / 'cb882_whole_after_node61_continued.log')
    finished = OUTPUT
    assembled = json.loads((finished / 'MANIFEST.json').read_text())
if not assembled['whole_candidate_closed']:
    save(dict(status, status='WHOLE_ORIGINAL_BATCH_REMAINS_OPEN',
              finished_manifest=str(finished / 'MANIFEST.json'), nodes=len(assembled['nodes']),
              pending=len(assembled['pending']), stopped=len(assembled['stopped'])))
    print('WHOLE_BATCH_OPEN', len(assembled['pending']), len(assembled['stopped']), flush=True)
    sys.exit(0)

status['status'] = 'RUNNING_FRESH_WHOLE_ORIGINAL_EXACT_GATE'
report = HERE / 'CB882_COMPLETE_WHOLE_ORIGINAL_REPLAY.json'
run([sys.executable, '-B', '-S', str(HERE / 'check_c_general_cover_local.py'), 'cb882',
     str(finished / 'MANIFEST.json'), str(report), '--rotating'],
    HERE / 'cb882_complete_whole_original_replay.log')
save(dict(status, status='NATIVE_WHOLE_ORIGINAL_GATE_FINISHED', report=str(report),
          finished_manifest=str(finished / 'MANIFEST.json'), portable_gate_pending=True))
print('NATIVE_WHOLE_GATE_FINISHED', str(report), flush=True)
