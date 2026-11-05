"""One ordinary continuation after the already-running C887 batch finishes.
No existing job or source is modified. A complete frontier is copied only
after its source manifest is final. A cancellation marker stops this waiter.
"""
from pathlib import Path
import json,hashlib,time,subprocess,sys
HERE=Path(__file__).resolve().parent
source=HERE/'c887_whole_general_continued';target=HERE/'c887_whole_scalar_first'
log=HERE/'c887_whole_general_continued.log';cancel=HERE/'C887_NEXT_BATCH_CANCEL'
receipt=HERE/'C887_NEXT_BATCH_MANAGER.json'
def save(value):
    tmp=receipt.with_suffix('.tmp');tmp.write_text(json.dumps(value,indent=2)+'\n');tmp.replace(receipt)
status=dict(status='WAITING_FOR_EXISTING_BATCH',source=str(source),output=str(target),current_sources_unchanged=True,no_original_or_mask_credit=True)
save(status)
while True:
    if cancel.exists():
        save(dict(status,status='CANCELLED_BEFORE_CONTINUATION'));sys.exit(0)
    if log.exists():
        with log.open('rb')as f:
            f.seek(max(0,log.stat().st_size-8192));tail=f.read().decode()
        if any(line.startswith('FINISHED ')for line in tail.splitlines()):break
    time.sleep(10)
raw=(source/'MANIFEST.json').read_bytes();m=json.loads(raw);status['source_manifest_sha256']=hashlib.sha256(raw).hexdigest()
if m['whole_candidate_closed']:
    finished=source
    save(dict(status,status='EXISTING_BATCH_CANDIDATE_CLOSED'))
else:
    assert not target.exists()
    command=[sys.executable,'-B',str(HERE/'c_dfs_resume_scalar_first.py'),str(source),str(target),'--nodes','200','--depth','26','--resume-stopped']
    status.update(status='RUNNING_ORDINARY_CONTINUATION',command=command)
    with (HERE/'c887_whole_scalar_first.log').open('w')as output:
        p=subprocess.Popen(command,cwd=HERE,stdout=output,stderr=subprocess.STDOUT);status['pid']=p.pid;save(status);print('STARTED',p.pid,str(target),flush=True);code=p.wait()
    if code:
        save(dict(status,status='CONTINUATION_ERROR',returncode=code));sys.exit(code)
    binding=source/'FRESH_ANCESTRY_BINDING.json'
    if binding.exists():(target/binding.name).write_bytes(binding.read_bytes())
    finished=target
    m=json.loads((finished/'MANIFEST.json').read_text());save(dict(status,status='CONTINUATION_BATCH_FINISHED',processed=len(m['nodes']),pending=len(m['pending']),stopped=len(m['stopped']),whole_candidate_closed=m['whole_candidate_closed']))
if not m['whole_candidate_closed']:
    print('BATCH_OPEN',len(m['pending']),len(m['stopped']),flush=True);sys.exit(0)
# A complete numerical cover triggers the required fresh original-prefix replay.
report=HERE/'C887_COMPLETE_WHOLE_ORIGINAL_REPLAY.json'
command=[sys.executable,'-B','-S',str(HERE/'check_c887_general_cover_rejoined.py'),str(finished/'MANIFEST.json'),str(report),'--union',str(HERE/'c887_fresh_dg_union_refined/MANIFEST.json')]
save(dict(status,status='RUNNING_FULL_ORIGINAL_REPLAY',command=command,finished_manifest=str(finished/'MANIFEST.json')))
with (HERE/'c887_complete_whole_original_replay.log').open('w')as output:code=subprocess.run(command,cwd=HERE,stdout=output,stderr=subprocess.STDOUT).returncode
save(dict(status,status='FULL_REPLAY_FINISHED'if code==0 else'FULL_REPLAY_ERROR',returncode=code,report=str(report),finished_manifest=str(finished/'MANIFEST.json')))
print('FULL_REPLAY_EXIT',code,str(report),flush=True)
