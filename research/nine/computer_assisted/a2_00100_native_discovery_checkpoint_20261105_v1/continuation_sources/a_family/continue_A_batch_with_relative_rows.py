#!/usr/bin/env python3
"""Resume one completed ordinary A batch with the frozen v9 row extension."""
from pathlib import Path
import argparse,datetime,hashlib,json,subprocess,sys,time
HERE=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('h',type=int,choices=(0,3,4));a=p.parse_args();h=a.h
old=HERE/f'a3_conditional_H{h}_sparse_cont6';new=HERE/f'a3_conditional_H{h}_relative_cont7'
log=HERE/f'a3_conditional_H{h}_sparse_cont6.log';outlog=HERE/f'a3_conditional_H{h}_relative_cont7.log'
stop=HERE/f'STOP_PENDING_V9_H{h}'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
print('WAITING_FOR_COMPLETED_V8_BATCH',h,str(log),flush=True)
while True:
    if stop.exists():print('PENDING_CONTINUATION_STOPPED',h,flush=True);sys.exit(0)
    text=log.read_text()
    if 'CONTINUED_TREE_RESULT' in text:break
    if 'Traceback (most recent call last):' in text:
        raise RuntimeError('Current batch failed; do not launch automatically.')
    time.sleep(15)
raw=(old/'manifest.json').read_bytes();m=json.loads(raw)
assert not new.exists()
ready=json.loads((HERE/'V9_RELATIVE_SUPPORT_ADOPTION_READY.json').read_text())
assert ready['status']=='READY_FOR_NEXT_ORDINARY_CONTINUATION'
for f in ready['files']:assert sha(f['path'])==f['sha256'],f['path']
assert ready['branching_policy_block_text_identical_to_v8'] is True
assert ready['local_new_family_literals']>0
for n in m['nodes']:assert sha(old/n['file'])==n['sha256'],n['index']
assert (old/'manifest.json').read_bytes()==raw
leaves=[n for n in m['nodes']if not n.get('children')]
if not any(n['status']=='OPEN'for n in leaves):
    print('COMPLETE_CANDIDATE_REQUIRES_FRESH_REPLAY',h,len(m['nodes']),flush=True);sys.exit(0)
command=[sys.executable,'-B',str(HERE/'run_conditional_global_corner_relative_v9.py'),'--h-component',str(h),'--policy','I-owned',str(old),str(new),'--max-depth','18','--max-new-nodes','128','--rounds','1','--proxy-rounds','0','--extra-existing-rounds','0']
receipt={'status':'V9_DISCOVERY_CONTINUATION_LAUNCH','created_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'H_component':h,'source':str(old),'source_manifest_sha256':hashlib.sha256(raw).hexdigest(),'source_nodes':len(m['nodes']),'source_OPEN_leaves':sum(n['status']=='OPEN'for n in leaves),'every_source_node_sha_checked':True,'output':str(new),'command':command,'branching_policy_unchanged':True,'new_original_cells':0,'new_masks':0}
(HERE/f'V9_LAUNCH_H{h}.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt),flush=True)
with outlog.open('w')as output:subprocess.run(command,cwd=HERE,stdout=output,stderr=subprocess.STDOUT,check=True)
print('V9_BATCH_FINISHED',h,flush=True)
