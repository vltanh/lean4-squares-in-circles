#!/usr/bin/env python3
"""Focused domain/header/literal/cache-restoration controls; no weighted replay."""
if not __debug__:raise RuntimeError('Controls require assertions.')
from pathlib import Path
from copy import deepcopy
from fractions import Fraction as F
import hashlib,json,subprocess,sys
import historical_source_cache as C
import replay_recovered_813 as R

def rejected(action):
    try:action()
    except (AssertionError,ValueError,KeyError,TypeError):return
    raise AssertionError('damaged control unexpectedly accepted')

def run(output):
    output=Path(output);assert not output.exists()
    before={str(p):C.sha(p)for p in Path(__file__).resolve().parent.rglob('*')if p.is_file()}
    evidence,cache=C.validate();outer=C.read(C.read(C.BINDING)['published_outer_report']['path'])
    ref=outer['fresh_component3_shared_bound_source']['source_report'];C.embedded_reference(ref)
    bad=deepcopy(ref);bad['sha256']='0'*64;rejected(lambda:C.embedded_reference(bad))
    bad=deepcopy(ref);bad['report']['component']=1;rejected(lambda:C.embedded_reference(bad))
    damaged=2
    for key,value in [('original_id','foreign'),('original_path',[]),('all_nine_originals_retained',False),
      ('closed_shared_faces_retained',False),('new_original_cells',1),('new_masks',1),('mask','011/00')]:
        bad=deepcopy(outer);bad[key]=value;rejected(lambda bad=bad:C.check_common(bad));damaged+=1
    pb=cache['post'][1]
    for key,value in [('component',1),('closed_domain',{}),('conditional_parent',{}),('nodes',2),
      ('excluded_leaves',1),('open_leaves',0),('closed_unions',{'incomplete':1}),('rounds',8),('deductions',813),('printed_rows_checked',1941)]:
        bad=deepcopy(outer);bad[key]=value
        rejected(lambda bad=bad:C.check_open_source(bad,pb,(7,565,1436)));damaged+=1
    modules=[(C.POST,'replay_source'),(C.SHARED,'replay_source'),(C.A1,'replay_source'),(C.COMPLEMENTS,'replay_source_exclusions')]
    saved=[getattr(m,n)for m,n in modules]
    with C.InstalledCache(cache)as installed:
        returned=[getattr(m,n)('unused-output-path')for m,n in modules]
        assert installed.calls==dict(post=1,shared=1,a1=1,complements=1)
        returned[0][0]['component']=0
        assert cache['post'][0]['component']==3
    assert [getattr(m,n)for m,n in modules]==saved
    class Deliberate(Exception):pass
    try:
        with C.InstalledCache(cache):raise Deliberate()
    except Deliberate:pass
    assert [getattr(m,n)for m,n in modules]==saved
    # The inherited reconstruction is held to an empty ordinary-row list here.
    # Only the new dispatch and exact literal checks are exercised by this stub.
    saved_rebuild=R.BASE.Adapter.rebuild
    def stub(self,state,printed):assert printed==[];return {},[],state
    R.BASE.Adapter.rebuild=stub
    try:
        adapter=R.Adapter.__new__(R.Adapter)
        class Counter:recovered_I64_occurrences=0;recovered_center_occurrences=0
        adapter.checker=Counter()
        state=dict(id=C.TARGET,path=deepcopy(C.ORIGINAL_PATH))
        row=dict(index=0,coefficients=[[3,'1'],[7,'1'],[17,'-2']],rhs='-16/25',name=R.I64_NAME)
        answer,_,_=adapter.rebuild(state,[row]);assert answer[0]==R.I64
        for key,value in [('coefficients',[[3,'1'],[7,'1'],[17,'2']]),('rhs','-3/5'),('name',R.I64_NAME+'_foreign')]:
            bad=deepcopy(row);bad[key]=value;rejected(lambda bad=bad:adapter.rebuild(state,[bad]));damaged+=1
        for key,value in [('id','foreign'),('path',[])]:
            bad=deepcopy(state);bad[key]=value;rejected(lambda bad=bad:adapter.rebuild(bad,[row]));damaged+=1
        center=dict(index=1,coefficients=[[0,'1']],rhs='91/60',name='physical_center_disk_0_1_0_91/60')
        adapter.rebuild(state,[center])
        for key,value in [('coefficients',[[2,'1']]),('rhs','3/2'),('name','physical_center_disk_9_1_0_91/60')]:
            bad=deepcopy(center);bad[key]=value;rejected(lambda bad=bad:adapter.rebuild(state,[bad]));damaged+=1
    finally:R.BASE.Adapter.rebuild=saved_rebuild
    optimized=subprocess.run([sys.executable,'-O','-B','-S',str(R.HERE/'replay_recovered_813.py'),'unused-output-path'],capture_output=True,text=True)
    assert optimized.returncode!=0 and 'Exact proof replay requires assertions.'in optimized.stderr
    assert not Path('unused-output-path').exists();damaged+=1
    after={p:C.sha(p)for p in before};assert after==before
    result=dict(status='PASS_HISTORICAL_REUSE_AND_NEW_LITERAL_CONTROLS',historical_evidence=evidence,
      damaged_inputs_rejected=damaged,provider_calls_restored_after_success=True,
      provider_calls_restored_after_exception=True,returned_objects_do_not_mutate_cache=True,
      one_valid_I64_literal=True,one_valid_center_literal=True,optimized_dispatch_rejected=True,
      all_input_bytes_unchanged=True,source_sha256=before,weighted_arithmetic_run=False,
      new_original_cells=0,new_masks=0)
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k]for k in('status','damaged_inputs_rejected','weighted_arithmetic_run')}),flush=True)

if __name__=='__main__':
    assert len(sys.argv)==2;run(sys.argv[1])
