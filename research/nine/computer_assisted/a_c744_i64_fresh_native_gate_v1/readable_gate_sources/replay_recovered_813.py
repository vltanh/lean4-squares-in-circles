#!/usr/bin/env python3
"""Fresh exact seven-round narrowed proof with explicit historical source reuse."""
if not __debug__:raise RuntimeError('Exact proof replay requires assertions.')
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import argparse,hashlib,importlib.util,json,subprocess,sys,time
import historical_source_cache as CACHE

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
sys.path.insert(0,str(ROOT/'ac_work/tree'))
import verify_a_c744_component3_post_a1_bounds_lazy_tree as BASE
spec=importlib.util.spec_from_file_location('independent_center_snapshot',HERE/'independent_physical_center_disk_rows.py')
CENTER=importlib.util.module_from_spec(spec);spec.loader.exec_module(CENTER)
I64_NAME='stronger_actual_ab_064_A_c744_I_high'
I64=(((3,F(1)),(7,F(1)),(17,F(-2))),F(-16,25),I64_NAME)
_current=None

class Checker(BASE.Checker):
    def __init__(self):
        global _current
        super().__init__();self.recovered_I64_occurrences=0;self.recovered_center_occurrences=0;_current=self

class Adapter(BASE.Adapter):
    def rebuild(self,state,printed):
        ordinary=[r for r in printed if r['name']!=I64_NAME and not r['name'].startswith(CENTER.PREFIX)]
        answer,bounds,physical=super().rebuild(state,ordinary)
        for r in printed:
            if r['name']!=I64_NAME and not r['name'].startswith(CENTER.PREFIX):continue
            value=(tuple((i,F(v))for i,v in r['coefficients']),F(r['rhs']),r['name'])
            if r['name']==I64_NAME:
                assert state['id']==CACHE.TARGET and state['path']==CACHE.ORIGINAL_PATH
                assert value==I64
                self.checker.recovered_I64_occurrences+=1
            else:
                CENTER.verify_literal(value);self.checker.recovered_center_occurrences+=1
            assert r['index']not in answer;answer[r['index']]=value
        return answer,bounds,physical

def verify_frozen_inputs():
    freeze=CACHE.read(HERE/'SOURCE_BINDINGS.json')
    for rel,h in freeze['files'].items():assert CACHE.sha(HERE/rel)==h,rel
    for path,h in freeze['loaded_independent_dependency_sha256'].items():assert CACHE.sha(path)==h,path
    b=CACHE.read(HERE/'NARROWED_SOURCE_BINDING.json')
    assert b['original_id']==CACHE.TARGET and b['original_path']==CACHE.ORIGINAL_PATH
    assert b['scope']=='EXPLICIT_NARROWED_SUBSET_OF_OLD_COMPONENT3'
    assert b['source_domain']==dict(name=I64_NAME,coefficients=[[3,'1'],[7,'1'],[17,'-2']],rhs='-16/25')
    assert b['mask']=='001/00'and b['squared_radius']=='1105/256'
    assert b['new_original_cells']==b['new_masks']==0
    mp=HERE/'tree/manifest.json';m=CACHE.read(mp)
    assert CACHE.sha(mp)==b['manifest_sha256']
    assert m['narrowed_I64_source_domain']==b['source_domain']
    assert m['scope']==CACHE.POST.SCOPE and m['component']==3 and m['closed_domain']==CACHE.POST.CLOSED_DOMAIN
    assert len(m['nodes'])==1
    n=m['nodes'][0]
    assert (n['index'],n['parent'],n['depth'],n['restriction'],n['children'],n['status'])==(0,None,0,None,[],'OPEN')
    assert 'split'not in n and n['sha256']==b['record_sha256']==CACHE.sha(HERE/'tree'/n['file'])
    record=CACHE.read(HERE/'tree'/n['file'])
    assert record['initial']['id']==CACHE.TARGET and record['initial']['path']==CACHE.ORIGINAL_PATH
    assert record['id']==CACHE.TARGET and record['original_path']==CACHE.ORIGINAL_PATH
    assert record['status']=='OPEN'and len(record['rounds'])==7
    assert sum(len(r['proposals'])for r in record['rounds'])==813
    assert sum(len(r['printed_rows'])for r in record['rounds'])==1941
    assert F(16,25)>F(3,5)
    for p,h in b['new_theorem_source_sha256'].items():assert CACHE.sha(p)==h,p
    return b,record

def fresh_scalar(binding,output):
    source=binding['scalar_checker'];folder=Path(source['cover'])
    report=output.with_name(output.stem+'_FRESH_SCALAR_064.json');log=output.with_name(output.stem+'_FRESH_SCALAR_064.log')
    assert not report.exists()and not log.exists()
    with log.open('x')as stream:
        subprocess.run([sys.executable,'-B','-S',source['path'],str(folder),str(report)],check=True,stdout=stream,stderr=subprocess.STDOUT)
    value=CACHE.read(report)
    assert value['status']=='PASS_COMPLETE_EXACT_TWO_LINK_SCALAR_COVER'
    assert tuple(value[k]for k in('domains','leaves','bernstein_coefficients'))==(28,121,15125)
    assert value['frontier']==0 and value['strict_except_all_zero']is True
    assert value['coefficient']=='641/1000'and value['target_variation']=='16/25'
    return dict(path=str(report),sha256=CACHE.sha(report),report=value)

def replay(output):
    output=Path(output).resolve();assert not output.exists()
    started=time.monotonic();binding,record=verify_frozen_inputs()
    evidence,cache=CACHE.validate()
    scalar=fresh_scalar(binding,output)
    internal=output.with_name(output.stem+'_INHERITED_ENGINE_ON_NARROWED_DOMAIN.json')
    assert not internal.exists()
    old_checker,old_adapter=BASE.Checker,BASE.Adapter
    BASE.Checker,BASE.Adapter=Checker,Adapter
    try:
        with CACHE.InstalledCache(cache)as installed:
            inherited=BASE.replay(HERE/'tree',internal)
        assert installed.calls==dict(post=1,shared=1,a1=1,complements=1)
    finally:BASE.Checker,BASE.Adapter=old_checker,old_adapter
    assert _current is not None
    assert inherited['status']=='PASS_PARTIAL_TWO_LINK_COMPLEMENT_TREE'
    assert tuple(inherited[k]for k in('nodes','leaf_domains','excluded_leaves','open_leaves','rounds','deductions','printed_rows_checked'))==(1,1,0,1,7,813,1941)
    assert (_current.recovered_I64_occurrences,_current.recovered_center_occurrences)==(2,131)
    assert inherited['all_nine_originals_retained']is True and inherited['closed_shared_faces_retained']is True
    assert inherited['new_original_cells']==inherited['new_masks']==0
    evidence_after,_=CACHE.validate();assert evidence_after==evidence
    verify_frozen_inputs()
    assert not any(n in sys.modules for n in('numpy','scipy','highspy','stronger_a3_runtime','stronger_a3_runtime_v2'))
    result=dict(status='PASS_RECOVERED_NARROWED_A3_064_BOUND_RECORD_OPEN',
      original_id=CACHE.TARGET,original_path=CACHE.ORIGINAL_PATH,mask='001/00',squared_radius='1105/256',
      scope=binding['scope'],source_domain=binding['source_domain'],inherited_old_component3_domain=CACHE.POST.CLOSED_DOMAIN,
      nodes=1,leaf_domains=1,excluded_leaves=0,open_leaves=1,rounds=7,deductions=813,printed_rows_checked=1941,
      I64_literal_occurrences_checked=2,universal_center_literal_occurrences_checked=131,
      independently_checked_final_state=record['final'],
      final_state_checked_by_unchanged_record_core=True,
      source_binding_sha256=CACHE.sha(HERE/'SOURCE_BINDINGS.json'),narrowed_binding_sha256=CACHE.sha(HERE/'NARROWED_SOURCE_BINDING.json'),
      historical_source_proof_reuse=evidence,cached_source_provider_calls=installed.calls,
      inherited_engine_report=dict(path=str(internal),sha256=CACHE.sha(internal),report=inherited),
      fresh_064_scalar_replay=scalar,weighted_source_record_freshly_replayed=True,
      complete_A1_and_old_source_arithmetic_repeated=False,cold_portable_proof_claimed=False,
      old_lost_receipts_recreated=False,retained235_consumer_replayed=False,
      original_wide_promotion_requires_separate_complete_hand_attachment=True,
      all_nine_originals_retained=True,original_corners=36,original_pairs=36,marked_cones=5,closed_shared_faces_retained=True,
      new_original_cells=0,new_masks=0,lean_lake_ci_run=False,seconds=time.monotonic()-started)
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k]for k in('status','rounds','deductions','printed_rows_checked','I64_literal_occurrences_checked','universal_center_literal_occurrences_checked','complete_A1_and_old_source_arithmetic_repeated','seconds')}),flush=True)
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('output',type=Path);p.add_argument('--validate-cache-only',action='store_true');a=p.parse_args()
    if a.validate_cache_only:
        verify_frozen_inputs();evidence,_=CACHE.validate()
        assert not a.output.exists();a.output.write_text(json.dumps(evidence,indent=2)+'\n');print(json.dumps(evidence),flush=True)
    else:replay(a.output)
