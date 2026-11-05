#!/usr/bin/env python3
"""One ordinary exact positive-weight source-row round, with no LP solve."""
if not __debug__:raise RuntimeError('Exact direct replay requires assertions.')
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import hashlib,json,sys,time
import independent_original_i64_bounds as I
import original_i64_bound_rows as P
import independent_direct_use_adapter as ATTACH
import direct_shared_bound_round_snapshot as DIRECT
import independent_physical_sat_diagonal_replay as CORE

def state(value):
    result=dict(id=value['id'],path=deepcopy(value['path']))
    for name in ('angles','positions','scalar'):result[name]=tuple(tuple(map(F,z))for z in value[name])
    for name in ('differences','diagonal'):
        result[name]={tuple(z['pair']):tuple(tuple(map(F,x))for x in z['intervals'])for z in value[name]}
    return result

class Engine:
    SCALE=CORE.DENOMINATOR
    GRID=CORE.GRID
    ceil_grid=staticmethod(CORE.ceiling_grid)
    stateview=staticmethod(CORE.state_view)
    @staticmethod
    def printed(rows,indices):
        return [dict(index=k,coefficients=[[i,str(v)]for i,v in rows[k][0]],rhs=str(rows[k][1]),name=rows[k][2])for k in sorted(indices)]

class Context:
    def __init__(self,adapter,binding):self.adapter=adapter;self.binding=binding;self.R=adapter.R;self.K=adapter.K
    def collect(self,initial):
        I.assert_caller(initial)
        _,absolute,current=self.adapter.rebuild(initial,[])
        rows=P.necessary_rows(initial,self.binding)+[P.necessary_height_row(initial)]
        return rows,absolute,current,None

def run(output):
    started=time.monotonic();output=Path(output);assert not output.exists()
    binding=I.verify_binding();whole=I.read(binding['whole_original_parent']['path'])
    initial=state(whole['record']['final']);checker=ATTACH.BASE.Checker();adapter=ATTACH.Adapter(checker,binding)
    initial['choices']=adapter.choices(initial['path'])
    assert initial['choices']==[]
    context=Context(adapter,binding)
    after,round_record,terminal=DIRECT.bound_round(Engine,context,initial,(I.PREFIX,))
    assert round_record is not None and round_record['proposals']
    record=dict(id=I.TARGET,original_path=I.ORIGINAL_PATH,initial=CORE.state_view(initial),rounds=[round_record])
    if terminal is None:record.update(status='OPEN',final=CORE.state_view(after))
    else:record.update(status='CANDIDATE_CLOSED',terminal=terminal)
    checker2=ATTACH.BASE.Checker();independent=ATTACH.Adapter(checker2,binding)
    audit,final=CORE.check_record(record,initial,independent)
    assert (final is None)==(after is None)
    if final is not None:assert CORE.state_view(final)==CORE.state_view(after)
    assert independent.endpoint_uses==len(round_record['printed_rows'])>0
    assert all(len(p['weights'])==1 and p['weights'][0][1]==CORE.DENOMINATOR and p['residual_coefficients']==[]and p['residual_correction']=='0'for p in round_record['proposals'])
    assert not any(name in sys.modules for name in('numpy','scipy','highspy'))
    I.verify_binding()
    source={str(p):I.sha(p)for p in I.HERE.rglob('*')if p.is_file()}
    inputs={str(Path(m.__file__).resolve()):I.sha(m.__file__)for m in list(sys.modules.values())if getattr(m,'__file__',None)and str(Path(m.__file__).resolve()).startswith(str(I.ROOT))}
    record_path=output.with_name(output.stem+'_RECORD.json');assert not record_path.exists();record_path.write_text(json.dumps(record,indent=2)+'\n')
    report=dict(status='PASS_FIRST_EXACT_ORIGINAL_WIDE_I64_DIRECT_BOUND_USE',original_id=I.TARGET,original_path=I.ORIGINAL_PATH,
      scope=I.SCOPE,binding_sha256=I.BINDING_SHA,source_gate_sha256=binding['fresh_narrowed_source_report']['sha256'],
      original_parent=binding['whole_original_parent'],original_initial_state_unchanged=True,source_I64_predicate_not_added_to_path=True,
      ordinary_exact_audit=audit,weighted_endpoint_occurrences=independent.endpoint_uses,
      record=dict(path=str(record_path.resolve()),sha256=I.sha(record_path)),certified_final_state=CORE.state_view(final)if final else None,
      positive_unit_weights=True,zero_residual_exact=True,usual_grid_and_frame_inference=True,
      old_source_arithmetic_repeated=False,new813_source_repeated=False,historical_source_identity_revalidated=True,
      numerical_solves=0,actual_LP_use_claimed=False,cold_portable_replay_claimed=False,
      source_sha256=source,independent_loaded_dependency_sha256=inputs,new_original_cells=0,new_masks=0,seconds=time.monotonic()-started)
    output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k]for k in('status','weighted_endpoint_occurrences','ordinary_exact_audit','seconds')}),flush=True)

if __name__=='__main__':
    assert len(sys.argv)==2;run(sys.argv[1])
