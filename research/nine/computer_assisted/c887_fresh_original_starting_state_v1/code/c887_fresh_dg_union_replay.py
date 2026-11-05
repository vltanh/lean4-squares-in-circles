"""Independent whole-original D/G SAT union with exact parent-bound hull."""
from pathlib import Path
from itertools import product
import json,time
import c887_fresh_ancestry as A
import independent_physical_union_bounds as UNION
UNION.CORE=A.CHECK.CORE

def replay(manifest_path,output_prefix,post_record=None):
 start=time.monotonic();manifest_path=Path(manifest_path).resolve();raw=manifest_path.read_bytes();m=json.loads(raw)
 assert m['schema']=='fresh_c887_complete_dg_union_shave_v1'and m['completed']is True and not m['pending']
 assert m['pair']==[3,6]and m['new_original_cells']==m['new_masks']==0
 parent=Path(m['parent']['path']);assert A.sha(parent)==m['parent']['sha256']
 prior,state,adapter,checker=A.replay_bounds(parent,Path(output_prefix).with_name(Path(output_prefix).name+'_root'))
 assert state is not None and A.CHECK.CORE.state_view(state)==m['initial']
 assert state['id']==A.CHECK.TARGET and state['path']==A.CHECK.ROOT_PATH
 assert not any(kind=='sat'and tuple(pair)==(3,6)for pair,kind,choice in state['choices'])
 expected=[list(x)for x in product((3,6),(0,1),(-1,1))]
 assert m['alternatives']==expected and len(m['children'])==8
 inputs=dict(prior['input_sha256']);inputs[str(manifest_path)]=A.sha(manifest_path);children=[]
 for index,(entry,choice)in enumerate(zip(m['children'],expected)):
  assert entry['index']==index and entry['choice']==choice and entry['file']==f'child_{index}.json'
  file=manifest_path.parent/entry['file'];assert A.sha(file)==entry['sha256'];inputs[str(file)]=entry['sha256']
  rec=json.loads(file.read_text());assert rec['status']==entry['status'];children.append((choice,rec))
 union_audit,joined=UNION.check_complete_sat_union(state,(3,6),children,adapter,m['joined_original_state'])
 assert m['closed_children']==union_audit['complete_cover']['excluded_alternatives']
 assert m['status']==('CANDIDATE_CLOSED'if joined is None else'OPEN')
 post_audit=None
 if post_record is not None:
  assert joined is not None;post_record=Path(post_record).resolve();inputs[str(post_record)]=A.sha(post_record);rec=json.loads(post_record.read_text())
  assert rec['initial']==A.CHECK.CORE.state_view(joined)
  assert not any('certified_original_root_bound_'in row['name']for rd in rec['rounds']for row in rd['printed_rows'])
  post_audit,joined=A.CHECK.CORE.check_record(rec,joined,adapter)
 target_path=A.HERE.parents[1]/'computer_assisted/native_shared_bound_progress_v1/native_evidence/direct_shared_bounds_and_C_lazy_readers_native_v1/native/ac_work/tree/C887_WHOLE_HEIGHT_BOUND_STATE_BINDING.json'
 assert A.sha(target_path)=='b24a9fa7675eb4d2330518da7481e5bca75700928035d202eeb9bf964a4adf2d';inputs[str(target_path)]=A.sha(target_path)
 bad=[]if joined is None else A.deficits(A.CHECK.CORE.state_view(joined),json.loads(target_path.read_text())['state'])
 for file,digest in inputs.items():assert A.sha(file)==digest
 for file,digest in m['sources'].items():assert A.sha(file)==digest;inputs[file]=digest
 A.CHECK.BASE.verify_all_bindings();A.CHECK.HEIGHT.verify_binding();A.EXT.no_producers()
 report=dict(status='PASS_FRESH_WHOLE_C887_EXCLUSION'if joined is None else'PASS_FRESH_WHOLE_C887_COMPLETE_DG_UNION_BOUNDS',whole_original_excluded=joined is None,original_id=A.CHECK.TARGET,original_path=A.CHECK.ROOT_PATH,initial_original_bounds=prior,complete_union=union_audit,post_union_bound_audit=post_audit,certified_state=None if joined is None else A.CHECK.CORE.state_view(joined),old_starting_state_implied=not bad,old_state_interval_deficits=bad,input_sha256=inputs,new_row_counts=dict(A.EXT.COUNTS),all_eight_closed_alternatives_checked=True,child_auxiliaries_discarded=True,original_parent_path_unchanged=True,missing_archived_bound_state_assumed=False,no_selected_child_assumed=True,new_original_cells=0,new_masks=0,numerical_producer_imported=False,seconds=time.monotonic()-start)
 return report,joined
