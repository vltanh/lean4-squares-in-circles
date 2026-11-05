"""Full C887 tree replay with fresh original+DG-union starting-state proof."""
from pathlib import Path
import argparse,json
import c887_fresh_dg_union_replay as ROOT
A=ROOT.A;CHECK=A.CHECK
ap=argparse.ArgumentParser();ap.add_argument('manifest',type=Path);ap.add_argument('output',type=Path);ap.add_argument('--union',required=True,type=Path);ap.add_argument('--post-record',type=Path);args=ap.parse_args()

def original_state(adapter,bindings,output):
 report,proved=ROOT.replay(args.union,output.with_name(output.stem+'_fresh_root'),args.post_record)
 assert proved is not None and report['old_starting_state_implied']and not report['old_state_interval_deficits']
 target_path=A.HERE.parents[1]/'computer_assisted/native_shared_bound_progress_v1/native_evidence/direct_shared_bounds_and_C_lazy_readers_native_v1/native/ac_work/tree/C887_WHOLE_HEIGHT_BOUND_STATE_BINDING.json'
 assert A.sha(target_path)=='b24a9fa7675eb4d2330518da7481e5bca75700928035d202eeb9bf964a4adf2d'
 target=json.loads(target_path.read_text())['state'];assert target['id']==CHECK.TARGET and target['path']==CHECK.ROOT_PATH
 assert not A.deficits(CHECK.CORE.state_view(proved),target)
 for file,digest in report['input_sha256'].items():assert A.sha(file)==digest;bindings[file]=digest
 for file,digest in report['initial_original_bounds']['local_transport']['input_sha256'].items():assert A.sha(file)==digest;bindings[file]=digest
 root_report=output.with_name(output.stem+'_fresh_root_report.json');root_report.write_text(json.dumps(report,indent=2)+'\n')
 bindings[str(root_report)]=A.sha(root_report)
 return dict(fresh_original_complete_dg_union_proof=report,starting_state_rederived_without_missing_archive=True,componentwise_interval_weakenings_checked=207),A.from_view(target,adapter),{}
CHECK.original_state=original_state
CHECK.Adapter=A.EXT.extend_adapter(CHECK.Adapter,allow_rotating=True)
report=CHECK.replay(args.manifest,args.output);A.EXT.no_producers()
report['independently_reconstructed_new_row_counts']=dict(A.EXT.COUNTS)
report['starting_state_rederived_without_missing_archive']=True
args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(A.EXT.COUNTS),flush=True)
