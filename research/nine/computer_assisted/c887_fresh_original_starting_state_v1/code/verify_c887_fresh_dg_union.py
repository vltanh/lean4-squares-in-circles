from pathlib import Path
import argparse,json
import c887_fresh_dg_union_replay as A
ap=argparse.ArgumentParser();ap.add_argument('manifest',type=Path);ap.add_argument('output',type=Path);ap.add_argument('--post-record',type=Path);a=ap.parse_args()
report,_=A.replay(a.manifest,a.output.with_suffix(''),a.post_record)
a.output.write_text(json.dumps(report,indent=2)+'\n');print(report['status'],'OLD_STATE_IMPLIED',report['old_starting_state_implied'],'DEFICITS',len(report['old_state_interval_deficits']),'SECONDS',report['seconds'],flush=True)
