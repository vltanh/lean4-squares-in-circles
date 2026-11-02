#!/usr/bin/env python3
from pathlib import Path
import json,copy
import verify_lower_side_height_bridge as bridge
import verify_signed_lower_side_envelope as signed

def run(source,checker,which):
 base=json.loads(Path(source).read_text());cases=[]
 d=copy.deepcopy(base);d['schema']='incorrect';cases.append(('changed_schema',d))
 d=copy.deepcopy(base)
 if which=='bridge':d['events'][0]=[-2]
 else:d['events']=[-1]*4;d.update(nodes=4,leaves=4,perroot=[1]*4)
 cases.append(('false_whole_root',d))
 d=copy.deepcopy(base)
 if which=='bridge':d['events'][1]=d['events'][1][:-1]
 else:d['events']=d['events'][:-1]
 cases.append(('missing_child',d))
 d=copy.deepcopy(base)
 if which=='bridge':d['events'][0][0]=2
 else:d['events'][0]=3
 cases.append(('unknown_axis',d))
 controls=[];p=Path('_damaged_height_control.json')
 for name,d in cases:
  p.write_text(json.dumps(d))
  try:checker.verify(p);controls.append(dict(name=name,rejected=False))
  except (ValueError,AssertionError)as e:controls.append(dict(name=name,rejected=True,reason=str(e)[:300]))
 p.unlink();assert all(x['rejected']for x in controls)
 return dict(result='PASS',controls=controls)
if __name__=='__main__':
 Path('lower_side_height_bridge_negative_controls.json').write_text(json.dumps(run('lower_side_height_bridge.json',bridge,'bridge'),indent=2)+'\n')
 Path('signed_lower_side_envelope_negative_controls.json').write_text(json.dumps(run('signed_lower_side_envelope.json',signed,'signed'),indent=2)+'\n')
 print('Both input control suites passed')
