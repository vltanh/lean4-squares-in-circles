#!/usr/bin/env python3
"""Four deliberately invalid trees must be rejected by the independent verifier."""
import json,subprocess,sys,tempfile
from pathlib import Path
BASE=Path(__file__).parent
controls=[('incomplete_tree',[0]),('invalid_axis',[99]),('false_root_leaf',[-1]),('noninteger_tag',[0.5])]
rows=[]
with tempfile.TemporaryDirectory(prefix='above_side_controls_',dir=BASE) as root:
    root=Path(root)
    for name,events in controls:
        src=root/(name+'.json');report=root/(name+'_report.json')
        src.write_text(json.dumps({'status':'DISCOVERY_COMPLETE_AWAITING_EXACT_REPLAY','events':events})+'\n')
        p=subprocess.run([sys.executable,str(BASE/'verify_weak_middle_above_side_physical_certificate.py'),'--certificate',str(src),'--report',str(report)],capture_output=True,text=True)
        assert p.returncode!=0 and not report.exists(),(name,p.stdout,p.stderr)
        rows.append({'name':name,'rejected':True,'returncode':p.returncode,'reason':p.stderr.splitlines()[-1]})
out={'status':'ALL_INVALID_TREES_REJECTED','controls':rows}
(BASE/'weak_middle_above_side_physical_negative_controls.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
