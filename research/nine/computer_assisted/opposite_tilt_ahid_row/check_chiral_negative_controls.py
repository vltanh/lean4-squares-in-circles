#!/usr/bin/env python3
"""Damage controls for exact table/coverage enforcement, using temporary copies."""
from copy import deepcopy
from pathlib import Path
from tempfile import TemporaryDirectory
import json,subprocess,sys
import verify_chiral_cover as checker

if not __debug__:
    raise RuntimeError('Exact negative controls require assertions')


def run(directory):
    name,expected=checker.expected_domains()[0]
    original=json.loads((directory/'cover'/name).read_text())
    variants=[]
    bad=deepcopy(original);bad['leaves'].pop();variants.append(('omit terminal leaf',bad))
    bad=deepcopy(original);bad['root_upper']='5/13';variants.append(('change closed angle root',bad))
    bad=deepcopy(original);bad['owners'][0]=3;variants.append(('change actual owner',bad))
    bad=deepcopy(original);bad['leaves'][0]['weights'][0]=2**bad['leaves'][0]['weight_power']+1;variants.append(('invalid absolute-value weight',bad))
    bad=deepcopy(original);bad['variation_certified_candidate']='23/100';variants.append(('weaken declared scalar margin',bad))
    bad=deepcopy(original)
    for leaf in bad['leaves']:leaf['weights']=[0]*5
    variants.append(('destroy supporting polynomial weights',bad))
    bad=deepcopy(original);bad['leaves'][0]['path'].append([4,0]);variants.append(('unknown split coordinate',bad))
    results=[]
    with TemporaryDirectory(prefix='chiral-row-damage-')as temporary:
        for label,data in variants:
            path=Path(temporary)/name;path.write_text(json.dumps(data))
            try:checker.check_file(path,expected)
            except(AssertionError,KeyError,ValueError,IndexError):results.append({'control':label,'status':'REJECTED'})
            else:raise AssertionError('Damaged certificate accepted: '+label)
    proc=subprocess.run([sys.executable,'-O','-B','-S',str(directory/'verify_chiral_cover.py'),'--help'],capture_output=True,text=True)
    assert proc.returncode!=0 and 'Python -O is not supported'in proc.stderr
    results.append({'control':'disable assertions with Python -O','status':'REJECTED'})
    return {'status':'PASS_EIGHT_DAMAGED_CONTROLS_REJECTED','controls':results,
            'new_original_cells_closed':0,'new_masks_closed':0}

if __name__=='__main__':
    folder=Path(__file__).parent
    result=run(folder);folder.joinpath('NEGATIVE_CONTROLS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
