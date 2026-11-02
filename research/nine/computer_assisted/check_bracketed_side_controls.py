"""Damaged-input checks for both small exact Fraction certificates."""
from pathlib import Path
from tempfile import TemporaryDirectory
import copy,hashlib,json
import verify_signed_lower_side_height as signed
import verify_bracketed_side_upper_height as upper
HERE=Path(__file__).resolve().parent

def main():
    records=[]
    for name,checker in [('signed_lower_side_height_candidate.json',signed),('bracketed_side_upper_height_candidate.json',upper)]:
        original=json.loads((HERE/name).read_text())
        damaged=[]
        d=copy.deepcopy(original);d['nodes']=d['nodes'][:-1];damaged.append(('missing final leaf',d))
        d=copy.deepcopy(original);d['nodes'][0]=4;damaged.append(('unknown node tag',d))
        d=copy.deepcopy(original);d['nodes']=[3];d['leaves']=1;d['maximum_depth']=0;damaged.append(('forged root leaf',d))
        d=copy.deepcopy(original);d['nodes'][0]=True;damaged.append(('noninteger node tag',d))
        with TemporaryDirectory(prefix='weak-middle-side-controls-') as temp:
            path=Path(temp)/'damaged.json'
            for label,data in damaged:
                path.write_text(json.dumps(data)+'\n')
                try:checker.verify(path)
                except (AssertionError,ValueError,TypeError) as exc:
                    records.append({'certificate':name,'damage':label,'status':'REJECTED','exception':type(exc).__name__})
                else:raise AssertionError(('damaged certificate accepted',name,label))
    out={'status':'ALL_DAMAGED_CONTROLS_REJECTED','records':records,
         'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (HERE/'bracketed_side_negative_controls.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
