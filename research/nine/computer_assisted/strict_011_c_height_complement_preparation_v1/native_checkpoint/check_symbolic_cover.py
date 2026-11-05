#!/usr/bin/env python3
"""Exact algebra/source controls for a prepared cover, with no scalar/LP run."""
if not __debug__:
    raise RuntimeError('Exact symbolic controls require assertions.')
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import argparse
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
GUARD='4c1fb0040f43281fd6e21bbece48d7293d0310a7341f490930c40ef51b689023'
ROOT='f67d826cbf6098191ced2319ff35acdeb752579cf9d5f0ef8a59bde6e1969f8b'
def digest(path):return sha256(Path(path).read_bytes()).hexdigest()
def main():
    parser=argparse.ArgumentParser();parser.add_argument('--guard-folder',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    folder=args.guard_folder.resolve();binding=folder/'PREMISE_BINDINGS.json'
    assert digest(binding)==GUARD
    value=json.loads(binding.read_text())
    for name,entry in value['files'].items():
        path=(folder/name).resolve();assert path.is_relative_to(folder)and not(folder/name).is_symlink()
        assert path.stat().st_size==entry['bytes']and digest(path)==entry['sha256']
    assert digest(folder/'callers/representative.json')==ROOT
    # Coordinates are (y_B,y_C,y_D). Expand s*(y_C-y_B)+t*(y_D-y_C).
    signs=((1,1),(1,-1),(-1,1),(-1,-1))
    forms=[[-s,s-t,t]for s,t in signs]
    assert forms==[[-1,0,1],[-1,2,-1],[1,-2,1],[1,0,-1]]
    rows=[dict(branch=k,coefficients=[[3,-a],[5,-b],[7,-c]],rhs='-21/100')
          for k,(a,b,c)in enumerate(forms)]
    for row in rows:row['coefficients']=[item for item in row['coefficients']if item[1]]
    # Exact representative sign and threshold faces. These are controls for
    # the algebra; the universal identity is proved in the accompanying hand.
    tests=0;faces=0
    values=[F(-3),F(-21,100),F(-7,100),F(0),F(7,100),F(21,100),F(3)]
    for a,b,c in product(values,repeat=3):
        W=abs(b-a)+abs(c-b);L=[x*a+y*b+z*c for x,y,z in forms]
        assert max(L)==W
        assert (W>F(21,100))==any(z>F(21,100)for z in L)
        if W>F(21,100):assert any(z>=F(21,100)for z in L)
        if W==F(21,100):faces+=1;assert any(z==F(21,100)for z in L)
        tests+=1
    report=dict(status='PASS_PREPARED_C_HEIGHT_SYMBOLIC_COVER_AND_SOURCE_PINS',
        source_sha256={str(HERE/'check_symbolic_cover.py'):digest(HERE/'check_symbolic_cover.py'),
                       str(HERE/'C_HEIGHT_COMPLEMENT.md'):digest(HERE/'C_HEIGHT_COMPLEMENT.md')},
        guard_binding_sha256=GUARD,root_document_sha256=ROOT,
        signs=[list(z)for z in signs],forms=forms,branch_rows=rows,
        exact_control_triples=tests,threshold_faces=faces,
        universal_scalar_replayed=False,cover_installed=False,numerical_solver_called=False,
        original_cell_credit=0,whole_mask_credit=0)
    with args.output.open('x')as stream:json.dump(report,stream,indent=2,sort_keys=True);stream.write('\n')
    print(json.dumps(dict(status=report['status'],report_sha256=digest(args.output))))
if __name__=='__main__':main()
