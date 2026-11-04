#!/usr/bin/env python3
"""Portable exact companion comparison and damaged-row controls."""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,json,time
import coupled_three_square_energy as P
import independent_coupled_three_square_energy as R

def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--report',type=Path,default=Path('COUPLED_THREE_ENERGY_EXACT_COMPANIONS.json'))
    a=ap.parse_args();root=Path(__file__).resolve().parent;started=time.monotonic();cases=0
    intervals=[(F(a,2),F(b,2))for a in range(-2,3)for b in range(a,3)]
    for U in intervals:
        for V in intervals:
            for W in intervals:
                producer,vertices=P.upper_planes(U,V,W)
                assert vertices==R.vertices(U,V,W)
                assert producer==R.planes(U,V,W)
                cases+=1
    source=root/'coupled_three_energy_fixture.json';raw=json.loads(source.read_text())
    assert raw['schema']=='coupled_energy_arithmetic_fixture_v1'
    diffs={tuple(e['pair']):tuple(tuple(map(F,ab))for ab in e['intervals'])for e in raw['differences']}
    rows,guards=P.rows(diffs)
    for row in rows:
        assert row==R.rebuild(row[2],diffs)
        R.verify_literal(row,diffs)
    controls=[];co,rhs,name=rows[0]
    for label,row in [('rhs_reduced',(co,rhs-F(1,10),name)),
                      ('translation_broken',(co+((0,F(1)),),rhs,name)),
                      ('empty_nonempty',((),F(-1),'coupled_three_empty_0_1_2_0_0'))]:
        try:R.verify_literal(row,diffs)
        except AssertionError:controls.append(label)
        else:raise AssertionError(('corrupt row accepted',label))
    report=dict(status='PASS_EXACT_COUPLED_ENERGY_COMPANIONS',polygon_cases=cases,
        empty_point_segment_polygon_cases_retained=True,representative_original_rows=len(rows),
        independent_literal_checks=len(rows),rejected_controls=controls,seconds=time.monotonic()-started,
        source_sha256={p.name:digest(p)for p in map(Path,(__file__,P.__file__,R.__file__,source,
            root/'COUPLED_THREE_SQUARE_ENERGY_HAND_PROOF.md'))},
        input_state_replayed=False,scope='Necessary-row arithmetic and diverse reconstruction only',
        original_cells_closed=0,masks_closed=0)
    a.report.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)

if __name__=='__main__':main()
