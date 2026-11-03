"""Independent arithmetic reader for printed whole-parent induction tables.

Uses standard-library Fraction only. It does not import any discovery code,
row generator, optimizer, or physical replayer. Physical provenance and the
acyclic original-parent interpretation require the separate complete replay.
"""
import argparse,json,hashlib
from fractions import Fraction
from pathlib import Path

DEN=1<<40

def weighted(rows,weights,bounds):
    table={r['index']:r for r in rows}
    assert len(table)==len(rows)
    acc=[Fraction(0) for _ in bounds];rhs=Fraction(0)
    for index,integer in weights:
        assert type(index) is int and type(integer) is int and integer>=0
        row=table[index];weight=Fraction(integer,DEN)
        rhs+=weight*Fraction(row['rhs'])
        for col,value in row['coefficients']:
            assert type(col) is int and 0<=col<len(acc)
            acc[col]+=weight*Fraction(value)
    return acc,rhs

def check(path):
    raw=path.read_bytes();data=json.loads(raw)
    assert data['schema']=='shared_inset_strip_exact_bound_induction_v1'
    assert data['new_branch_nodes']==0
    deductions=0;printed=0
    for ri,round_data in enumerate(data['rounds']):
        assert round_data['round']==ri
        bounds=list(map(Fraction,round_data['absolute_variable_bounds']))
        assert len(bounds)==54 and all(v>=0 for v in bounds)
        printed+=len(round_data['printed_rows'])
        for proposal in round_data['proposals']:
            co,rhs=weighted(round_data['printed_rows'],proposal['weights'],bounds)
            for col,value in proposal['objective']:co[col]-=Fraction(value)
            payment=sum(m*abs(c) for m,c in zip(bounds,co))
            assert rhs==Fraction(proposal['summed_rhs'])
            assert payment==Fraction(proposal['residual_correction'])
            assert [[i,str(c)] for i,c in enumerate(co) if c]==proposal['residual_coefficients']
            assert rhs+payment==Fraction(proposal['proved_upper'])<=Fraction(proposal['upper'])
            deductions+=1
    terminal=data.get('terminal');reserve=None
    if terminal and terminal['kind']=='positive_exact_reserve':
        bounds=list(map(Fraction,terminal['absolute_variable_bounds']))
        co,rhs=weighted(terminal['rows'],terminal['weights'],bounds)
        reserve=-rhs-sum(m*abs(c) for m,c in zip(bounds,co))
        assert reserve>0 and reserve==Fraction(terminal['reserve'])
        assert co==list(map(Fraction,terminal['weighted_coefficients']))
        assert rhs==Fraction(terminal['weighted_rhs'])
        printed+=len(terminal['rows'])
    return {'id':data['id'],'status':'PASS_PRINTED_RATIONAL_ARITHMETIC','source_sha256':hashlib.sha256(raw).hexdigest(),'deductions':deductions,'printed_rows':printed,'positive_terminal_reserve':None if reserve is None else str(reserve),'scope':'Arithmetic only; separate original-parent physical/state replay is required.'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('certificates',type=Path,nargs='+');ap.add_argument('--out',type=Path);args=ap.parse_args()
    result={'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'reports':[check(p) for p in args.certificates]}
    text=json.dumps(result,indent=2)+'\n'
    if args.out:args.out.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
