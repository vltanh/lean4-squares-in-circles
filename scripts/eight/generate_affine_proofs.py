#!/usr/bin/env python3
"""Emit ordinary Lean proof terms for every original affine row.

Only rational square-root brackets are calculated here.  Row consequences are
proved by PreparedRow.claim from the rational NumericValid predicate, with
proof scripts left uncompiled as requested.  This program never invokes Lean,
the JavaScript verifier, CI, or an audit/checker.
"""
from pathlib import Path
from fractions import Fraction
from math import isqrt
import argparse
import json

SCALE=10**14
def f(x): return Fraction(str(x))
def q(x):
    x=f(x)
    return str(x.numerator) if x.denominator==1 else f'({x.numerator}/{x.denominator})'
def iv(xs):return '⟨'+','.join(q(x) for x in xs)+'⟩'
def root(x):
    x=f(x)
    k=isqrt((x.numerator*SCALE*SCALE)//x.denominator)
    return Fraction(k,SCALE),Fraction(k+1,SCALE)
def discr(a,Q,u):
    u=f(u)
    return (u+1)**2+4*(1+u*u)*(Q-Fraction(1,2)) if a['kind']=='O' else (u+1)**2-(1+u*u)*Fraction(71,36)
def roots(a,Q):
    if a['kind']=='C' and f(a['hi'])<=Fraction(6,7):return [(0,0),(0,0),(0,0)]
    return [root(discr(a,Q,a['lo'])),root(discr(a,Q,a['hi'])),root(Q) if a['kind']=='O' else (0,0)]
def norm_bracket(r,arcs):
    s=arcs[r['source']];axis=r['axis'];lam=f(r['lambda'])
    p,qv,sg=f(s['p']),f(s['q']),s['sign']
    if axis in (2,3):
        s=arcs[r['target']]
        p,qv,sg=-f(s['p']),-f(s['q']),-s['sign']
        axis=4 if axis==2 else 1
    X=p-lam if axis==4 else p
    Y=qv-lam*sg if axis==1 else qv
    return root(X*X+Y*Y)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[2])
    ap.add_argument('--chunk-size',type=int,default=4096)
    args=ap.parse_args();base=args.root/'research/eight'
    out=args.root/'SquaresInCircles/Eight/Generated/Affine'
    records=[]
    for src in sorted(base.glob('*HAND_DATA.json')):
        d=json.loads(src.read_text())
        if not isinstance(d,dict) or not isinstance(d.get('arcs'),list) or not isinstance(d.get('rows'),list):continue
        name=''.join(x.title() for x in src.stem.removesuffix('_HAND_DATA').lower().split('_'))
        dest=out/name;Q=f(d['Q']);arcs=d['arcs'];byid={a['id']:a for a in arcs}
        ns='SquaresInCircles.Eight.Generated.Affine.'+name
        lines=['module','',f'public import {ns}.Meta',
               'public import SquaresInCircles.Eight.Arithmetic.PreparedRow','',
               '/-! Complete endpoint formulas with exact rational brackets. Uncompiled. -/','',
               '@[expose] public section',f'namespace {ns}','open Arithmetic','',
               'def preparedArcs : List PreparedArc := [']
        for i,a in enumerate(arcs):
            rr=roots(a,Q)
            lines.append(f'  ⟨meta.arcs.getD {i} default,meta.radius,'+','.join(iv(x) for x in rr)+'⟩,')
        lines[-1]=lines[-1].removesuffix(',')+']'
        lines += ['',
            'def prepare (r : AffineTableRow) (normRoot : QInterval) : PreparedRow :=',
            '  ⟨r,preparedArcs.getD r.source default,preparedArcs.getD r.target default,',
            '    meta.charge r.edge,normRoot⟩','',
            f'end {ns}','']
        (dest/'Prepared.lean').write_text('\n'.join(lines))
        count=(len(d['rows'])+args.chunk_size-1)//args.chunk_size
        for k in range(count):
            chunk=d['rows'][k*args.chunk_size:(k+1)*args.chunk_size]
            tag=f'{k:03d}'
            lines=['module','',f'public import {ns}.Prepared',f'public import {ns}.Chunk{tag}','',
                '/-! Proof-producing original-row bindings. All proof scripts are uncompiled.',
                'The numeric proposition is evaluated inside ordinary Lean `decide`;',
                'no external success flag or report field is used as a premise. -/','',
                '@[expose] public section',f'namespace {ns}','open Arithmetic','',
                f'def normRoots{tag} : List QInterval := [']
            lines += ['  '+iv(norm_bracket(r,byid))+',' for r in chunk]
            lines[-1]=lines[-1].removesuffix(',')+']'
            lines += ['',f'def proofRow{tag} (i : Fin rows{tag}.length) : PreparedRow :=',
                f'  prepare (rows{tag}.get i) (normRoots{tag}.getD i.val ⟨0,0⟩)','',
                'set_option maxRecDepth 1000000 in',
                'set_option maxHeartbeats 0 in',
                f'theorem proofRows{tag}_numeric : ∀ i : Fin rows{tag}.length,',
                f'    (proofRow{tag} i).NumericValid ∧ (proofRow{tag} i).Matches meta ∧',
                f'    (rows{tag}.get i).Structural meta := by',
                '  decide','',
                f'theorem rows{tag}_claims : ∀ r ∈ rows{tag}, r.Claim meta := by',
                '  intro r hr',
                '  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr',
                f'  exact PreparedRow.claim (proofRows{tag}_numeric i).1 (proofRows{tag}_numeric i).2.1','',
                f'theorem rows{tag}_structural : ∀ r ∈ rows{tag}, r.Structural meta := by',
                '  intro r hr',
                '  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr',
                f'  exact (proofRows{tag}_numeric i).2.2','',
                f'end {ns}','']
            (dest/f'Proof{tag}.lean').write_text('\n'.join(lines))
        lines=['module','',f'public import SquaresInCircles.Eight.Generated.Affine.{name}']
        lines += [f'public import {ns}.Proof{k:03d}' for k in range(count)]
        lines += ['', '@[expose] public section',f'namespace {ns}','open Arithmetic','',
            '/-- Every supplied original row has the full continuous semantic Claim. -/',
            'theorem all_row_claims : ∀ r ∈ rows, r.Claim meta := by',
            '  intro r hr','  simp only [rows,List.mem_append] at hr',
            '  rcases hr with '+' | '.join(f'h{k}' for k in range(count))]
        lines += [f'  · exact rows{k:03d}_claims r h{k}' for k in range(count)]
        lines += ['', 'theorem all_rows_structural : ∀ r ∈ rows, r.Structural meta := by',
            '  intro r hr','  simp only [rows,List.mem_append] at hr',
            '  rcases hr with '+' | '.join(f'h{k}' for k in range(count))]
        lines += [f'  · exact rows{k:03d}_structural r h{k}' for k in range(count)]
        lines += ['',f'end {ns}','']
        (dest/'Claims.lean').write_text('\n'.join(lines))
        records.append({'module':name,'rows':len(d['rows']),'arcs':len(arcs),'proof_chunks':count})
        print(f'Generated {name}: {len(d["rows"])} row proof scripts',flush=True)
    (out.parent/'AffineClaims.lean').write_text('module\n\n'+'\n'.join(
        f'public import SquaresInCircles.Eight.Generated.Affine.{r["module"]}.Claims' for r in records)+'\n')
    (out/'proof_generation_index.json').write_text(json.dumps({'status':'complete-row-proof-scripts-uncompiled',
        'verification':'not run','tables':records},indent=2)+'\n')

if __name__=='__main__':main()
