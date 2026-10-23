#!/usr/bin/env python3
"""Embed every fixed F7/F8 affine row and all semantic metadata in Lean.

This generator copies data and emits finite structural proof obligations.
It does not run a verifier, compile Lean, inspect axioms, or treat a PASS
field as a theorem. Continuous row/closed-domain proofs are separate modules.
"""
from pathlib import Path
from fractions import Fraction
import json
import argparse

def q(x):
    f=Fraction(str(x));return str(f.numerator) if f.denominator==1 else f'({f.numerator}/{f.denominator})'
def iv(v):return '⟨'+q(v[0])+','+q(v[1])+'⟩'
def vec(v):return '!['+', '.join(v)+']'
def axis(j):return ['.one','.two','.three','.four'][int(j)-1]

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[2]);ap.add_argument('--chunk-size',type=int,default=4096);args=ap.parse_args()
    base=args.root/'research/eight';out=args.root/'SquaresInCircles/Eight/Generated/Affine';out.mkdir(parents=True,exist_ok=True)
    records=[]
    for src in sorted(base.glob('*HAND_DATA.json')):
        d=json.loads(src.read_text())
        if not isinstance(d,dict) or not isinstance(d.get('arcs'),list) or not isinstance(d.get('rows'),list):continue
        name=''.join(x.title() for x in src.stem.removesuffix('_HAND_DATA').lower().split('_'))
        arcs=d['arcs'];indices={a['id']:i for i,a in enumerate(arcs)}
        dest=out/name;dest.mkdir(exist_ok=True)
        header=['module','','public import SquaresInCircles.Eight.Arithmetic.AffineTableData','','@[expose] public section','namespace SquaresInCircles.Eight.Generated.Affine.'+name,'open Arithmetic','']
        meta=header+['/-- Complete original arc data; schema eight-affine-v1. -/','def meta : AffineTableMeta :=','  { radius := '+q(d['Q']),'    arcs := [']
        for a in arcs:
            meta.append('      ⟨'+str(a['id'])+','+str(a['role'])+','+str(a['kind']=='O').lower()+','+str(a['sign']==1).lower()+','+iv([a['lo'],a['hi']])+',⟨'+','.join(q(a[k]) for k in ['c','p','q'])+'⟩⟩,')
        meta[-1]=meta[-1].removesuffix(',')+']'
        meta += ['    cuts := '+vec([iv(d.get('cuts',{}).get(str(i),[-1,1])) for i in range(7)]),
                 '    word := '+vec([str(x) for x in d.get('word',[0,1,0,1,0,1,1])]),
                 '    charge := '+vec([q(x) for x in d.get('beta',[0]*7)]),
                 '    target := '+vec([q(x) for x in d['gamma']]),
                 '    differenceRange := '+vec([iv(d.get('difference_ranges',{}).get(str(i),['-7/10','7/10'])) for i in range(7)]),
                 '    allowedAxes := '+vec(['['+','.join(axis(j) for j in d.get('axis_domains',{}).get(str(i),[1,2,3,4]))+']' for i in range(7)])+' }','',
                 f'theorem arc_count : meta.arcs.length = {len(arcs)} := by rfl','',
                 'end SquaresInCircles.Eight.Generated.Affine.'+name,'']
        (dest/'Meta.lean').write_text('\n'.join(meta))
        imports=[]
        for k in range((len(d['rows'])+args.chunk_size-1)//args.chunk_size):
            chunk=d['rows'][k*args.chunk_size:(k+1)*args.chunk_size];cn=f'Chunk{k:03d}'
            rows=['module','',f'public import SquaresInCircles.Eight.Generated.Affine.{name}.Meta','',
                  '/-! Raw complete row data. Structural proofs are not continuous row Claims.','Uncompiled draft; no external checker result is imported. -/','',
                  '@[expose] public section',f'namespace SquaresInCircles.Eight.Generated.Affine.{name}',
                  'open Arithmetic','',f'def rows{k:03d} : List AffineTableRow := [']
            for r in chunk:
                row=[str(r['edge']),str(indices[r['source']]),str(indices[r['target']]),axis(r['axis']),str(r['k']),str(r['r']==1).lower(),iv([r['lo'],r['hi']]),q(r['lambda']),'.'+r['mode'],q(r.get('h',1)),q(r.get('gamma',d['gamma'][r['edge']]))]
                rows.append('  ⟨'+','.join(row)+'⟩,')
            rows[-1]=rows[-1].removesuffix(',')+']'
            rows += ['',f'theorem rows{k:03d}_count : rows{k:03d}.length = {len(chunk)} := by rfl','',
                     f'end SquaresInCircles.Eight.Generated.Affine.{name}','']
            (dest/f'{cn}.lean').write_text('\n'.join(rows));imports.append(cn)
        idx=['module','']+[f'public import SquaresInCircles.Eight.Generated.Affine.{name}.{c}' for c in imports]+['',
             '@[expose] public section',f'namespace SquaresInCircles.Eight.Generated.Affine.{name}',
             'open Arithmetic','',
             'def rows : List AffineTableRow := '+ ' ++ '.join(f'rows{k:03d}' for k in range(len(imports))),
             f'theorem complete_row_count : rows.length = {len(d["rows"])} := by',
             '  simp only [rows,List.length_append,'+','.join(f'rows{k:03d}_count' for k in range(len(imports)))+']',
             '  norm_num','',f'end SquaresInCircles.Eight.Generated.Affine.{name}','']
        (out/f'{name}.lean').write_text('\n'.join(idx))
        records.append({'module':name,'source':src.name,'rows':len(d['rows']),'arcs':len(arcs),'chunks':len(imports)})
    (out.parent/'AffineData.lean').write_text('module\n\n'+'\n'.join(f'public import SquaresInCircles.Eight.Generated.Affine.{r["module"]}' for r in records)+'\n')
    (out/'generation_index.json').write_text(json.dumps({'schema':'eight-affine-v1','status':'raw-data-and-counts-uncompiled','tables':records},indent=2)+'\n')
    print(json.dumps({'tables':len(records),'rows':sum(r['rows'] for r in records),'arcs':sum(r['arcs'] for r in records),'chunks':sum(r['chunks'] for r in records),'verification':'not run'}))

if __name__=='__main__':main()
