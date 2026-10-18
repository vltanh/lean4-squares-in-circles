#!/usr/bin/env python3
"""Exact solver-independent replay for every 4+4 reference certificate root.

No numpy/scipy/LP/inexact comparisons; uses only Fraction, gzip, JSON.
Every root is reconstructed from public geometry, with all mixed choices,
order symmetries and center-bound residual forces retained.
"""
from __future__ import annotations
import argparse,gzip,json
from pathlib import Path
from m5_fourfour_exact_model import (RationalModel,REPS,BOUND,
    exact_leaf_margin,check_constants)

class ProofError(ValueError):pass


def replay_one(obj,k):
 if set(obj)!= {'root','pi','sigma','tree'} or obj['root']!=k:
  raise ProofError('Wrong root object')
 if tuple(obj['pi'])!=REPS[k][0] or tuple(obj['sigma'])!=REPS[k][1]:
  raise ProofError('Unlisted or mismatched symmetry root')
 m=RationalModel(*REPS[k]);stats={'nodes':0,'branches':0,'leaves':0,'max_depth':0}
 def walk(node,used,selected,depth=0):
  stats['nodes']+=1;stats['max_depth']=max(depth,stats['max_depth'])
  if type(node) is not list or not node:raise ProofError('Invalid node')
  if node[0]==0:
   if len(node)!=2 or type(node[1]) is not list or not node[1]:
    raise ProofError('Invalid leaf')
   witnesses=[]
   for pair in node[1]:
    if type(pair) is not list or len(pair)!=2:
     raise ProofError('Invalid row/weight pair')
    row_id,wt=pair
    if type(row_id) is not int or not (0<=row_id<len(m.rows)):
     raise ProofError('Row out of range')
    if row_id>=m.base and row_id not in selected:
     raise ProofError('Leaf used unselected SAT or cone row')
    if type(wt) is not int or wt<=0:
     raise ProofError('Bad multiplier')
    witnesses.append((row_id,wt))
   if exact_leaf_margin(m,witnesses)>=0:
    raise ProofError('No strict rational contradiction')
   stats['leaves']+=1;return
  if node[0]!=1 or len(node)!=3 or type(node[1]) is not int:
   raise ProofError('Invalid branch')
  pair=node[1]
  if not(0<=pair<16) or pair in used:
   raise ProofError('Invalid or repeated mixed pair')
  if type(node[2]) is not list or len(node[2])!=8:
   raise ProofError('Missing signed SAT alternative')
  stats['branches']+=1
  for child,bundle in zip(node[2],m.bundles[pair]):
   walk(child, used|{pair}, selected|set(bundle), depth+1)
 walk(obj['tree'],set(),set())
 if stats['nodes']!=stats['leaves']+stats['branches']:
  raise ProofError('Node accounting mismatch')
 return stats


def main():
 parser=argparse.ArgumentParser();parser.add_argument('--directory',type=Path,default=Path('proofs'))
 parser.add_argument('--start',type=int,default=0);parser.add_argument('--end',type=int,default=len(REPS))
 args=parser.parse_args();check_constants()
 if not(0<=args.start<=args.end<=len(REPS)):raise ValueError('Invalid root range')
 overall=dict(nodes=0,branches=0,leaves=0,max_depth=0)
 for k in range(args.start,args.end):
  path=args.directory/f'root_{k:02d}.json.gz'
  if not path.is_file():raise ProofError(f'Missing root {k}')
  obj=json.loads(gzip.decompress(path.read_bytes()))
  stats=replay_one(obj,k)
  for key in ('nodes','branches','leaves'):overall[key]+=stats[key]
  overall['max_depth']=max(overall['max_depth'],stats['max_depth'])
  print('Verified',f'{k:02d}',stats,flush=True)
 print('EXACT CERTIFICATE REPLAY PASSED for root range',args.start,args.end,overall,flush=True)
 if args.start==0 and args.end==len(REPS):
  print('All 66 D4 roots cover 484 allowed order pairs; 4+4 fixed-frame q<=Rbar^2 excluded.',flush=True)
 else:
  print('PARTIAL ROOT RANGE ONLY; no whole 4+4 theorem.',flush=True)

if __name__=='__main__':main()
