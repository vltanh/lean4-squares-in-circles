#!/usr/bin/env python3
"""Deliberate corruptions of the exact rational 4+4 proof replay."""
from copy import deepcopy
from pathlib import Path
import gzip,json
from verify_m5_fourfour_certificate import replay_one,ProofError


def reject(desc,obj):
 try:replay_one(obj,0)
 except (ProofError,ValueError,IndexError,TypeError):
  print('Rejected:',desc)
  return
 raise AssertionError('Unsafe mutation accepted: '+desc)


def first_leaf(node):
 if node[0]==0:return node
 for child in node[2]:
  r=first_leaf(child)
  if r:return r


def first_branch(node):
 if node[0]==1:return node
 raise AssertionError('Expected a branching root')


def main():
 path=Path(__file__).resolve().parents[2]/'proofs/root_00.json.gz'
 obj=json.loads(gzip.decompress(path.read_bytes()))
 replay_one(obj,0)
 altered=deepcopy(obj);altered['pi'][0]=99
 reject('invalid root permutation',altered)
 altered=deepcopy(obj);altered['tree'][2].pop()
 reject('omitted signed SAT alternative',altered)
 altered=deepcopy(obj);first_leaf(altered['tree'])[1][0][1]=0
 reject('zeroed contradiction multiplier',altered)
 altered=deepcopy(obj);first_leaf(altered['tree'])[1].append([1443,1])
 reject('unselected mixed-pair row',altered)
 altered=deepcopy(obj);altered['tree'][1]=16
 reject('out-of-range mixed pair',altered)
 print('All five deliberate proof-data mutations rejected.')

if __name__=='__main__':main()
