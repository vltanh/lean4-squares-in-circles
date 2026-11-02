#!/usr/bin/env python3
"""Damaged-certificate controls for the exact G-order replayer."""
import copy,gzip,json,hashlib
from pathlib import Path
from weak_outer_hand_G_order_verify import verify
HERE=Path(__file__).resolve().parent
CERT=HERE/'weak_outer_hand_G_order_certificate.json.gz'
DATA=json.load(gzip.open(CERT,'rt'))
def find(node,condition):
 if condition(node):return node
 for child in node.get('children',{}).values():
  found=find(child,condition)
  if found is not None:return found
 return None

def missing_root(d):d['roots'].pop()
def missing_angle_child(d):
 n=find(d['roots'][0],lambda n:n.get('kind')=='angle');assert n is not None;n['children'].pop('0')
def missing_separator_child(d):
 n=find(d['roots'][0],lambda n:n.get('kind')=='sep');assert n is not None;n['children'].pop(next(iter(n['children'])))
def false_whole_root(d):d['roots'][0]={'w':[]}
def negative_weight(d):
 n=find(d['roots'][0],lambda n:'w'in n);assert n is not None;n['w'][0][1]=-n['w'][0][1]

def main():
 reports=[]
 for name,damage in [('missing_orientation_root',missing_root),('missing_closed_angle_child',missing_angle_child),('missing_owned_separator_child',missing_separator_child),('false_whole_root_leaf',false_whole_root),('negative_multiplier',negative_weight)]:
  d=copy.deepcopy(DATA);damage(d)
  try:verify(d)
  except (AssertionError,ValueError,KeyError,TypeError) as exc:
   reports.append({'control':name,'status':'REJECTED','reason':str(exc)[:500]});print(name,'REJECTED',flush=True)
  else:raise AssertionError('Damaged certificate was accepted: '+name)
 report={'status':'PASS','controls':reports,'certificate_sha256':hashlib.sha256(CERT.read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256((HERE/'weak_outer_hand_G_order_verify.py').read_bytes()).hexdigest()}
 (HERE/'weak_outer_hand_G_order_rejection_controls.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
