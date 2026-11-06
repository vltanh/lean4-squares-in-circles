"""Negative controls for structure and arithmetic; deliberately bypass packet hash."""
import copy,json
from pathlib import Path
import check_leaf480 as C

def locate(t,tag):
 if t[0]==tag:return t
 kids=t[2:] if t[0]==1 else t[3] if t[0]==2 else []
 for child in kids:
  x=locate(child,tag)
  if x is not None:return x
 return None

def run():
 packet=C.read_packet();out={}
 def test(name,mutate,count=0):
  d=copy.deepcopy(packet);mutate(d)
  try:C.replay(d,0,count)
  except (ValueError,IndexError,TypeError) as e:out[name]=type(e).__name__+': '+str(e)
  else:raise RuntimeError('accepted damaged control: '+name)
 def first(d,tag):
  for root in d['roots']:
   x=locate(root,tag)
   if x is not None:return x
  raise RuntimeError('missing test node')
 test('missing_signed_root',lambda d:d['roots'].pop())
 test('missing_angle_child',lambda d:first(d,1).pop())
 test('invalid_angle_owner',lambda d:first(d,1).__setitem__(1,4))
 test('missing_SAT_child',lambda d:first(d,2)[3].pop())
 test('invalid_SAT_pair',lambda d:first(d,2).__setitem__(2,first(d,2)[1]))
 test('invalid_node_tag',lambda d:d['roots'][0].__setitem__(0,8))
 test('repeated_arithmetic_row',lambda d:first(d,0)[1].append(first(d,0)[1][0]))
 test('out_of_range_row',lambda d:first(d,0)[1].__setitem__(0,999999),1)
 test('negative_fallback_weight',lambda d:first(d,0).__setitem__(slice(None),[0,first(d,0)[1],None,['-1']*len(first(d,0)[1])]),1)
 test('zero_fallback_weight',lambda d:first(d,0).__setitem__(slice(None),[0,first(d,0)[1],None,['0']*len(first(d,0)[1])]),1)
 test('unrelated_common_axis',lambda d:first(d,3).__setitem__(1,[99,0]))
 test('repeated_chain_vertex',lambda d:first(d,3).__setitem__(2,[1,1,2]))
 report={'status':'PASS_12_REJECTED_MUTATIONS','hash_check_bypassed_for_structural_controls':True,'rejected':out}
 (Path(__file__).parent/'MUTATION_REPORT.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':run()
