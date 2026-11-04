"""Independent exact rational replay of the two-link scalar certificate.
Reconstructs physical trigonometric numerators separately; no discovery import.
"""
from fractions import Fraction as Q
from itertools import product
from math import comb
from pathlib import Path
from hashlib import sha256
import json,time,argparse,sys
if not __debug__:raise RuntimeError('Assertions are required')
Z=(0,0,0);INDICES=list(product(range(5),repeat=3));SCALE=736000

def plus(*polys):
 result={}
 for p in polys:
  for key,value in p.items():result[key]=result.get(key,Q(0))+value
 return {key:value for key,value in result.items()if value}
def times(p,q):
 result={}
 for a,x in p.items():
  for b,y in q.items():
   key=tuple(u+v for u,v in zip(a,b));assert max(key)<=4
   result[key]=result.get(key,Q(0))+x*y
 return {key:value for key,value in result.items()if value}
def multiple(p,c):return {k:v*c for k,v in p.items()if v*c}
def coordinate(axis,power=1):
 key=[0,0,0];key[axis]=power;return {tuple(key):Q(1)}
ONE={Z:Q(1)}
def product_poly(ps):
 result=ONE
 for p in ps:result=times(result,p)
 return result

def reconstruct(signs,owners,k):
 squares=[coordinate(i,2)for i in range(3)]
 denominators=[plus(ONE,s)for s in squares]
 cosine_numerators=[plus(ONE,multiple(s,-1))for s in squares]
 sine_numerators=[multiple(coordinate(i),2*signs[i])for i in range(3)]
 factors=[times(a,b)for a,b in zip(denominators,cosine_numerators)]
 common=product_poly(factors)
 base=multiple(common,-2*SCALE);sines=[]
 for edge,owner in enumerate(owners):
  i,j=edge,edge+1;other=j if owner==i else i
  # (1+cos(theta_i-theta_j))/(2 alpha_owner), with cos expanded by dot product.
  cosnum=plus(times(denominators[i],denominators[j]),
              times(cosine_numerators[i],cosine_numerators[j]),
              times(sine_numerators[i],sine_numerators[j]))
  sinnum=plus(times(sine_numerators[i],cosine_numerators[j]),
              multiple(times(cosine_numerators[i],sine_numerators[j]),-1))
  quotient=product_poly([denominators[owner],cosine_numerators[other]]+
                        [factors[r]for r in range(3)if r not in(i,j)])
  base=plus(base,multiple(times(cosnum,quotient),Q(SCALE,2)))
  sines.append(multiple(times(sinnum,quotient),Q(SCALE,2)))
 # Good endpoint toll, its negative halfwidth, and the actual-link inner halfwidth.
 for axis,num in ((0,plus(multiple(coordinate(0),Q(55,32)),multiple(squares[0],-Q(119,46)),
                          multiple(cosine_numerators[0],-Q(1,2)),multiple(coordinate(0),-1))),
                  (2,plus(multiple(cosine_numerators[2],Q(1,2)),coordinate(2)))):
  quotient=product_poly([cosine_numerators[axis]]+[factors[r]for r in range(3)if r!=axis])
  base=plus(base,multiple(times(num,quotient),SCALE))
 quotient=product_poly([denominators[k]]+[factors[r]for r in range(3)if r!=k])
 base=plus(base,multiple(times(coordinate(k),quotient),-Q(601,500)*SCALE))
 return [base]+sines

def bernstein(poly,box):
 a=[poly.get(key,Q(0))for key in INDICES]
 for axis,(lo,hi)in enumerate(box):
  width=hi-lo
  matrix=[[sum(Q(comb(power,m)*comb(index,m),comb(4,m))*lo**(power-m)*width**m
                   for m in range(min(power,index)+1))for power in range(5)]for index in range(5)]
  stride=5**(2-axis);answer=[]
  for index in range(125):
   digit=(index//stride)%5;first=index-digit*stride
   answer.append(sum(matrix[digit][r]*a[first+r*stride]for r in range(5)))
  a=answer
 return a

def check_file(path,expected):
 record=json.loads(path.read_text());signs,owners,k=expected
 assert record['schema']=='exact_actual_edge_three_angle_bernstein_cover_v1'
 assert record['signs']==signs and record['owners']==owners and record['selected_owner']==k
 assert record['root_upper']=='5/12'and record['coefficient']=='601/1000'and record['target_variation']=='3/5'
 assert record['scale']==SCALE and record['frontier']==[]
 polynomials=reconstruct(signs,owners,k);trie={};positive_min=None;count=0;maxdepth=0
 for leaf in record['leaves']:
  node=trie;box=[(Q(0),Q(5,12))]*3;addresses=[(0,0)]*3
  for axis,side in leaf['path']:
   assert type(axis)is int and type(side)is int and axis in(0,1,2)and side in(0,1)
   assert 'leaf'not in node
   if 'axis'in node:assert node['axis']==axis
   else:node['axis']=axis
   node=node.setdefault(side,{})
   lo,hi=box[axis];mid=(lo+hi)/2;box[axis]=(lo,mid)if side==0 else(mid,hi)
   n,d=addresses[axis];addresses[axis]=(2*n+side,d+1)
  assert node=={};node['leaf']=True
  assert leaf['weight_denominator']==8
  w=leaf['weights'];assert len(w)==2 and all(type(v)is int and -8<=v<=8 for v in w)
  p=plus(multiple(polynomials[0],8),multiple(polynomials[1],w[0]),multiple(polynomials[2],w[1]))
  coefficients=bernstein(p,box);origin=all(lo==0 for lo,hi in box)
  assert leaf['origin_leaf']==origin
  if origin:assert coefficients[0]==0 and all(v>0 for v in coefficients[1:])
  else:assert all(v>0 for v in coefficients)
  multiplier=1
  for n,d in addresses:multiplier*=12*(12*(1<<d))**4
  integers=[v*multiplier for v in coefficients];assert all(v.denominator==1 for v in integers)
  assert int(min(integers))==int(leaf['coefficient_min'])
  active=integers[1:]if origin else integers
  assert int(min(active))==int(leaf['positive_coefficient_min'])
  value=min(coefficients[1:]if origin else coefficients)
  positive_min=value if positive_min is None else min(positive_min,value)
  count+=len(coefficients);maxdepth=max(maxdepth,len(leaf['path']))
 def complete(node):
  if 'leaf'in node:assert node=={'leaf':True};return 1
  assert set(node)=={'axis',0,1}
  return 1+complete(node[0])+complete(node[1])
 nodes=complete(trie);assert nodes==record['nodes']and maxdepth==record['maxdepth']
 return dict(file=path.name,sha256=sha256(path.read_bytes()).hexdigest(),signs=signs,owners=owners,
             selected_owner=k,leaves=len(record['leaves']),nodes=nodes,maxdepth=maxdepth,
             bernstein_coefficients=count,minimum_positive_rational_coefficient=str(positive_min),
             scalar_strict_except_all_zero=True)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('folder',type=Path);ap.add_argument('report',type=Path)
 a=ap.parse_args();start=time.monotonic();manifest=json.loads((a.folder/'MANIFEST.json').read_text());audits=[];expected_files=set()
 assert manifest['open']==0 and manifest['coefficient']=='601/1000'and manifest['target_variation']=='3/5'
 for u,v in product((-1,1),repeat=2):
  signs=[1,u,v]
  for t,s in product((0,1),repeat=2):
   owners=[t,1+s]
   for k in sorted(set(owners)):
    name='s'+''.join('p'if x>0 else'm'for x in signs)+'_o'+''.join(map(str,owners))+'_k'+str(k)+'.json'
    expected_files.add(name);audits.append(check_file(a.folder/name,(signs,owners,k)))
 assert len(audits)==28 and {d['file']for d in manifest['domains']}==expected_files
 assert len(manifest['domains'])==28
 assert manifest['leaves']==sum(e['leaves']for e in audits)
 for e in manifest['domains']:
  audit=next(x for x in audits if x['file']==e['file'])
  for k in('signs','owners','selected_owner','nodes','maxdepth','leaves'):assert e[k]==audit[k]
  assert e['open']==0
 assert not any(n in sys.modules for n in ('numpy','scipy','exact_three_angle_cover','exact_three_angle_cover_0601'))
 report=dict(status='PASS_COMPLETE_EXACT_TWO_LINK_SCALAR_COVER',domains=28,leaves=sum(x['leaves']for x in audits),
             bernstein_coefficients=sum(x['bernstein_coefficients']for x in audits),frontier=0,
             coefficient='601/1000',target_variation='3/5',strict_except_all_zero=True,
             physical_lifting_separately_required=True,new_original_cells=0,new_masks=0,audits=audits,
             checker_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-start)
 a.report.write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:v for k,v in report.items()if k not in('audits',)}),flush=True)
if __name__=='__main__':main()
