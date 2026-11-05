"""Independent exact literal reconstruction; no discovery imports."""
from fractions import Fraction as F
PREFIX='physical_general_center_cone_'
def verify_literal(literal,angles):
 terms,rhs,label=literal
 assert label.startswith(PREFIX)
 fields=label[len(PREFIX):].split('_');assert len(fields)==7
 owner,axis,sign=map(int,fields[:3]);nx,ny,r,s=map(F,fields[3:])
 assert 0<=owner<9 and axis in(0,1)and sign in(-1,1)
 assert r>=s>=0 and(nx,ny)!=(0,0)
 assert len(angles)==9
 low,high=map(F,angles[owner]);assert -1<=low<=high<=1
 denominator=2*r+1;scale=(2*s+1)/denominator
 if axis==0:
  constant,linear=sign*nx,sign*ny
  cross_constant,cross_linear=ny,-nx
 else:
  constant,linear=sign*ny,-sign*nx
  cross_constant,cross_linear=nx,ny
 for endpoint in(low,high):
  major=constant+linear*endpoint
  cross=cross_constant+cross_linear*endpoint
  assert major>0
  assert scale*major-cross>=0 and scale*major+cross>=0
 support=(F(977,256)+r*r+s*s)/denominator
 expected=[]
 for index,value in[(2*owner,nx),(2*owner+1,ny),(18+owner,-support*constant),(27+owner,-support*linear)]:
  if value:expected.append((index,value))
 assert tuple(sorted(expected))==tuple(terms)and F(rhs)==0
 assert label==PREFIX+'_'.join(map(str,(owner,axis,sign,nx,ny,r,s)))
 return literal
