"""Exact negative control for the weaker width-13/10 gap-capacity conjecture."""
from fractions import Fraction as F
from itertools import combinations,product
from pathlib import Path
import json
from exact_arcs import asin_bounds,atan_bounds,PI_LO,PI_HI
if not __debug__:
 raise RuntimeError('Run without -O: certificate comparisons use assertions.')
ROOT=Path(__file__).resolve().parent

def dot(x,y):return sum(a*b for a,b in zip(x,y))
def add(x,y):return tuple(a+b for a,b in zip(x,y))
def scale(s,x):return tuple(s*a for a in x)
def asin_signed(x):
 if x<0:
  lo,hi=asin_bounds(-x);return -hi,-lo
 return asin_bounds(x)
def interval_add(x,y):return x[0]+y[0],x[1]+y[1]
def interval_sub(x,y):return x[0]-y[1],x[1]-y[0]
def interval_scale(s,x):
 assert s>=0
 return s*x[0],s*x[1]

def check():
 data=json.loads((ROOT/'FOUR_CORE_GAP_COUNTEREXAMPLE.json').read_text())
 assert data['schema']=='four-core-gap-counterexample-v1'
 R0=F(data['core_radius']);R=F(data['circle_radius'])
 assert R0==F(41,40) and R==F(5,4)
 squares=[]
 for row in data['squares']:
  p=tuple(map(F,row['centre']));t=F(row['half_angle_tangent'])
  c=(1-t*t)/(1+t*t);s=2*t/(1+t*t);u=(c,s);v=(-s,c)
  assert dot(u,u)==dot(v,v)==1 and dot(u,v)==0
  assert dot(p,p)<R0*R0
  corners=[add(p,scale(F(1,2),add(scale(x,u),scale(y,v)))) for x,y in product((-1,1),repeat=2)]
  assert all(dot(z,z)<F(49013,10000) for z in corners)
  squares.append((p,t,u,v,corners))
 assert len(squares)==4
 for i,j in combinations(range(4),2):
  p,t,u,v,_=squares[i];q,tt,uu,vv,_=squares[j];d=add(q,scale(-1,p))
  def support(axis,a,b):return (abs(dot(axis,a))+abs(dot(axis,b)))/2
  assert any(abs(dot(axis,d))>support(axis,u,v)+support(axis,uu,vv) for axis in (u,v,uu,vv))
 # The two inner squares are strictly inside the test circle.
 for i in (0,1):assert all(dot(z,z)<R*R for z in squares[i][4])
 arcs=[]
 for i,quarter in ((2,1),(3,-1)):
  p,t,u,v,_=squares[i]
  # Rotate the square's coordinate frame by quarter*pi/2.
  eu=scale(quarter,v);ev=scale(-quarter,u)
  c,d=dot(p,eu),dot(p,ev)
  assert c>F(1,2) and c+F(1,2)>R
  low=d-F(1,2);high=d+F(1,2)
  assert -R<low<high<R
  assert R*R-low*low>(c-F(1,2))**2
  assert R*R-high*high>(c-F(1,2))**2
  assert 0<t<F(1,2)
  theta=interval_scale(F(2),atan_bounds(t))
  shift=(PI_LO/2,PI_HI/2) if quarter==1 else (-PI_HI/2,-PI_LO/2)
  theta=interval_add(theta,shift)
  arcs.append((interval_add(theta,asin_signed(low/R)),interval_add(theta,asin_signed(high/R))))
 top,bottom=arcs
 gap_small=interval_sub(top[0],bottom[1])
 gap_large=interval_sub(interval_add(bottom[0],(2*PI_LO,2*PI_HI)),top[1])
 assert gap_small[0]>F(193,100)
 assert gap_large[0]>F(13,5)
 assert gap_small[1]<F(2) and gap_large[1]<F(27,10)
 print('PASS: four strict disjoint cores; two exact gap bounds:',
       tuple(float(x) for x in gap_large),tuple(float(x) for x in gap_small))
 print('PASS: weaker pair-span13/10 capacities allow4+3=7; stronger27/20 excludes this example.')
if __name__=='__main__':check()
