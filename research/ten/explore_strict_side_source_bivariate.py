"""EXPLORATORY floating interval scan, not an exact certificate."""
from explore_strict_diagonal_interval import I,clamp,cross
import math,json,argparse
D=I(math.sqrt(2));K=2+D
TARGET=(.2637,.2639,.2413,.2416)
def test(x,y):
 try:
  p=2*x/(1+x*x);q=(1-x*x)/(1+x*x);r=2*y/(1+y*y);s=(1-y*y)/(1+y*y)
  if p.a>=q.b or r.a>=s.b:return 'steep'
  d=clamp((1-D*p-q*s+p*r)/q,-13/8,13/8)
  X=-1-r-q+p;Y=1+s+p+q
  den=Y-d*X/K
  if den.b<645/544:return 'denominator'
  den=I(max(den.a,645/544),den.b)
  S=clamp((K*X+d*Y+X*X+Y*Y)/den,1,21/8)
  u=clamp(K/2-d*S/(2*K),4/3,33/16);v=clamp(K-u,4/3,33/16)
  H=clamp((S+d)/2,.5,17/8);B=clamp((S-d)/2,.5,17/8)
  Rq=clamp(u.square()+H.square(),(79/40)**2,4.5)
  ell=(D-p-r)/q
  if ell.b<=0 or ell.a>1:return 'length'
  DA=u*q-H*p;DB=v*s-B*r
  NA=H*((u-1)*q-(H-1)*p);NB=B*((v-1)*s-(B-1)*r)
  if min(DA.b,DB.b,NA.b,NB.b)<=0:return 'positive'
  T=NA*DB-NB*DA
  if not T.contains0():return 'torque'
  w=[v+X,-B+Y];e=[q,-p];m=[p,q]
  if (w[0]*e[0]+w[1]*e[1]).a>=-.5 or (w[0]*m[0]+w[1]*m[1]).b<=.5:return 'circle_feature'
  gx=H*DB*p-B*DA*r;gy=H*DB*q+B*DA*s
  if not cross(w,[gx,gy]).contains0():return 'align'
  if x.a>=TARGET[0] and x.b<=TARGET[1] and y.a>=TARGET[2] and y.b<=TARGET[3]:return 'target'
  return None
 except ValueError:return 'domain'
def main():
 parser=argparse.ArgumentParser();parser.add_argument('--depth',type=int,default=32);parser.add_argument('--nodes',type=int,default=500000);args=parser.parse_args()
 stack=[(I(0,5/12),I(0,5/12),0)];counts={};pending=[];nodes=0
 while stack:
  x,y,depth=stack.pop();nodes+=1;reason=test(x,y)
  if reason:counts[reason]=counts.get(reason,0)+1;continue
  if depth>=args.depth or nodes>=args.nodes:pending.append((x.pair(),y.pair()));continue
  if x.b-x.a>=y.b-y.a:
   z=(x.a+x.b)/2;stack.extend([(I(z,x.b),y,depth+1),(I(x.a,z),y,depth+1)])
  else:
   z=(y.a+y.b)/2;stack.extend([(x,I(z,y.b),depth+1),(x,I(y.a,z),depth+1)])
 print(nodes,counts,'unresolved',len(pending))
 if pending:print('first',pending[:8]);print('hull',[[min(p[i][0] for p in pending),max(p[i][1] for p in pending)] for i in range(2)])
if __name__=='__main__':main()
