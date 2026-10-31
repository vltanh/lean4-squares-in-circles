"""Exploratory floating interval pruning, NOT an exact certificate."""
import math,argparse,json
class I:
 def __init__(self,a,b=None):self.a=float(a);self.b=float(a if b is None else b)
 def __add__(x,y):
  if not isinstance(y,I):y=I(y)
  return I(x.a+y.a,x.b+y.b)
 __radd__=__add__
 def __neg__(x):return I(-x.b,-x.a)
 def __sub__(x,y):return x+-I(y) if not isinstance(y,I) else x+-y
 def __rsub__(x,y):return I(y)+-x
 def __mul__(x,y):
  if not isinstance(y,I):y=I(y)
  v=[x.a*y.a,x.a*y.b,x.b*y.a,x.b*y.b];return I(min(v),max(v))
 __rmul__=__mul__
 def __truediv__(x,y):
  if not isinstance(y,I):y=I(y)
  if y.a<=0:raise ValueError('nonpositive')
  return x*I(1/y.b,1/y.a)
 def sqrt(x):
  if x.b<0:raise ValueError('negative')
  return I(math.sqrt(max(0,x.a)),math.sqrt(max(0,x.b)))
 def square(x):return I(0 if x.a<=0<=x.b else min(x.a*x.a,x.b*x.b),max(x.a*x.a,x.b*x.b))
 def contains0(x):return x.a<=0<=x.b
 def pair(x):return [x.a,x.b]
def add(a,b):return [a[i]+b[i] for i in range(2)]
def sub(a,b):return [a[i]-b[i] for i in range(2)]
def sq(a):return a[0].square()+a[1].square()
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def clamp(a,lo,hi):
 if a.b<lo or a.a>hi:raise ValueError('empty clamp')
 return I(max(lo,a.a),min(hi,a.b))
K=I(2+math.sqrt(2))
def evaluate(box,kind):
 q,f,g=box
 try:
  M=(q-I(.25)).sqrt();u=K-M+f*(M-K/2);v=K-u
  HA=clamp(q-u.square(),.25,5).sqrt();HB=clamp(q-v.square(),.25,5).sqrt()
  zlo=I(max(0,HA.a-1),max(0,HA.b-1));zhi=HB
  span=zhi-zlo
  if span.b<=0:return 'height',None
  span=I(max(0,span.a),span.b);z=zlo+g*span
  if z.a>=HB.b or z.b<=HA.a-1:return 'strictheight',None
  normals=[];dens=[]
  for r,H in [(u,HA),(v,HB)]:
   N=r*z-H*(r-1);D=H*(1-H+z)
   if N.b<=0 or D.b<=0 or (N-D).a>=0:return 'direction',None
   if D.a>0:t=clamp(N/D,0,1)
   else:t=I(0,1)
   vertical=I(1)/(1+t.square()).sqrt();horizontal=t*vertical
   normals.append((horizontal,vertical));den=r-H*t
   if den.b<=0:return 'force',None
   dens.append((t,I(max(0,den.a),den.b)))
  (p,a),(r,b)=normals;(ta,da),(tb,db)=dens
  QA=[1-u+p,1-HA+a];QB=[v-1-r,1-HB+b];delta=sub(QB,QA);dx,dy=delta
  if dx.b<=0:return 'orientation',None
  gv=[HA*db*ta-HB*da*tb,HA*db+HB*da]
  if kind=='EA':
   E=p*dx+a*dy
   if not E.contains0() or (dx-a).a>0:return 'contact',None
   e=[a,-p];m=[p,a];left=sub(QB,e)
  elif kind=='EB':
   E=-r*dx+b*dy
   if not E.contains0() or (dx-b).a>0:return 'contact',None
   e=[b,r];m=[-r,b];left=QA
  else:
   E=sq(delta)-1
   if not E.contains0() or (p*dx+a*dy).b<=0 or (-r*dx+b*dy).a>=0:return 'contact',None
   e=delta;m=[-dy,dx];left=QA
  ul=add(left,m);ur=add(ul,e)
  if any((sq(P)-q).a>0 for P in [left,add(left,e),ul,ur]):return 'contain',None
  if kind=='EA':w=ul
  elif kind=='EB':w=ur
  elif kind=='VVL':w=ul
  elif kind=='VVR':w=ur
  else:
   if not (sq(ul)-q).contains0() or not (sq(ur)-q).contains0():return 'radial',None
   return None,dict(A=[.5-u,.5-HA],B=[v-.5,.5-HB],C=add(left,[(e[i]+m[i])/2 for i in range(2)]),D=[(v-u)/2,-z])
  if not (sq(w)-q).contains0():return 'circle',None
  if not cross(w,gv).contains0():return 'align',None
  return None,dict(A=[.5-u,.5-HA],B=[v-.5,.5-HB],C=add(left,[(e[i]+m[i])/2 for i in range(2)]),D=[(v-u)/2,-z])
 except ValueError as ex:
  if str(ex) in ['empty clamp','negative']:return 'domain',None
  return None,None

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--depth',type=int,default=22);parser.add_argument('--max-nodes',type=int,default=300000);parser.add_argument('--output');args=parser.parse_args()
 output=[]
 for kind in ['EA','EB','VVL','VVR','VVRAD']:
  stack=[([I((79/40)**2,4.5),I(0,1),I(0,1)],0)];counts={};unresolved=[];n=0
  while stack:
   box,depth=stack.pop();n+=1;reason,centers=evaluate(box,kind)
   if reason:counts[reason]=counts.get(reason,0)+1;continue
   if depth>=args.depth or n>=args.max_nodes:
    unresolved.append([x.pair() for x in box]);continue
   widths=[(x.b-x.a)/(0.6 if i==0 else 1) for i,x in enumerate(box)];j=max(range(3),key=lambda i:widths[i]);mid=(box[j].a+box[j].b)/2
   lo=box.copy();hi=box.copy();lo[j]=I(box[j].a,mid);hi[j]=I(mid,box[j].b);stack.extend([(hi,depth+1),(lo,depth+1)])
  print(kind,n,counts,'unresolved',len(unresolved),flush=True)
  if unresolved:print('hull',[[min(b[i][0] for b in unresolved),max(b[i][1] for b in unresolved)] for i in range(3)],flush=True)
  output.append(dict(kind=kind,nodes=n,rejections=counts,unresolved=unresolved))
 if args.output:open(args.output,'w').write(json.dumps(dict(status='EXPLORATORY_FLOAT_INTERVALS_NOT_PROOF',results=output),indent=2)+'\n')
if __name__=='__main__':main()
