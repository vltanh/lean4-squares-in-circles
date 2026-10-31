#!/usr/bin/env python3
"""Exact outward-integer cover of the two original radial-M root rows.
The equations and complete domain are in
S123_POSITIVE_CHANNEL_RADIAL_MIDDLE_COMPLETE_EXCLUSION.md.
No floating-point arithmetic, numerical root, or input data is used.
"""
from collections import Counter
S=1<<40
def lo(p,q=S):return p//q
def hi(p,q=S):return -((-p)//q)
def pt(p,q=1):return (lo(p*S,q),hi(p*S,q))
def add(a,b):return(a[0]+b[0],a[1]+b[1])
def neg(a):return(-a[1],-a[0])
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 p=(a[0]*b[0],a[0]*b[1],a[1]*b[0],a[1]*b[1])
 return(lo(min(p)),hi(max(p)))
def div(a,b):
 assert b[0]>0
 return mul(a,(lo(S*S,b[1]),hi(S*S,b[0])))
def sq(a):
 if a[0]>=0:return(lo(a[0]*a[0]),hi(a[1]*a[1]))
 if a[1]<=0:return(lo(a[1]*a[1]),hi(a[0]*a[0]))
 return(0,hi(max(a[0]*a[0],a[1]*a[1])))
one=pt(1);two=pt(2);four=pt(4);half=pt(1,2);quarter=pt(1,4)
def vals(z,T,kind):
 z2=sq(z);den=add(one,z2)
 # Exact monotonic rational endpoints on 0<=z<=2/13.
 zl,zh=z
 x=(lo((S*S-zh*zh)*S,S*S+zh*zh),hi((S*S-zl*zl)*S,S*S+zl*zl))
 t=(lo(2*zl*S*S,S*S+zl*zl),hi(2*zh*S*S,S*S+zh*zh))
 if kind=='tilted':
  eps=add(mul(z,T),mul(quarter,mul(den,sq(T))))
  V=add(T,mul(half,mul(z,sq(T))))
  r=sub(mul(quarter,mul(sub(one,z2),sq(T))),mul(z,T))
  XA=sub(one,r)
 else:
  V=T;eps=mul(z,V);r=neg(eps);XA=add(one,eps)
 d=add(one,eps);D=add(mul(four,sq(d)),one)
 a=div(mul(four,d),D);b=div(sub(mul(four,sq(d)),one),D)
 qn=sub(d,a);qf=add(half,b)
 u=add(mul(x,qn),mul(t,qf));y=add(neg(mul(t,qn)),mul(x,qf));W=sub(one,u);HB=sub(two,V)
 eq1=sub(add(sq(W),sq(HB)),add(sq(add(d,one)),quarter))
 if kind=='tilted':
  eq2=sub(mul(mul(XA,T),HB),mul(mul(y,W),add(t,T)))
 else: eq2=sub(mul(V,HB),mul(mul(y,W),t))
 return eps,V,t,r,W,y,eq1,eq2
def check(box,kind):
 eps,V,t,r,W,y,f,g=vals(*box,kind)
 # Discard only necessary false original guards/equalities.
 guards=[sub(pt(1,60),eps),sub(V,pt(1,50)),sub(pt(13,50),V),sub(W,half),sub(one,W),sub(y,sub(one,V)),sub(sub(two,V),y)]
 for i,v in enumerate(guards):
  if v[1]<0:return('empty'+str(i),None)
 if f[0]>0 or f[1]<0:return('circle',None)
 if g[0]>0 or g[1]<0:return('mean',None)
 gaps=[sub(V,pt(1,25)),sub(pt(3,50),V),sub(t,pt(2,25)),sub(pt(13,100),t),sub(pt(7,2000),eps)]
 m=min(v[0] for v in gaps)
 if m>0:return('pass',m)
 return None
def run(kind):
 root=((0,pt(2,13)[1]),(0,pt(13,50)[1]))
 stack=[(root,0)];count=Counter();vis=depth=0;mn=S
 while stack:
  box,dep=stack.pop();vis+=1;out=check(box,kind)
  if out:
   k,m=out;count[k]+=1;depth=max(depth,dep)
   if m is not None:mn=min(mn,m)
   continue
  assert dep<60, (kind,box,vals(*box,kind))
  # Compare normalized widths; all endpoints remain exact integers.
  widths=[(box[0][1]-box[0][0])*169,(box[1][1]-box[1][0])*100]
  j=max(range(2),key=lambda k:widths[k]);l,h=box[j];mid=(l+h)//2
  assert l<mid<h
  A=list(box);B=list(box);A[j]=(l,mid);B[j]=(mid,h)
  stack.append((tuple(B),dep+1));stack.append((tuple(A),dep+1));count['split']+=1
 expected = {'tilted': (Counter({'split':64,'circle':38,'mean':24,'pass':3}),129,16,12280343), 'aligned': (Counter({'split':39,'circle':23,'mean':14,'pass':3}),79,12,498216206)}[kind]
 assert (count,vis,depth,mn)==expected
 assert mn>0
 print('PASS',kind,dict(count),'visited',vis,'depth',depth,'margin',mn,'den',S)
 return count,vis,depth,mn
if __name__=='__main__':
 run('tilted');run('aligned')

