"""Independent literal reconstruction of guarded oriented pair-cap rows.

The physical theorem is bound separately. This module checks its exact
original interval guards and expands the unnormalized support inequality
into the existing54-variable coordinates; it imports no producer code.
"""
from fractions import Fraction as Q
if not __debug__:raise RuntimeError('Exact literal reconstruction requires assertions')
def rows(angles,scalar,differences):
 angles=[tuple(Q(x)for x in v)for v in angles];scalar=[tuple(Q(x)for x in v)for v in scalar]
 assert len(angles)==9 and len(scalar)==36
 assert all(a<=b for a,b in angles+scalar)
 result=[];witnesses=[]
 for main in range(9):
  for other in range(9):
   if main==other:continue
   key=tuple(sorted((main,other)));raw=tuple(tuple(Q(x)for x in v)for v in differences[key])
   dx,dy=raw if main<other else tuple((-b,-a)for a,b in raw)
   reserve=Q(1)-max(abs(dx[0]),abs(dx[1]))
   if reserve<=0:continue
   assert dx[0]<=dx[1]and dy[0]<=dy[1]
   allowed_angles=[]
   if min(angles[main][0],Q(0))==0 or min(scalar[main+9][0],Q(0))==0:allowed_angles.append(1)
   if max(angles[main][1],Q(0))==0 or max(scalar[main+9][1],Q(0))==0:allowed_angles.append(-1)
   allowed_sides=[]
   if dy[0]>=0:allowed_sides.append(1)
   if dy[1]<=0:allowed_sides.append(-1)
   for angle_sign in allowed_angles:
    for side in allowed_sides:
     sign=angle_sign*side
     # Start from a(sigma*x_M-h_M)+b(sigma*x_B-h_B)
     # +(a-k/2)|beta_M|-(a+b)(1-alpha_M)<=K.
     a=Q(46);b=Q(27,2);k=Q(207,16);cap=Q(211,4)
     co={}
     def add(index,value):co[index]=co.get(index,Q(0))+value
     for original,weight in((main,a),(other,b)):
      add(2*original,weight*sign)
      add(18+original,-weight/2)
      add(36+original,-weight/2)
     add(18+main,a+b);add(36+main,a-k/2)
     rhs=cap+a+b
     name=f'oriented_good_pair_cap_{main}_{other}_{angle_sign}_{side}'
     result.append((tuple(sorted((i,x)for i,x in co.items()if x)),rhs,name))
     witnesses.append(dict(name=name,main=main,other=other,angle_sign=angle_sign,vertical_side=side,
      horizontal_load_sign=sign,main_angle_interval=list(map(str,angles[main])),
      main_signed_beta_interval=list(map(str,scalar[main+9])),dx=list(map(str,dx)),dy=list(map(str,dy)),
      strict_horizontal_reserve=str(reserve)))
 return result,witnesses

def check(produced,guards,angles,scalar,differences):
 expected,witnesses=rows(angles,scalar,differences)
 assert produced==expected and guards==witnesses
 return dict(status='PASS_EXACT_ORIENTED_CAP_ROW_RECONSTRUCTION',rows=len(expected))
