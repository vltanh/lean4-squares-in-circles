"""Exact necessary affine oriented-cap rows from existing original intervals.

Physical input: ORIENTED_GOOD_ENDPOINT_TILT_TOLL_HAND_PROOF.md.
No four-row or height-variation hypothesis is used by these pair rows.
Variable convention is the existing54-variable original model:
  0:18 center coordinates;18:27 alpha;27:36 signed beta;
  36:45 absolute beta;45:54 original insets.
"""
from fractions import Fraction as F
from itertools import permutations
if not __debug__:raise RuntimeError('Exact oriented-cap guards require assertions')
def directed(ds,i,j):
 if i<j:return ds[i,j]
 return tuple((-hi,-lo)for lo,hi in ds[j,i])
def rows(angles,scalar,differences):
 angles=tuple(tuple(map(F,v))for v in angles);scalar=tuple(tuple(map(F,v))for v in scalar)
 assert len(angles)==9 and len(scalar)==36
 assert all(lo<=hi for lo,hi in angles+scalar)
 out=[];guards=[]
 for m,b in permutations(range(9),2):
  dx,dy=directed(differences,m,b)
  if not(-1<dx[0]<=dx[1]<1):continue
  sides=[]
  if dy[0]>=0:sides.append(1)
  if dy[1]<=0:sides.append(-1)
  signs=[]
  if angles[m][0]>=0 or scalar[9+m][0]>=0:signs.append(1)
  if angles[m][1]<=0 or scalar[9+m][1]<=0:signs.append(-1)
  for eta in signs:
   for delta in sides:
    sigma=eta*delta
    co={2*m:46*sigma,2*b:F(27,2)*sigma,18+m:F(73,2),36+m:F(529,32),18+b:F(-27,4),36+b:F(-27,4)}
    name=f'oriented_good_pair_cap_{m}_{b}_{eta}_{delta}'
    out.append((tuple(sorted((k,F(v))for k,v in co.items()if v)),F(449,4),name))
    guards.append(dict(name=name,main=m,other=b,angle_sign=eta,vertical_side=delta,horizontal_load_sign=sigma,
      main_angle_interval=list(map(str,angles[m])),main_signed_beta_interval=list(map(str,scalar[9+m])),
      dx=list(map(str,dx)),dy=list(map(str,dy)),strict_horizontal_reserve=str(1-max(abs(dx[0]),abs(dx[1])))))
 return out,guards
