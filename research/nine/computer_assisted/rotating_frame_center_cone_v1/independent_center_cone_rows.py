"""Independent exact row reconstruction. No producer or numerical imports."""
from fractions import Fraction as F
PREFIX='physical_rotating_frame_center_cone_'

def verify_literal(literal,angles):
 terms,rhs,name=literal
 assert name.startswith(PREFIX)
 fields=name[len(PREFIX):].split('_');assert len(fields)==5
 owner,axis,sign=map(int,fields[:3]);nx,ny=map(F,fields[3:])
 assert 0<=owner<9 and axis in (0,1) and sign in (-1,1) and (nx,ny)!=(0,0)
 assert len(angles)==9
 lower,upper=map(F,angles[owner]);assert -1<=lower<=upper<=1
 A,B=(sign*nx,sign*ny) if axis==0 else (sign*ny,-sign*nx)
 C,D=(ny,-nx) if axis==0 else (nx,ny)
 for z in (lower,upper):
  m=A+B*z;v=C+D*z
  assert m>0 and F(121)*abs(v)<=F(30)*m
 cap=(F(977,256)+F(8281,3600))*F(30,121)
 expected={2*owner:nx,2*owner+1:ny,18+owner:-cap*A,27+owner:-cap*B}
 expected=tuple((j,c)for j,c in sorted(expected.items())if c)
 assert tuple(terms)==expected and F(rhs)==0
 return expected,F(0),name
