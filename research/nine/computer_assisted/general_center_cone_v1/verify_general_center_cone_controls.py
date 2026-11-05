"""Finite literal/guard rejection controls for generalized center cones."""
from pathlib import Path
from fractions import Fraction as F
import json,sys,hashlib
import physical_general_center_cone_rows as P
import independent_general_center_cone_rows as V
HERE=Path(__file__).resolve().parent

def reject(name,callback):
 try:callback()
 except (AssertionError,ValueError,ZeroDivisionError,IndexError):return name
 raise AssertionError(('damaged literal accepted',name))

def main():
 assert __debug__
 count=0;identities=0;negatives=[]
 for r,s in P.PARAMETERS:
  a,b=2*r+1,2*s+1;k=b/a;c=(F(977,256)+r*r+s*s)/a
  lhs={(2,0):F(1),(0,2):F(1),(1,0):1-a,(0,1):1-b,(0,0):r*r+s*s}
  expanded={(2,0):F(1),(0,2):F(1),(1,0):-2*r,(0,1):-2*s,(0,0):r*r+s*s}
  assert lhs==expanded and a*c-r*r-s*s==F(977,256)and k*a==b;identities+=1
 for interval in[(-F(1),F(1)),(F(0),F(0)),(-F(1,8),F(1,8)),(F(1,16),F(5,8)),(-F(5,8),-F(1,16))]:
  angles=[interval]*9
  for literal in P.generate(angles):V.verify_literal(literal,angles);count+=1
 for r,s in P.PARAMETERS:
  k=(2*s+1)/(2*r+1);angles=[(-k,k)]*9
  for owner in range(9):
   for axis,sign,nx,ny in[(0,1,1,0),(0,-1,-1,0),(1,1,0,1),(1,-1,0,-1)]:
    literal=P.row(angles,owner,axis,sign,nx,ny,r,s);V.verify_literal(literal,angles);count+=1
  if k<1:
   literal=P.row(angles,0,0,1,1,0,r,s)
   for side in(0,1):
    damaged=list(angles);damaged[0]=(-k-F(1,4096),k)if side==0 else(-k,k+F(1,4096))
    negatives.append(reject('guard_endpoint_'+str(r)+'_'+str(s)+'_'+str(side),lambda:V.verify_literal(literal,damaged)))
 angles=[(-F(1),F(1))]*9;literal=P.row(angles,0,0,1,1,0,F(31,32),F(31,32));terms,rhs,label=literal
 negatives.append(reject('changed_rhs',lambda:V.verify_literal((terms,rhs+1,label),angles)))
 negatives.append(reject('changed_coefficient',lambda:V.verify_literal((((terms[0][0],terms[0][1]+1),)+terms[1:],rhs,label),angles)))
 negatives.append(reject('missing_coefficient',lambda:V.verify_literal((terms[:-1],rhs,label),angles)))
 negatives.append(reject('duplicate_coefficient',lambda:V.verify_literal((terms+(terms[0],),rhs,label),angles)))
 for name,tail in[('bad_owner','9_0_1_1_0_31/32_31/32'),('bad_axis','0_2_1_1_0_31/32_31/32'),('bad_sign','0_0_0_1_0_31/32_31/32'),('zero_direction','0_0_1_0_0_31/32_31/32'),('negative_parameter','0_0_1_1_0_31/32_-1'),('reversed_parameter','0_0_1_1_0_1/2_1'),('changed_cap_parameter','0_0_1_1_0_1_1')]:
  negatives.append(reject(name,lambda tail=tail:V.verify_literal((terms,rhs,V.PREFIX+tail),angles)))
 assert not any(name in sys.modules for name in('numpy','scipy','highspy'))
 report=dict(status='PASS_GENERAL_CENTER_CONE_EXACT_CONTROLS',exact_parameter_identities=identities,positive_literal_controls=count,rejected_control_count=len(negatives),rejected_controls=negatives,full_canonical_angle_rows_retained=True,closed_endpoint_equality_retained=True,numerical_packages_imported=False,new_original_cells=0,new_masks=0,source_sha256={n:hashlib.sha256((HERE/n).read_bytes()).hexdigest()for n in['physical_general_center_cone_rows.py','independent_general_center_cone_rows.py','GENERAL_CENTER_CONE_HAND_PROOF.md']})
 (HERE/'GENERAL_CENTER_CONE_CONTROLS.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
