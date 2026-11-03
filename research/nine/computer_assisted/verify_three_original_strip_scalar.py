"""Exact scalar companion to THREE_ORIGINAL_NARROW_STRIP_CAPACITY_HAND_PROOF.
No numerical optimizer or physical-disjointness approximation is a premise.
"""
from fractions import Fraction as F
from math import comb
import json
from pathlib import Path

coeff=[F(-1),F(18),F(-6),F(-16),F(6),F(0),F(5)]
a,b=F(1,6),F(1)
power=[sum(coeff[k]*comb(k,j)*a**(k-j)*(b-a)**j
           for k in range(j,7)) for j in range(7)]
bern=[sum(power[j]*F(comb(i,j),comb(6,j))
          for j in range(i+1)) for i in range(7)]
expected=[F(82301,46656),F(29681,7776),F(253,48),F(139,24),F(191,36),F(13,3),F(6)]
checks={
 'printed_bernstein_identity':bern==expected,
 'all_bernstein_coefficients_positive':all(z>0 for z in bern),
 'k_one_sixth_above_two_fifths':F(25,148)>F(4,25),
 'k_one_sixth_below_twenty_one_fiftieths':F(25,148)<F(441,2500),
 'A_one_sixth_above_101_200':F(37,144)>F(10201,40000),
 'one_sixth_distance_bound':F(1,50)**2+F(99,200)**2==F(9817,40000)<F(1,4),
 'sqrt_two_lower_bound':F(141,100)**2<F(2),
 'slope_one_distance_bound':F(83,50)-F(141,100)==F(1,4),
 'unit_disk_second_point':F(7,10)**2+F(71,100)**2==F(9941,10000)<1,
 'joining_slope':(1-F(71,100))/(F(7,10)-F(2,5))==F(29,30),
 'joining_intercept':1+F(29,30)*F(2,5)==F(104,75),
 'first_join':F(208,75)-F(29,15)*F(2,5)==2,
 'last_join':F(208,75)-F(29,15)*F(7,10)==F(71,50),
 'each_ordered_gap_gt_seven_tenths':1-F(7,10)**2>F(7,10)**2,
 'rotation_projection_positive':2-3*F(7,10)**2==F(53,100)>0,
 'rational_endpoint_difference_coefficient':1/(2*F(7,5))==F(5,14),
}
# Independently expand the Bernstein expression into its s power coefficients.
recovered=[F(0) for _ in range(7)]
for i,bi in enumerate(bern):
 for j in range(7-i):
  recovered[i+j]+=bi*comb(6,i)*comb(6-i,j)*((-1)**j)
checks['reverse_bernstein_expansion']=recovered==power
assert all(checks.values()),{k:v for k,v in checks.items() if not v}
report={'scope':'Exact scalar arithmetic and coefficient identities only; geometric proof is in the accompanying hand theorem.','status':'PASS','checks':checks,'bernstein_coefficients':[str(z) for z in bern]}
Path(__file__).with_name('three_original_strip_scalar_report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':'PASS','checks':len(checks),'bernstein_rows':len(bern)}))
