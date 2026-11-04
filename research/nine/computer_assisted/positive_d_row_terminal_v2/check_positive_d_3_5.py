"""Exact rational constants and algebra for the continuous 3/5 hand proof."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json
HERE=Path(__file__).resolve().parent
U=F(3,5);k=F(23,32)
checks={
 'U_positive':U>0,'U_below_two_thirds':U<F(2,3),'U_below_one':U<1,
 'U_squared_below_half':U*U<F(1,2),
 'one_minus_U_squared':1-U*U==F(16,25),
 'physical_pair_cone':F(4,5)>U,
 'critical_slope':F(3,4)**2*(1-U*U)==U*U,
 'critical_radius':1+F(3,4)**2==F(5,4)**2,
 'critical_q_value':F(5,4)-1-U*F(3,4)==F(-1,5),
 'small_t_radius_upper_squared_reserve':F(49,36)-F(34,25)==F(1,900),
 'small_t_slope_payment':k/F(7,6)-U==F(9,560),
 'middle_t_radius_lower_squared_reserve':F(34,25)-F(29,25)**2==F(9,625),
 'middle_t_positive_square':(F(29,25)-1)**2==F(16,625),
 'middle_t_negative_coefficient':k-U*F(5,4)==F(-1,32),
 'middle_t_total_reserve':F(16,625)-F(3,128)==F(173,80000),
 'large_t_sigma_decreases':k<F(3,4),
 'sqrt2_upper_squared_reserve':F(100,49)-2==F(2,49),
 'large_t_endpoint_payment':F(55,32)/F(10,7)-F(6,5)==F(1,320),
 'equality_height_reserve':F(2,3)-U==F(1,15),
 'G_height_reserve':1-U==F(2,5),
}
# Independent polynomial expansion. Keys are (degree in r, degree in s).
def add(*polynomials):
    ans={}
    for poly in polynomials:
        for monomial,coefficient in poly.items():ans[monomial]=ans.get(monomial,F(0))+coefficient
    return {m:c for m,c in ans.items()if c}
def scale(poly,c):return {m:v*c for m,v in poly.items()if v*c}
def mul(a,b):
    ans={}
    for (i,j),u in a.items():
        for (k,l),v in b.items():ans[i+k,j+l]=ans.get((i+k,j+l),F(0))+u*v
    return {m:c for m,c in ans.items()if c}
one={(0,0):F(1)};r={(1,0):F(1)};s={(0,1):F(1)}
q=add(r,scale(one,-1),scale(s,-U))
sigma_numerator=add(one,scale(s,k),scale(r,-1))
left=add(mul(r,q),sigma_numerator)
right=add(mul(add(r,scale(one,-1)),add(r,scale(one,-1))),mul(s,add(scale(one,k),scale(r,-U))))
checks['scalar_payment_polynomial_identity']=left==right
# Differentiate q+2h and multiply by r^3 before using r^2=1+s^2.
left_derivative=add(mul(s,mul(r,r)),scale(mul(r,mul(r,r)),-U),mul(r,r),scale(mul(s,add(one,s)),-1))
right_derivative=add(one,mul(s,mul(s,s)),scale(mul(r,mul(r,r)),-U))
def circle_reduce(poly):
    pending=dict(poly);ans={}
    while pending:
        (i,j),coefficient=pending.popitem()
        if i>=2:
            for m in((i-2,j),(i-2,j+2)):pending[m]=pending.get(m,F(0))+coefficient
        else:ans[i,j]=ans.get((i,j),F(0))+coefficient
    return {m:c for m,c in ans.items()if c}
checks['derivative_polynomial_reduction']=circle_reduce(left_derivative)==circle_reduce(right_derivative)
# Exact factorization proving the derivative lower bound on [0,1].
s2=mul(s,s);s3=mul(s,s2);s4=mul(s2,s2)
left_inequality=add(scale(mul(add(one,s3),add(one,s3)),2),scale(mul(add(one,s2),mul(add(one,s2),add(one,s2))),-1))
right_inequality=mul(mul(add(one,scale(s,-1)),add(one,scale(s,-1))),add(s4,scale(s3,2),scale(s,2),one))
checks['derivative_lower_bound_factorization']=left_inequality==right_inequality
assert all(checks.values())
source=HERE/'POSITIVE_D_TOTAL_VARIATION_3_5_HAND_PROOF.md'
out=dict(status='PASS_EXACT_3_5_SCALAR_IDENTITIES_AND_CONSTANTS',bound=str(U),exact_checks=len(checks),checks=checks,
 hand_proof_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 continuous_physical_proof_is_required=True,new_original_cells=0,new_masks=0)
(HERE/'POSITIVE_D_3_5_ARITHMETIC.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
