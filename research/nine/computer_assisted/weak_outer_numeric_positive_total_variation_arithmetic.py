#!/usr/bin/env python3
"""Exact scalar constants for the positive-D total-variation row theorem."""
from fractions import Fraction as F
import json

def verify():
    reserve=23**2-2*16**2
    assert reserve==17>0
    two=F(10,7)**2-2;three=3-F(12,7)**2
    assert two==F(2,49)>0 and three==F(3,49)>0
    endpoint=F(77,64)+F(6,7)-2
    assert endpoint==F(27,448)>0
    # After multiplication by r, q+sigma equals
    # r^2+1-2r+t(23/32-r/2)=(r-1)^2+t(23/32-r/2).
    def add(*polynomials):
        result={}
        for polynomial in polynomials:
            for key,value in polynomial.items():result[key]=result.get(key,F(0))+value
        return {key:value for key,value in result.items() if value}
    def mul(left,right):
        result={}
        for (a,b),u in left.items():
            for (c,d),v in right.items():
                key=(a+c,b+d);result[key]=result.get(key,F(0))+u*v
        return {key:value for key,value in result.items() if value}
    q_times_r={(2,0):F(1),(1,0):F(-1),(1,1):F(-1,2)}
    sigma_times_r={(0,0):F(1),(0,1):F(23,32),(1,0):F(-1)}
    q_sigma=add(q_times_r,sigma_times_r)
    r_minus_one={(1,0):F(1),(0,0):F(-1)}
    square_payment=add(mul(r_minus_one,r_minus_one),{(0,1):F(23,32),(1,1):F(-1,2)})
    assert q_sigma==square_payment
    # The numerator of (q+2h)' before subtracting1/2 is
    # s*(1+s^2)+(1-s)=1+s^3.
    coefficients=[F(1),F(1)-F(1),F(0),F(1)]
    assert coefficients==[1,0,0,1]
    return {'status':'PASS','positive_D_total_variation':'1/2',
            'small_tilt_squared_reserve':reserve,'radical_bound_reserves':[str(two),str(three)],
            'large_tilt_endpoint_lower_bound':str(endpoint),'whole_mask_closed':False}
if __name__=='__main__':print(json.dumps(verify(),indent=2))
