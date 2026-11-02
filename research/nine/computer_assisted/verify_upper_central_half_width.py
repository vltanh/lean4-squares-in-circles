"""Independent exact arithmetic audit of the recovered half-width theorem.

All geometric coverage is in the companion hand proof. No producer,
numerical solver, external package, Lean, or CI is used.
"""
from fractions import Fraction as F
import json


def mul(p,q):
    out=[F(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):out[i+j]+=a*b
    return out

def derivative(p):return [i*p[i] for i in range(1,len(p))]
def value(p,x):return sum(c*x**i for i,c in enumerate(p))
def subtract(p,q):return [(p[i] if i<len(p) else 0)-(q[i] if i<len(q) else 0) for i in range(max(len(p),len(q)))]

P=subtract([1024*x for x in mul([4,4,1],[1,0,1])],[3481*x for x in [1,2,1]])
Z=subtract([250000*x for x in mul([9,6,1],[1,0,1])],[1692601*x for x in [1,2,1]])
assert P == [615,-2866,1639,4096,1024]
assert Z == [557399,-1885202,807399,1500000,250000]
P1,P2=derivative(P),derivative(derivative(P))
Z1,Z2=derivative(Z),derivative(derivative(Z))
assert all(x>0 for x in P2+Z2)
assert value(P1,F(1,4)) == -F(2429,2)
assert value(P2,F(1,4)) == 10190
assert value(P,F(1,3)) == F(496,81)
assert value(P1,F(1,3)) == -F(6920,27)
assert value(Z,F(1,2)) == F(79091,4)
assert value(Z1,F(1,2)) == 172197
assert F(1301,1000)-F(59,64) == F(3033,8000)
assert F(1,2)-F(3033,8000) == F(967,8000)
assert F(59,64)-F(703,4000)-F(151,240) == F(2807,24000)
assert F(2807,24000)-F(7,60) == F(7,24000)
assert F(91,60)+F(1,16) == F(379,240)
assert F(379,240)-F(59,60) == F(143,240)
assert F(143,240)+F(1,30) == F(151,240)
assert F(129,80)-F(59,60) == F(151,240)
checks={
    'endpoint_main_axis_root':194*1600-557**2,
    'endpoint_diagonal_resource':F(2377**2+752**2-1105*5625,1440000),
    'P_quarter_negative_derivative':-value(P1,F(1,4)),
    'P_curvature_after_quarter':value(P2,F(1,4))-10000,
    'P_anchor_lower_bound':value(P,F(1,3))-6,
    'P_anchor_derivative_bound':257-abs(value(P1,F(1,3))),
    'P_complete_tangent_quadratic':6-F(257**2,20000),
    'Z_global_curvature':Z2[0]-1600000,
    'Z_anchor_lower_bound':value(Z,F(1,2))-19000,
    'Z_anchor_derivative_bound':173000-abs(value(Z1,F(1,2))),
    'Z_complete_tangent_quadratic':19000-F(173000**2,3200000)-9000,
    'sqrt34_lower':34-F(583,100)**2,
    'sqrt34_upper':36-34,
    'J_anchor_value':4119*583-60*40000,
    'J_anchor_derivative_upper':F(13,102)-F(967,8000),
    'J_anchor_derivative_lower':211*9911-1300*1600,
    'J_complete_concave_quadratic':F(703,4000)-F(351,2000)-2*F(11,1000)**2,
    'replacement_above_seven_sixtieths':F(2807,24000)-F(7,60),
    'replacement_above_one_tenth':F(2807,24000)-F(1,10),
    'zero_loss_branch_floor':F(59,64)-F(151,240)-F(7,60),
    'zero_loss_branch_exact_claim':F(59,64)-F(151,240)-F(2807,24000),
}
assert checks['endpoint_diagonal_resource'] == F(8,1440000)
assert checks['J_complete_concave_quadratic'] == F(1,125000)
assert all(x>0 for x in checks.values())
print(json.dumps({'result':'PASS','P_coefficients_ascending':[str(x) for x in P],'Z_coefficients_ascending':[str(x) for x in Z],'positive_reserves':{k:str(v) for k,v in checks.items()}},indent=2))
