from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / 'INNER_PENTAGON_H3_0124_UNIQUE_FREE_ENDPOINT_EXCLUSION.md'
EXPECTED = '76ba586f7147908f4f2eaf738285f4324871fa223c5663c58d533476e9bbb3a1'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

assert sha(SOURCE) == EXPECTED
pins = []
for name, digest in re.findall(r'^\|\s*([^|]+\.md)\s*\|\s*([0-9a-f]{64})\s*\|', SOURCE.read_text(), re.M):
    name = name.strip().strip('`')
    actual = sha(ROOT / name)
    assert actual == digest, (name, actual, digest)
    pins.append({'file': name, 'sha256': actual})
assert len(pins) == 11

# Independent sparse polynomial arithmetic; no author checker is imported.
N = 7
class P:
    def __init__(self, d=0):
        self.d = {k:F(v) for k,v in d.items() if v} if isinstance(d,dict) else ({(0,)*N:F(d)} if d else {})
    def __add__(self, other):
        other = other if isinstance(other,P) else P(other)
        d = self.d.copy()
        for k,v in other.d.items(): d[k] = d.get(k,F(0))+v
        return P(d)
    __radd__ = __add__
    def __neg__(self): return P({k:-v for k,v in self.d.items()})
    def __sub__(self, other): return self + (-other if isinstance(other,P) else -F(other))
    def __rsub__(self, other): return P(other) - self
    def __mul__(self, other):
        other = other if isinstance(other,P) else P(other)
        d = {}
        for a,x in self.d.items():
            for b,y in other.d.items():
                k=tuple(i+j for i,j in zip(a,b)); d[k]=d.get(k,F(0))+x*y
        return P(d)
    __rmul__ = __mul__
    def __pow__(self, n):
        out=P(1)
        for _ in range(n): out=out*self
        return out

def var(i):
    a=[0]*N; a[i]=1
    return P({tuple(a):1})
A,B,C,S,c,s,v = [var(i) for i in range(N)]
identities = {}
def ident(name, p):
    assert not p.d, (name,p.d)
    identities[name] = True

ident('opposite_corner_determinant', (A-1)*B-(B-1)*A-(A-B))
ident('adjacent_u_corner_determinant', (A-1)*(-B)-(-B)*A-B)
ident('adjacent_v_corner_determinant', (-A)*B-(B-1)*(-A)+A)
ident('opposite_incoming_component_order', (1-B*S)-(1-A*S)-(A-B)*S)
ident('bottom_vertex_own_projection', c*(-(c-s))*F(1,2)+s*v+F(1,2)-s*(v+(c+s)*F(1,2))-(1-c*c-s*s)*F(1,2))
Nu=1-A*S; Nv=B*S; cx=C-F(1,2); cy=F(3,2)-B
D=Nu*cx+Nv*cy-(Nu*cy-Nv*cx)
formula=(1-A*S)*(C+B-2)+B*S*(C+1-B)
ident('dot_minus_determinant_expansion', D-formula)
ident('affine_parameter_expansion', D-(C+B-2)-S*(-A*(C+B-2)+B*(C+1-B)))
L=A-C
ident('actual_lower_parameter_numerator', A*(1-L)*(C+B-2)+B*L*(C+1-B)-(A*(C+B-2)+L*(-A*(C+B-2)+B*(C+1-B))))
ident('two_actual_circle_equations_difference', A*A+B*B-(C*C+(2-B)*(2-B))-(A*A-C*C+4*B-4))
ident('radial_zero_concurrence_cross_equation', (A-1)*B-(B-1)*A-(A-B))

Q=F(1105,256)
reserves = {
 'outward_port_exceeds_radius_squared': F(9,2)-Q,
 'upper_radius_below_21_10': F(21,10)**2-Q,
 'sqrt2_exceeds_7_5': F(2)-F(7,5)**2,
 'center_radius_exceeds_9_7': F(5,7)**2-F(1,2),
 'cosine_radius_derivative': F(9,7)**2-F(61,40)**2+2,
 'contact_tangent_below_7_3': F(49,9)-F(5537,1024),
 'contact_angle_below_3pi8': F(2)-F(16,9),
 'strong_contact_cosine_squared_integer': F(5*988**2-2205**2),
 'two_link_tangent_comparison': F(13,11)-F(15,13),
 'inner_shared_side_negative_center_radius': F(4)-F(221,100),
 'large_E2_radius_from_91_25': F(91,25)-F(19,10)**2,
 'outer_v_B_lower_bound': F(7,4)-F(13,10)**2,
 'outer_v_projection_beyond_R': F(23,10)-F(21,10),
 'one_over_sqrt3_below_3_5': F(3,5)**2-F(1,3),
 'adjacent_A_small_radius_contradiction': F(4)-F(173,50),
 'adjacent_B_below_three_halves': F(3,2)-F(23,16),
 'negative_D0_B_below_7_10': F(231,100)-F(9,4),
 'negative_D0_A_above_187_100': F(351,100)-F(187,100)**2,
 'negative_D0_strict_affine_reserve': -F(63,100)*F(1,5)+F(37,420)*F(8,5),
 'zero_concurrence_outer_axis_width': F(12,5)-F(21,10),
}
assert all(v>0 for v in reserves.values())
assert reserves['outward_port_exceeds_radius_squared']==F(47,256)
assert reserves['contact_tangent_below_7_3']==F(343,9216)
assert reserves['strong_contact_cosine_squared_integer']==18695
assert reserves['two_link_tangent_comparison']==F(4,143)
assert reserves['negative_D0_strict_affine_reserve']==F(157,10500)
equalities = {
 'strong_pair_cosine': ((F(7,5)**2+F(9,7)**2-2)/(2*F(7,5)*F(9,7)),F(988,2205)),
 'small_horizontal_angle_ratio': (F(1,10)/F(7,5),F(1,14)),
 'adjacent_B_radius_cap': (Q-F(9,4),F(23,16)**2),
 'negative_D0_L_lower': (F(187,100)-F(3,2),F(37,100)),
 'negative_D0_first_lower': (F(13,10)+F(1,2)-2,-F(1,5)),
 'negative_D0_second_lower': (F(13,10)+1-F(7,10),F(8,5)),
 'negative_D0_multiplier': (F(1,2)*F(37,100)/F(21,10),F(37,420)),
}
assert all(a==b for a,b in equalities.values())
out = {
 'reviewer':'triangle_bridges',
 'source':SOURCE.name,'source_sha256':EXPECTED,
 'method':'Independent exact Fraction and sparse-polynomial reconstruction; no author checker imported; no numerical pose premise.',
 'input_pins':pins,
 'polynomial_identities':identities,
 'strict_reserves':{k:str(v) for k,v in reserves.items()},
 'rational_equalities':{k:str(a) for k,(a,b) in equalities.items()},
 'all_passed':True,
}
target=ROOT/'checkpoints/triangle_bridges_h3_0124_unique_free_independent_checks_2026_10_28.json'
target.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'source_sha256':EXPECTED,'pins':len(pins),'polynomial_identities':len(identities),'strict_reserves':len(reserves),'rational_equalities':len(equalities),'checks_sha256':sha(target),'checker_sha256':sha(Path(__file__))},indent=2))
