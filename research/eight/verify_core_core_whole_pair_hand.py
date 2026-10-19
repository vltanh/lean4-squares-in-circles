"""Exact scalar comparisons in CORE_CORE_WHOLE_PAIR_HAND_PROOF.md."""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json


def atan_partial(x, m):
    return sum(((-1)**j*x**(2*j+1)/F(2*j+1)
                for j in range(m+1)), F(0))


g=F(269343, 250000)
kappa=7*g/12
assert F(7) <= F(7506931, 10**6) <= F(8)
assert F(16,25)-kappa>0
assert atan_partial(F(3,4),8)<F(161,250)
side_upper=F(161,250)-F(12,25)+(F(16,25)-kappa)*F(6,7)
assert side_upper==F(608599,3500000)<F(7,40)
assert 1-kappa-F(6,7)**2/3>0
assert F(4,3)**2<2  # c_C>5/9
assert F(7,5)**2<2  # c_C>67/120
assert (F(9,5)-g)**2/(24*7)<F(1,300)
assert F(7,40)+F(1,300)<F(9,50)
assert 7>g and g<F(11,10)
core_ell_upper=F(8,40)+F(67,120)*F(11,10)
assert core_ell_upper==F(977,1200)
assert atan_partial(F(6,7),3)>F(2,3)
assert F(2,3)-core_ell_upper==-F(59,400)>-F(9,50)
assert F(85,144)<F(16,25)
assert F(43,30)**2>2  # sqrt(2)/2+1/12 <4/5
cosine_lower=sum(((-1)**j*F(4,3)**(2*j)/factorial(2*j)
                  for j in range(4)), F(0))
assert cosine_lower==F(7709,32805)>F(7,32)
assert F(71,50)**2>2  # h<21/100
pair_lower=F(4,3)-F(9,50)*F(21,100)-F(9,25)
assert pair_lower==F(14033,15000)>F(23,25)
out={'status':'PASS','K_domain':['7','8'],'g':str(g),
     'side_potential_upper':str(side_upper),
     'corner_increment_upper':'1/300',
     'absolute_potential_upper':'9/50',
     'cosine_lower_at_four_thirds':str(cosine_lower),
     'pair_lower':str(pair_lower),'target':'23/25',
     'strict_reserve':str(pair_lower-F(23,25)),
     'scope':'all signed core/core pairs and all separating axes'}
Path(__file__).with_name('core_core_whole_pair_hand_arithmetic.json').write_text(
    json.dumps(out,indent=2)+'\n')
print('PASS:',out)
