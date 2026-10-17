"""Fixed rational arithmetic for the same-sign quarter-one hand lemma."""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json

Q, p, q, lam = F(9789,2500), F(13,200), F(203,200), F(39,40)
R_hi, pi_lo = F(1979,1000), F(314159,100000)
assert R_hi**2 > Q
assert F('1.9145')**2 < Q-F(1,4)
assert F('1.399')**2 < Q/2
assert p*F('1.4145') > F('.0919')
assert (p+q-lam)*F('.899') > F('.0919')

N0_hi = F('1.454')
assert (p+lam)**2+q*q < N0_hi**2
assert -lam*F('.764')+N0_hi/2 < 0
assert -lam+F('1.85')/2 < 0
assert q*(1-F('.7')**2/2)-p*F('.7') > 0
assert F('1.85')**2 > p*p+q*q+lam*lam+2*lam*(p+q*F('.645'))

x=F(7,10)
sl,sh,cl,ch=F(3221,5000),F(16106,25000),F(19121,25000),F(191211,250000)
sinlo=sum((-1)**j*x**(2*j+1)/factorial(2*j+1) for j in range(4))
sinhi=sum((-1)**j*x**(2*j+1)/factorial(2*j+1) for j in range(3))
coslo=sum((-1)**j*x**(2*j)/factorial(2*j) for j in range(4))
coshi=sum((-1)**j*x**(2*j)/factorial(2*j) for j in range(5))
assert sl < sinlo < sinhi < sh < F('.645')
assert F('.764') < cl < coslo < coshi < ch
assert p*p+q*q+lam*lam+2*lam*(p*ch-q*sl) < F('.9')**2

rows=[]
for x,coslo,sinplus,normhi in [
    (-F(7,10),cl,F(0),F('.9')),
    (F(0),F(1),F(0),N0_hi),
    (F(7,10),cl,sl,F('1.85')),
]:
    value=pi_lo/2+x+F('.0919')+(p+q+lam)/2+lam*coslo+lam*sinplus-R_hi*normhi
    assert value>F(157,200)
    rows.append({'x':str(x),'N_upper':str(normhi),'F_lower':str(value)})

out={'status':'PASS','endpoint_rows':rows}
Path(__file__).with_name('quarter_one_outer_same_hand_arithmetic.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
