#!/usr/bin/env python3
"""Exact reconstruction of the four-row coupled cone inset-loss table."""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import hashlib,json

HERE=Path(__file__).resolve().parent
B=F(331,20000)+F(23,150)
assert B==F(10193,60000)
t0=1/(32*B)
assert t0==F(1875,10193)

coefficients=[F(0)]*7
for i,x in enumerate([F(1,1024),-B/16,B*B]):
    for j,y in enumerate([1,2,2,2,1]):
        coefficients[i+j]-=x*y
coefficients[6]+=1
integers=[-3515625,31192500,-34480999,-138378248,
          -134862623,-169570748,3496102751]
assert coefficients==[F(x,3600000000)for x in integers]

cuts=[t0,F(1,4),F(5,16),F(1,2),F(1)]
expected=[F(20711767,589824000000),
          F(195613010401,56623104000000000),
          F(7923782519,268435456000000),
          F(38487751,5120000000)]
rows=[]
for a,b,want in zip(cuts,cuts[1:],expected):
    powers=[sum(coefficients[k]*comb(k,j)*a**(k-j)*(b-a)**j
                for k in range(j,7))for j in range(7)]
    bernstein=[sum(powers[j]*F(comb(i,j),comb(6,j))
                   for j in range(i+1))for i in range(7)]
    assert min(bernstein)==want and want>0
    rows.append({'interval':[str(a),str(b)],
                 'bernstein_coefficients':list(map(str,bernstein)),
                 'minimum':str(want)})

floor_reserve=-F(7,20)+F(15,31)-F(1,32)-F(1,10)
assert floor_reserve==F(13,4960)>0
assert F(29,60)-F(7,20)==F(2,15)<F(23,150)
assert F(1,2)>F(7,10)**2 and 2>F(7,5)**2 and 46>F(27,4)**2
assert F(13,12)-F(7,10)==F(23,60)<F(29,60)
assert F(23,60)-F(7,10)==-F(19,60)
assert F(1,4)-F(18,155)**2-(F(29,30)-F(15,31))**2==F(2960,864900)>0
assert F(3,4)+F(29,30)==F(103,60)>F(88,60)
assert F(29,60)-F(7,5)==-F(11,12)
assert F(91,60)-F(11,12)==F(3,5)
assert F(4,5)-F(1,8)==F(27,40)>F(3,5)
report={'proof_status':'coupled_cone_inset_loss_exact_arithmetic_passed',
        'polynomial_denominator':3600000000,
        'polynomial_coefficients':integers,'rows':rows,
        'floor_reserve':str(floor_reserve),
        'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(HERE/'coupled_cone_inset_loss_arithmetic_replay.json').write_text(
    json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
