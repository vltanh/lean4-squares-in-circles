"""Fixed rational comparisons for the continuous mismatch implications."""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json

checks=[]
def positive(name,x):
    x=F(x)
    assert x>0,(name,x)
    checks.append({'name':name,'positive_reserve':str(x)})

def trig(x,odd,degree):
    return sum((F((-1)**((i-int(odd))//2),factorial(i))*x**i
                for i in range(int(odd),degree+1,2)),F(0))

rows=[('7/10','29/100'),('2/5','38/100'),('3/10','41/100'),
      ('1/4','43/100'),('1/5','44/100'),('1/8','46/100'),
      ('1/10','47/100'),('1/20','48/100'),('1/40','49/100'),
      ('1/250','49/100')]
for L,kappa in rows:
    x,k=F(L),F(kappa)
    positive('chord slope '+L,(trig(x,True,7)+trig(x,False,10)-1)/2-k*x)

Q=F('3.9156')
positive('sqrt2 exceeds 141/100',2-F('1.41')**2)
assert F(1,2)+F('1.41')/24==F('0.55875')
positive('a upper from farthest corner',(F('1.415')+F(1,2))**2+F(1,4)-Q)
positive('b upper from farthest corner',2*F('1.4')**2-Q)
primary=F('.915')-F('1.05875')*F('.92')+F('.05875')*F('.4')
assert primary==-F(711,20000)
positive('both primary margins negative',-primary)
positive('source sign margin',-(F('.915')*F('.1')+F('.4')-F('.5')))
positive('target sign margin',-(F('.4')+F('.915')*F('.1')-F('.5')*(1-F('.1')**2/2)))
example=7*F('.89735')+F('.02')*F('.29')*F('.3')-F(710,113)
assert example==F(47,11300000)
positive('conditional example contraction reserve',example)
out={'status':'PASS','scope':'Fixed constants for the hand mismatch contraction, primary-axis elimination and strict-sign implications; no unproved pair theorem is asserted.','checks':checks,'comparison_count':len(checks)}
Path(__file__).with_name('candidate_mismatch_bootstrap_arithmetic.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
