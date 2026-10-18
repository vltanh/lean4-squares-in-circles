"""Fixed rational arithmetic for the symmetric aligned edge-4 hand lemma."""
from fractions import Fraction as F
import json

Q, R = F('9789/2500'), F('7289/2500')
p, g, gamma, C = map(F, ('1.49748','1.89442','.89765','3.23522'))
checks = []

def positive(name, value):
    assert value > 0, (name, value)
    checks.append({'name': name, 'positive_reserve': str(value)})

P = list(map(F, ('161761/12500','572020119/31250000',
                 '-42944417/7812500','-284163/100000','37437/50000')))
derived = [4*C, g*(4*R-2), C-2*p*R, -3*g/2, p/2]
assert P == derived
assert C == 2*F('.03965')+F('3.85510')-p/2+g/2-gamma

def derivative(poly):
    return [j*poly[j] for j in range(1,len(poly))]

def evaluate(poly,x):
    ans = F(0)
    for c in reversed(poly):
        ans = ans*x+c
    return ans

P1, P2, P3 = derivative(P), derivative(derivative(P)), derivative(derivative(derivative(P)))
assert P3 == [F('-17.04978'),F('17.96976')]
positive('diagonal above .5',Q/2-F(1))
positive('diagonal below .9',F('1.4')**2-Q/2)
positive('first endpoint radical above 1.398',Q-F('1.4')**2-F('1.398')**2)
positive('second endpoint radical above 1.885',Q-F('.6')**2-F('1.885')**2)
positive('radical sum above 3.28',F('1.398')+F('1.885')-F('3.28'))
positive('radical sum below 3.42',F('3.42')**2-4*R)
positive('quartic third derivative positive',evaluate(P3,F('3.28')))
positive('quartic second derivative above 29',evaluate(P2,F('3.28'))-29)
u0 = F('16987/5000')
positive('reference lies above lower endpoint',u0-F('3.28'))
positive('reference lies below upper endpoint',F('3.42')-u0)
positive('reference value above .001948',evaluate(P,u0)-F('.001948'))
positive('reference derivative greater than -.0015',evaluate(P1,u0)+F('.0015'))
positive('reference derivative less than .0015',F('.0015')-evaluate(P1,u0))
positive('completed-square quartic reserve',F('.001948')-F('.0015')**2/58-F('.0019'))
assert F('.0019')/(F('3.42')**2+4)==F(19,156964)
positive('strict cost surplus above .00012',F(19,156964)-F('.00012'))
positive('self-contained whole-angle curvature floor',F(3)*F('1.8')*F('3.9')/8-2)

print(json.dumps({'status':'PASS','scope':'Symmetric aligned outer contact only',
                  'coefficient_identities':6,'strict_comparisons':len(checks),
                  'checks':checks},indent=2))
