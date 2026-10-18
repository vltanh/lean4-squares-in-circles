"""Fixed rational comparisons in the complete quarter-one hand proof.

This is an optional arithmetic replay of the displayed constants.  It
performs no optimization, sampling, or adaptive subdivision.
"""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json

Q, p, q, g, K = F(9789,2500), F(13,200), F(203,200), F(291,250), F(73,10)
pi, R, ac = F('3.14159'), F('1.979'), F(7,12)
goal = F(157,200)
checks = []
def check(name, left, right=F(0)):
    assert left > right, (name, left, right)
    checks.append({'name': name, 'strict_margin': str(left-right)})
def sinlo(x):
    return sum((-1)**j*x**(2*j+1)/factorial(2*j+1) for j in range(4))
def sinhi(x):
    return sum((-1)**j*x**(2*j+1)/factorial(2*j+1) for j in range(3))
def coslo(x):
    return sum((-1)**j*x**(2*j)/factorial(2*j) for j in range(4))
def coshi(x):
    return sum((-1)**j*x**(2*j)/factorial(2*j) for j in range(5))

check('outer axial lower', Q-F(1,4), F('1.9145')**2)
check('outer axial upper', F('1.915')**2, Q-F(1,4))
check('outer diagonal lower', Q/2, F('1.399')**2)
check('outer diagonal upper', F('1.4')**2, Q/2)
check('core diagonal lower', F(2), (24*F('.058'))**2)
check('core diagonal upper', (24*F('.06'))**2, F(2))
check('radius upper', R**2, Q)
check('outer marker positive at b=0', -F('.09')+p*F('1.4145'))
check('outer marker increasing', q-p)
assert F('.882') == -F('.09')+(p+q)*F('.9')  # strict c_o < .9 above
check('outer marker minus b decreases', F(100,383), F(3,13))
check('outer marker minus b lower', -F('.09')+F('.08')*F('.899'), -F('.019'))
check('outer marker minus b upper', F('.002'), -F('.09')+p*F('1.415'))
check('core marker upper', F('.84'), K*(ac-F('.558'))+g*F('.56'))
check('core-quarter marker perturbation', F('.06'), (g-F('1.077372'))*F('.56'))
check('core/core cost', F(4,3)-F('.48'), goal)
check('easy opposite sign cost', pi/2-F('.7'), goal)
check('outer sloped line upper', F('2.416')**2, F('1.49')*Q)
check('sin linear lower coefficient', 1-F('.7')**2/6, F('.9'))
check('one minus cos quadratic lower coefficient', F(1,2)-F('.7')**2/24, F('.47'))

x = F('.7')
sl, sh, cl, ch = F('.6442'), F('.64424'), F('.76484'), F('.764844')
check('sin .7 lower', sinlo(x), sl)
check('sin .7 upper', sh, sinhi(x))
check('cos .7 lower', coslo(x), cl)
check('cos .7 upper', ch, coshi(x))
check('norm derivative sign', q*(1-x*x/2)-p*x)
lam0 = F('.975')
check('negative-half norm bound', F(5,4)*lam0**2-2*p*lam0-p*p-q*q)
check('negative-half norm bound monotonicity', F(5,2)*lam0-2*p)
check('positive-half norm bound', 3*lam0**2-2*lam0*(p+F('.645')*q)-p*p-q*q)
check('positive-half norm bound monotonicity', 6*lam0-2*(p+F('.645')*q))
check('negative-half concavity', cl-F(3,4))

rows=[]
for lam, c, nm, n0, np in [
    (F('.975'), F('.0919'), F('.9'), F('1.454'), F('1.85')),
    (q, F('.088'), F('.916'), F('1.483'), F('1.87')),
    (g, F('.09'), F('.992'), F('1.594'), F('2.007')),
]:
    check(f'norm minus {lam}', nm*nm, p*p+q*q+lam*lam+2*lam*(p*ch-q*sl))
    check(f'norm zero {lam}', n0*n0, (p+lam)**2+q*q)
    check(f'norm plus {lam}', np*np, p*p+q*q+lam*lam+2*lam*(p*ch+q*sh))
    for xx, cc, ss, nn in [(-x,cl,F(0),nm),(F(0),F(1),F(0),n0),(x,cl,sl,np)]:
        value=pi/2+xx+c+(p+q+lam)/2+lam*cc+lam*ss-R*nn
        check(f'envelope {lam} at {xx}', value, goal)
        rows.append({'lambda':str(lam),'constant':str(c),'x':str(xx),'norm_upper':str(nn),'cost_lower':str(value)})

F0=pi/2+F('.09')+(p+q+g)/2+g-R*F('1.594')
assert F0==F('.792269')
check('outer negative-source envelope constant', F('.18')-p*F('1.415'), F('.088'))
check('negative source is on core side, agreeing projection', F('.5'), R-F('1.5'))
check('negative source is on core side, opposing projection', F('.5'), F('.915')-F('.5'))
check('negative-target coefficient of A', q*cl, p)
check('negative-target coefficient of B', q-g*F('.7'))
check('negative-target quadratic coefficient', F('.9')*F('.47'), F('.4'))
check('negative-target secondary cost', pi/2-g*F('.415')-F(121,640), goal)
check('outer/core secondary cost', pi/2-F('.49344'), goal)
check('outer/core negative-half secondary difference', g*F('1.05')*F('.9'), F(1))
check('outer/core positive-half secondary difference', 1-g*F('.06'))

check('core/outer primary positive-target cost', pi/2+F(7,18)-F('.996'), goal)
check('core/outer primary negative-target negative-half derivative bracket', F('.399')-F('.7')/4-F('1.399')*F('.7')**2/6)
check('core/outer primary negative-target negative-half cost', pi/2-F('.859')-F(1,12)+F('.5'), goal)
check('core/outer primary negative-target near zero cost', pi/2-F('.859')+1-ac-F('.1415'), goal)
check('core/outer primary negative-target positive tail', pi/2+F('.1')-F('.84'), goal)

check('outer/core primary negative-target positive-half bracket', 1-g/12-F('.7')*g/4)
check('outer/core primary negative-target h bracket at .6', 13*g/12-1-g*F('.6')/4-13*g*F('.6')**2/72)
z=F('.7')
hlo=-z+g*(coslo(z)-1)/2+13*g*sinlo(z)/12
check('outer/core primary negative-target h at .7', hlo, -F('.025'))
z=F('.6')
check('sin .6 lower',sinlo(z),F('.564'))
check('cos .6 lower',coslo(z),F('.825'))
check('cos .6 upper',F('.826'),coshi(z))
check('W .6 lower',(1+sinlo(z)+coslo(z))/2,F('1.1945'))
check('outer/core primary negative-target forced B', F('1.1945')-F('1.415')+F('.558')*F('.564'), F('.11')*F('.826'))
check('outer/core primary negative-target tail cost', F0-F('.025')+g*F('.11')*F('.174'), goal)

check('outer/core corner positive-target x barrier', F('1.5')-F('.3')**2/2-F('.3')/12, F('1.415'))
for xx in (F('.3'),F('.7')):
    P=pi/2-F('.842')-F(33,350)+F(37,42)*xx-F(5,7)*xx*xx
    check(f'outer/core corner positive-target endpoint {xx}',P,goal)
check('outer/core side positive-target positive-half bracket',1-g/12-F('.7')*g/2)
z=F('.5')
check('outer/core side positive-target feasibility barrier', F('.5')+F(13,12)*(z-z**3/6)+F('.5')*(1-z*z/2),F('1.415'))
check('outer/core side positive-target low-z bracket',13*g/12-1-F('.915')*g*F('.4')/2-13*g*F('.4')**2/72)
num=F('.915')-F(13,12)*(F('.4')-F('.4')**3/6)-F('.5')*(1-F('.4')**2/2)
check('outer/core side positive-target high-z B bound',F('.04')*F('.875'),num)
check('outer/core side positive-target h bracket at .5',13*g/12-1-g*F('.5')/4-13*g*F('.5')**2/72)
check('outer/core side positive-target tail cost',F0-g/200,goal)

out={'status':'PASS','strict_comparisons':len(checks),'F0_lower':str(F0),'endpoint_rows':rows,'comparisons':checks}
Path(__file__).with_name('quarter_one_all_boundary_hand_arithmetic.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'PASS','strict_comparisons':len(checks),'F0_lower':str(F0),'endpoint_rows':rows},indent=2))
