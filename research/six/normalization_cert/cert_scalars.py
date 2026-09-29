"""Scalar predicates (S1)-(S54) from the supplied normalization proof.

There are 78 inequalities and four algebraic-identity sanity checks. Positive
interval lower bounds, not sampled numerical minima, determine acceptance.
Three inequalities (S5, S30, S32a) are two-variable. Numerical minima are
reported only as diagnostics. ia.iv widens float endpoints outward.
"""
import math
import sys
from ia import *

H = HALF
SQ2 = arb(2).sqrt()
U0 = (Q0-(arb(5)/2-RHO0)**2).sqrt()-H
X0 = (Q0-arb(9)/4).sqrt()-H
T1 = (1/(2*R0)).asin()
UMAX = R0/SQ2-H
Q = arb(9)/10
A1P = PI/2-arb(5)/4*X0
A1M = PI/2-arb(5)/4*U0
A2M = arb(27)/50
VAC = 'vacuous'
RESULTS = []
SANITY = []


def U(a):
    """Upper bound on sqrt(Q0-(a+1/2)^2)-1/2 on the feasible portion.
    A negative radicand throughout is sufficient for vacuity."""
    d = Q0-(a+H)**2
    if d<0: return VAC
    return d.nonnegative_part().sqrt()-H


A = U


def B_up(t):
    p1 = (RHO0-H)*t.cos()-H*t.sin()
    p2 = R0-t.cos()-t.sin()
    if t<T1: return p1
    if t>T1: return p2
    return p1.max(p2)


def lab_up(a_lo,u_hi):
    return amin(5*u_hi/4,PI/6+(u_hi-H)/3+3*(1-a_lo)/4,PI/4)


def check1(name,f,lo_,hi_,maxdepth=48,note=''):
    stack = [(lo_,hi_,0)]
    best = float('inf')
    n,ok = 0,True
    while stack:
        l,h,d = stack.pop()
        n += 1
        v = f(iv(l,h))
        if isinstance(v,str):
            if v!=VAC: raise ValueError('unknown vacuity reason')
            continue
        if v>0:
            best = min(best,float(v.lower()))
            continue
        m = (l+h)/2
        if d>=maxdepth or not l<m<h:
            ok = False
            print(f'FAIL {name} at [{l},{h}]: {v}')
            break
        stack.extend(((l,m,d+1),(m,h,d+1)))
    est = float('inf')
    for i in range(2001):
        t = lo_+(hi_-lo_)*i/2000
        v = f(arb(t))
        if not isinstance(v,str): est = min(est,float(v.mid()))
    RESULTS.append((name,ok,est,n,note))
    print(f'{"OK" if ok else "BAD"} {name}: min~{est:.6f}, {n} intervals; {note}')
    return ok


def check2(name,f,box,maxdepth=40,note=''):
    stack,n,ok = [(box,0)],0,True
    while stack:
        bx,d = stack.pop()
        n += 1
        v = f(iv(*bx[0]),iv(*bx[1]))
        if isinstance(v,str):
            if v!=VAC: raise ValueError('unknown vacuity reason')
            continue
        if v>0: continue
        i = 0 if bx[0][1]-bx[0][0]>=bx[1][1]-bx[1][0] else 1
        l,h = bx[i]
        m = (l+h)/2
        if d>=maxdepth or not l<m<h:
            ok = False
            print(f'FAIL {name} at {bx}: {v}')
            break
        b1,b2 = list(bx),list(bx)
        b1[i],b2[i] = (l,m),(m,h)
        stack.extend(((tuple(b1),d+1),(tuple(b2),d+1)))
    est = float('inf')
    for i in range(201):
        for j in range(201):
            s = box[0][0]+(box[0][1]-box[0][0])*i/200
            t = box[1][0]+(box[1][1]-box[1][0])*j/200
            v = f(arb(s),arb(t))
            if not isinstance(v,str): est = min(est,float(v.mid()))
    RESULTS.append((name,ok,est,n,note))
    print(f'{"OK" if ok else "BAD"} {name}: min~{est:.6f}, {n} boxes; {note}')
    return ok


def check0(name,v,note=''):
    ok = bool(v>0)
    RESULTS.append((name,ok,float(v.mid()),1,note))
    print(f'{"OK" if ok else "BAD"} {name}: {float(v.mid()):.6f}; {note}')
    return ok


def sanity(name,v,note=''):
    ok = bool(abs(v)<arb('1e-15'))
    SANITY.append((name,ok,note))
    print(f'{"ok" if ok else "BAD"} {name}: identity sanity only; {note}')
    return ok


def up(x): return math.nextafter(float(x.upper()),math.inf)
def dn(x): return math.nextafter(float(x.lower()),-math.inf)
def upf(x): return math.nextafter(x,math.inf)
def dnf(x): return math.nextafter(x,-math.inf)
PI4 = up(PI/4)


def main():
    RESULTS.clear()
    SANITY.clear()
    print('Scalar certificate predicates for Q0=142559/50000')
    sanity('I1',(RHO0-H)*T1.cos()-H*T1.sin()-(R0-T1.cos()-T1.sin()),
           'cap branches agree at t1')
    sanity('I2',(arb(3)/2)**2+(X0+H)**2-Q0,'9/4+(X0+1/2)^2=Q0')
    sanity('I3',(arb(5)/2-RHO0)**2+(U0+H)**2-Q0,'(5/2-rho0)^2+(U0+1/2)^2=Q0')
    sanity('I4',(RHO0+H)**2+arb(1)/4-Q0,'(rho0+1/2)^2+1/4=Q0')

    check0('S1',(arb(3)/2-RHO0)-(R0-(arb(2)/5).cos()-(arb(2)/5).sin()),'B(2/5)<3/2-rho0')
    check0('S1a',arb(2)/5-T1,'t1<2/5')
    check0('S2',(arb(3)/2-RHO0)-(R0-SQ2),'cap frame is primary')
    check0('S3',(arb(3)/2-RHO0)-((Q0-1).sqrt()-1),'near corner is inside central disk')
    check0('S4',(2-RHO0)*(arb(2)/5).cos()-(RHO0-H),'piercing lower normal margin')
    def S5(t,h):
        V = 1-(h+H)*t.sin()
        return (h/t.cos()+1+V*t.tan())**2+V**2-Q0
    check2('S5',S5,[(0.0,0.4),(dn(arb(3)/2-RHO0),up(RHO0-H))],note='piercing G(t,h)>Q0')
    check0('S5a',H-RHO0*(arb(2)/5).sin(),'rho0 sin(2/5)<1/2')
    check0('S6',H-U0,'U0<1/2')
    check0('S7',H-((RHO0-H)*(arb(1)/4).cos()-H*(arb(1)/4).sin()),'B(1/4)<1/2')
    check0('S7a',T1-arb(1)/4,'1/4<t1')
    check1('S8a',lambda t:(RHO0-H)-(R0-t.cos()-t.sin()+t/2),dn(T1),0.4,note='tilt budget on [t1,2/5]')
    check1('S8b',lambda t:(RHO0-H)*(H-t*t/24)-t/12,0.0,up(T1),note='tilt budget Taylor coefficient')

    check0('S9',arb(9)/(10*SQ2)-(RHO0-H),'OWN-E exclusion with diagonal tolerance')
    check0('S10a',(2-RHO0)-arb(177)/200,'177/200<2-rho0')
    check0('S10b',arb(223)/200-RHO0,'rho0<223/200')
    check0('S10c',arb(117)/250-U0,'U0<117/250')
    check0('S11a',(2-RHO0)-(9*R0/arb(202).sqrt()-H),'linear maximizer lies left of a=2-rho0')
    check0('S11b',2*PI+7-9*(2-RHO0)-11*U0,'9a+11u<2pi+7')
    check0('S12',1-SQ2*C0-U0,'secondary separators fail')
    check0('S13',A1P+A1M-2*PI/3,'A1 forbidden arc exceeds 2pi/3')
    check0('S14',PI/2+A2M-2*PI/3,'A2 forbidden arc exceeds 2pi/3')

    def S15d(t):
        W = X0+H-4*t/5
        Wp = arb(-4)/5
        return 2*(arb(3)/2+W*t.sin())*(Wp*t.sin()+W*t.cos())+2*W*Wp
    check1('S15',S15d,0.0,0.25,note='CN theta<0: positive derivative')
    def aN(t): return H+H*t.cos()+(H+C0)*t.sin()
    def S16d(t):
        ap = -H*t.sin()+(H+C0)*t.cos()
        return 2*(aN(t)+H)*ap-arb(8)/5*(X0+H-4*t/5)
    check1('S16',S16d,0.0,PI4,note='OWN-N theta<0: positive derivative')
    check1('S17a',lambda t:-H*t.sin()+(H+C0)*t.cos(),0.0,PI4,note='a_N increasing')
    check0('S17b',aN(arb(5)/4*X0)-RHO0,'a_N(5X0/4)>rho0')
    def S18d(t):
        return -(1+H*t.cos())*t.sin()+arb(8)/5*(X0+H+4*t/5)
    check1('S18',S18d,0.0,PI4,note='OWN-N theta>=0: positive derivative')
    check0('S19a',PI/6+3*(1-A(H))/4-arb(5)/8,'u>=1/2 implies label>=5/8')
    tS = (2*(R0/SQ2-1)).asin()
    check0('S19b',arb(5)/8-tS,'N secondary: |theta|<5/8')

    def aS1(t): return H+(H-C0)*t.cos()+(H+C0)*t.sin()
    def S20d(t):
        ap = -(H-C0)*t.sin()+(H+C0)*t.cos()
        return 2*(aS1(t)+H)*ap-arb(8)/5*(U0+H-4*t/5)
    check1('S20',S20d,0.0,PI4,note='A1 OWN-S theta>=0: positive derivative')
    def S21d(t):
        return -2*(1+(H-C0)*t.cos())*(H-C0)*t.sin()+arb(8)/5*(U0+H+4*t/5)
    check1('S21',S21d,0.0,PI4,note='A1 OWN-S theta<0: positive derivative')
    def S22d(t):
        W = U0+H-4*t/5
        return 2*(arb(5)/2-RHO0+W*t.sin())*(W*t.cos()-arb(4)/5*t.sin())-arb(8)/5*W
    check1('S22',S22d,0.0,0.3,note='A1 CS: derivative positive on [0,3/10]')
    def S22v(t):
        W = U0+H-4*t/5
        return (arb(5)/2-RHO0+W*t.sin())**2+W**2-Q0
    check1('S22b',S22v,0.3,0.4,note='A1 CS: value positive on [3/10,2/5]')
    check0('S23a',aS1(arb(5)/4*U0)-RHO0,'a_S1(5U0/4)>rho0')
    check0('S23b',aS1(PI/4)-RHO0,'a_S1(pi/4)>rho0')
    check0('S23c',arb(5)/4*U0-arb(2)/5,'2/5<5U0/4')
    check0('S23d',arb(5)/4*X0-arb(1)/4,'1/4<5X0/4')
    check0('S24',H-(R0-SQ2),'E quadrant: CN impossible')
    check0('S25',H+1/(2*SQ2)-UMAX,'E quadrant: SEC+ impossible')
    check0('S26',H+(H-C0)/SQ2-UMAX,'A1 E quadrant: SEC- impossible')
    check0('S27',H+(H+C0)/SQ2-UMAX,'N SEC- and S SEC+ impossible')
    def S28d(t):
        return -2*(1+(RHO0-H)*t.cos())*(RHO0-H)*t.sin()+arb(8)/5*(H+4*t/5)
    check1('S28',S28d,0.0,PI4,note='A2 OWN-N theta>=0: positive derivative')

    def S29(t):
        a = H+t.sin()
        u = U(a)
        if isinstance(u,str): return VAC
        return (PI/2-A2M)-(t+lab_up(a,u))
    check1('S29',S29,0.0,up((RHO0-H).asin()),note='A2 OWN-S marker bound')
    def S30(t,u):
        a = H+(H+u)*t.tan()
        if (1+(H+u)*t.tan())**2+(u+H)**2>Q0: return VAC
        return (PI/2-A2M)-(t+lab_up(a,u))
    check2('S30',S30,[(0.0,PI4),(0.0,up(UMAX))],note='A2 CS in S quadrant, b>0')
    def S31(t):
        uS = H+t.sin()
        aU = A(uS)
        if isinstance(aU,str): return VAC
        lab = amin(5*uS/4,PI/6+(uS-H)/3+3*(1-aU)/4,PI/4)
        return -A2M-(t-lab)
    check1('S31',S31,0.0,up((R0/SQ2-1).asin()),note='A2 E SEC-/CS, theta>=0')
    def S32a(t,u):
        aU = A(u)
        if isinstance(aU,str): return VAC
        if u+(aU-H)*t.tan()<H: return VAC
        lab = amin(5*u/4,PI/6+(u-H)/3+3*(1-aU)/4,PI/4)
        return t+lab-A2M
    check2('S32a',S32a,[(0.0,PI4),(0.0,up(UMAX))],note='A2 E CS theta<0, b<=0')
    def S32b(t):
        return -A2M-(-t+arb(5)/4*((RHO0-H)*t.tan()-H))
    check1('S32b',S32b,dn((H/(RHO0-H)).atan()),PI4,note='A2 E CS theta<0, b>0')

    check0('S35',Q*(arb(1)/4).cos()+H-RHO0,'CE: q_E normal')
    def S36(t):
        V = 1-Q*t.sin()
        return (H/t.cos()+1+V*t.tan())**2+V**2-Q0
    check1('S36',S36,0.0,0.25,note='CE: q_E transverse')
    check0('S37',Q*(PI/12+arb(2)/5).cos()-(RHO0-H),'CW: q_W normal')
    def S38(t):
        v = 1-Q*(PI/12+t).sin()
        return Q*(PI/4-t).cos()-((Q0-v**2).sqrt()-1)
    check1('S38',S38,-0.4,0.4,note='CW: q_D normal when q_W transverse fails')
    def S39(t):
        return (arb(3)/2-RHO0)/t.cos()+H+(1-Q*(t-PI/12).sin())*t.tan()-RHO0
    check1('S39',S39,dn(PI/12),0.4,note='CW: lower q_W transverse failure infeasible')
    def aE(t):
        if t>=0: return H+H*t.cos()+H*t.sin()
        if t<=0: return H+H*t.cos()+(H-C0)*abs(t.sin())
        return H+H*t.cos()+(H-C0)*abs(t.sin())
    def S40(t):
        a = aE(t)
        if a>RHO0: return VAC
        u = U(a)
        if isinstance(u,str): return VAC
        return H-Q*abs(t.sin())-u
    check1('S40',S40,-5/12,upf(0.3),note='OWN-E: q_E transverse')
    check0('S40a',Q*(arb(5)/12).cos()+H-RHO0,'OWN-E: q_E normal')
    check0('S41a',aE(arb(3)/10)-RHO0,'a_E(3/10)>rho0')
    check0('S41b',aE(-arb(5)/12)-RHO0,'a_E(-5/12)>rho0')
    check0('S41c',aE(-PI/4)-RHO0,'a_E(-pi/4)>rho0')
    def aWneg(t): return H+(H-C0)*t.cos()+H*t.sin()
    check0('S42a',aWneg(arb(2)/3)-RHO0,'a_W(-2/3)>rho0')
    check0('S42b',aWneg(PI/4)-RHO0,'a_W(-pi/4)>rho0')
    check0('S43a',Q*(arb(2)/3-PI/12).cos()+H-RHO0,'OWN-W negative: q_W normal')
    def S43(t):
        a = aWneg(t)
        if a>RHO0: return VAC
        u = U(a)
        if isinstance(u,str): return VAC
        return H-Q*(t-PI/12).sin()-u
    check1('S43',S43,dn(PI/12),upf(2/3),note='OWN-W: q_W transverse lower')
    def S44(t):
        ulo = H-Q*(PI/4-t).sin()
        if ulo>0:
            aa = A(ulo)
            abound = RHO0 if isinstance(aa,str) else aa.min(RHO0)
        else:
            abound = RHO0
        return Q*(PI/12+t).cos()-(abound-H)
    check1('S44',S44,-up(PI/12),PI4,note='OWN-W subcase ii: q_W normal')
    check1('S45a',lambda t:H+Q*(PI/4-t).cos()-RHO0,-1/30,PI4,note='OWN-W iii: q_D normal can fail only below -1/30')
    def S45b(t):
        a = H+Q*(PI/4-t).cos()
        u = U(a)
        if isinstance(u,str): return VAC
        return H-Q*(PI/12+t).sin()-u
    check1('S45b',S45b,-up(PI/12),-1/30,note='OWN-W iii: q_W transverse upper')
    check0('S45c',Q*(PI/12).cos()-(RHO0-H),'OWN-W iii: q_W normal')

    check0('S47',(arb(3)/2-RHO0)-Q*(PI/2-arb(3)/10).cos(),'q_E not in OWN-N')
    check0('S47b',(H-C0)/(arb(2)/5)-(arb(2)/3).tan(),'q_E not in OWN-S')
    def aWpos(t): return H+(H-C0)*(t.cos()+t.sin())
    check1('S48',lambda t:(aWpos(t)+H)**2+(Q*(PI/12+t).sin())**2-Q0,5/8,PI4,note='W upper window 5/8')
    check1('S49',lambda t:H*t.cos()+(H-C0)*t.sin()-Q*(5*PI/12-t).cos(),dnf(0.17),5/12,note='q_W not in OWN-N, theta>=0.17')
    check0('S49b',(arb(3)/2-RHO0)-Q*(5*PI/12-arb(17)/100).cos(),'q_W normal excludes theta_N<=0.17')
    check1('S50',lambda t:(H-C0)*(t.cos()+t.sin())-Q*(7*PI/12-t).cos(),0.0,PI4,note='q_W not in OWN-S, theta_S<=0')
    check1('S51',lambda t:(H-C0)*t.cos()+H*t.sin()-Q*(PI/4+t).cos(),dnf(0.4),upf(2/3),note='D OWN-W: theta>-2/5')
    check0('S52a',PI/2-arb(3)/10-arb(3)/10,'E<N')
    check0('S52b',PI-arb(2)/3-(PI/2+arb(5)/12),'N<W')
    check0('S52c',3*PI/2-arb(5)/8-5*PI/4,'D<S')
    check0('S52d',2*PI-arb(5)/12-(3*PI/2+arb(2)/3),'S<E+2pi')
    check0('S53',(arb(41)/40).cos()-(RHO0-H)/(arb(5)/2-RHO0),'W/D primary-axis exclusion')
    check0('S54a',(arb(5)/12).cos()-(RHO0-H),'own moving pin normal')
    def S54(t):
        a = aE(t)
        if a>RHO0: return VAC
        u = U(a)
        if isinstance(u,str): return VAC
        return H-(1+C0)*abs(t.sin())-u
    check1('S54',S54,-5/12,upf(0.3),note='own moving pin transverse')

    if len(RESULTS)!=78 or len(SANITY)!=4:
        raise AssertionError(('obligation inventory mismatch',len(RESULTS),len(SANITY)))
    bad = [r[0] for r in RESULTS if not r[1]]+[r[0] for r in SANITY if not r[1]]
    print(f'{len(RESULTS)} scalar certificates, {len(SANITY)} identity sanity checks, {len(bad)} failed')
    return RESULTS


if __name__ == '__main__':
    main()
    sys.exit(0 if all(r[1] for r in RESULTS) and all(r[1] for r in SANITY) else 1)
