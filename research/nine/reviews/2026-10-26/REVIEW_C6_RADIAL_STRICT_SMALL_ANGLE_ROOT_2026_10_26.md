# Root review: small radial-port angles exclude three strict feature types

Date: October26,2026.

**Verdict: PASS for SIX_CYCLE_RADIAL_STRICT_PARTNER_SMALL_ANGLE_EXCLUSION.md.**
The local theorem excludes A,M,O at a strict unique endpoint with
actual radial angle<=2/7 and retains T. Its low-turn join is conditional
on the actual adjacent-port distance premise. No original parent
gate closes, and no computational certificate, Lean or CI is used.

## 1. Constants, actual frame and the A/M alternatives

For2<=R<=sqrt(1105)/16, the stated positive-square comparisons give
187/200<d<61/60. I checked both squared reserves. The sine/cosine
bounds on the complete interval0<=beta<=2/7 give
w=1-d*cos(beta)+(1/2)*sin(beta)<2411/9800 and
h=d*sin(beta)+(1/2)*cos(beta)<39/50.
The polynomial upper bound for h increases on the whole interval;
its endpoint and the displayed strict rational reserve are correct.

The A exclusion uses the actual adjacent-port distance one and the
previously reviewed whole-domain near-corner theorem beta>1/2.
No contact label alone is substituted for a distance condition.

For M, I checked Sections1--2 of the cited shared-means source.
Only its local strict-turn/own-axis calculation is used: the actual
mean yields a>b>1/2 and P=(a-2)*v+tau*b*u with G=v.
It does not require a mean at the other unique body. Every actual
mean endpoint stays in that local calculation. Hence a=1+w<7/5,
contrary to a>R/sqrt(2)>=sqrt(2). All comparison signs and the
1509/9800 rational reserve are valid.

## 2. Independent reconstruction of the full O identities

The original O applications are Q=(a-1,b-1) and T=(a-1,b),
a>b>1/2. With the original proper concurrence, put
X=1-t*a,Y=1-t*b,L=sqrt(X^2+Y^2),G=(x,y)=(X,Y)/L.
The exact radial-port invariants are P*G=w-1 and det(P,G)=h.
Since P=(w-1)*G-h*JG and Q=P+G, I independently obtained

    a=1+w*x+h*y,   b=1+w*y-h*x.

For m=x+y,n=y-x, expansion of a^2+b^2=R^2, using
w^2+h^2=1+r0^2-2*(1-w) and R^2-r0^2=2*d+1, gives

    w*(m+1)+h*n=d.

From the linked actual concurrence coordinates I also derived
n=t*(a*y-b*x)=t*(n+h), and
L=(h*m-n*w)/(h+n). The numerator and denominator signs are
not inferred from independent relaxed variables.

The t=0 endpoint is initially retained. Then n=0,m=sqrt(2),
and the circle identity contradicts the uniform w bound, so it is
excluded by proof. Thus0<n<1 in the remaining comparison.
The actual strict return turn has dot product
-X^2+Y*(1-Y)=L*y-L^2<0, equivalent to L>y. Substitution gives
h*x>n*(w+y). This is the precise strict-turn premise and is not
applied to a low-turn O-shaped endpoint.

## 3. Whole-domain scalar contradiction

The bounds give h<d. If w<=0, the exact circle identity would
give d<=h*n<h<d. Thus w>0 is proved before dividing or dropping it.

If n>=3/7, the ratio x/y=(sqrt(2-n^2)-n)/(sqrt(2-n^2)+n)
decreases with n and is less than13/25 at the lower endpoint,
using sqrt(89)<19/2. The strict-turn inequality would then give

    n<h*x/y<(39/50)*(13/25)<3/7,

with the stated exact201/8750 reserve. Therefore n<3/7.
Together with m+1<=1+sqrt(2)<17/7, the exact circle equation gives

    d<(2411/9800)*(17/7)+(39/50)*(3/7)
      =187/200-111/34300<187/200<d.

I checked the rational identity. This excludes every O parameter
allowed by the original equations, including the initially retained
t=0 boundary. No radius, force, concurrence or angle interval is sampled.

## 4. Exact feature and low-turn join

The strict A/M/O/T cover leaves T after the three exclusions.
In the complementary low-turn domain, the previously reviewed turn
sum gives alpha+beta<=pi/4. An actual adjacent S-incident port at
the low endpoint gives alpha>1/2 and beta<2/7; therefore all its
strict A/M/O partners are excluded simultaneously.

This covers every low-table row in which that particular original
S-incident application is adjacent, including an original mean already
at that endpoint without relabeling it. It supplies no adjacent-distance
premise for an arbitrary interior mean or opposite vertex.
The low-adjacent/T residue, all other low placements, full two-owner
mean row, every true channel/slider and all nine original physical
squares remain. No original graph gate, coarse cell or sharp theorem
is claimed complete.

