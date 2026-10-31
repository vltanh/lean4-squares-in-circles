# Independent review of the whole C6 doubly shared channel exclusion

Date: October 25, 2026.
Reviewer: root, independently of the author.

**Verdict: PASS for the entire saved theorem and its physical contact-type scope.**
The result excludes every original side transmitter with genuine shared
interfaces at both loaded ends. It imposes a matching restriction on the
remaining shared interfaces. It does not close the all-unique/shared C6
gate or prove the remaining completion capacity.

## 1. Frozen sources and verification

The complete mathematical source reviewed is:

    SIX_CYCLE_DOUBLE_SHARED_CHANNEL_EXCLUSION.md
    SHA256 b4d1e06fdaabd78ae6994d05f7916f5f864ddd8dece22b399cb968147c2f6c60

Its exact checker and full certificate are:

    SIX_CYCLE_DOUBLE_SHARED_CHANNEL_CHECK.py
    SHA256 608ab8a1bdd12f56e349710328dd304c1b050a2b7316c73f0119cdf4825231b7
    SIX_CYCLE_DOUBLE_SHARED_CHANNEL_CERTIFICATE.json
    SHA256 d37478e34494ff0a6de0e92cd9a9db8e55f3412430a0a14efef433ad71d26de8

I read the entire saved proof and checker, reconstructed the geometric
normalization, equal-circle linear system, original loaded torque and
global rational-to-polynomial identity, and checked the complete angle
parameterization. I then ran the exact checker in an independent output
directory. It passed all 209 coefficient inequalities, the full polynomial
factor identity, the complete Bernstein inverse and every exact floor.
Its regenerated JSON was byte-for-byte identical to the saved certificate.

The four exact parameter-point checks in the checker are supplemental
consistency checks. They are not a proof of the rational normalization:
that normalization is the global algebraic identity verified below.
No sampled sign or numerical extremum is used.

The accepted original scope is supplied by
SIX_CYCLE_UNIQUE_STRICT_TURN_AND_SHARED_NORMAL_FORM.md and
SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md. The matching interpretation is
checked against the actual incoming/outgoing rows of
SIX_CYCLE_SHARED_SUPPORT_FUNCTIONAL.md, Section 3.

## 2. Complete original geometry

All three original loads are physically unique-circle-corner squares,
all three transmitters are true unloaded degree-two side channels, and
all three additional packing squares remain present. No load, application,
transverse parameter, multiplier or physical mask is changed.

A doubly shared horizontal channel forces both endpoint frames to be
parallel. The accepted endpoint-center half-planes and physical unique
circle masks give the displayed a,b,c,d>1/2, not merely nonnegative
coordinates. The side-channel reserve is exactly one, so a+c=3.
Both original shared means at height h remain free within their actual
intervals.

At either endpoint load the other interface cannot be shared. The
positive vertical component of its actual circle load and the strict
turn select its bottom inner vertex and the displayed directions
(cos(alpha),-sin(alpha)) and (-cos(beta),-sin(beta)).
The complete domain is alpha,beta in [pi/4,pi/2), with
pi/2<alpha+beta<=3pi/4. Neither weak pi/4 endpoint is discarded.

I independently reconstructed the support inequalities for Q-P.
They force Delta_x>0 and the side direction
beta-pi/2<=phi<=pi/2-alpha. The inward side normal points downward;
an upward inward normal is incompatible with the actual support
directions and the strict sum of angles. Thus cos(phi)>=1/sqrt(2).

The source's trigonometric bound cos(alpha)+cos(beta)>1/sqrt(2)
is uniform. Its possible equality requires a forbidden pi/2 endpoint.
It gives an actual chord length strictly between zero and sqrt(2)-1.
The two applications therefore cannot both be vertices. The original
at-least-one-vertex conclusion leaves exactly one interior application.
An axis-normal interface at that interior point is genuinely shared,
including when the transmitter mean is its own endpoint. The other
interface is a singleton by the accepted at-most-one-share theorem.

The left-right reflection now stated explicitly as reflection across
the vertical axis merely interchanges B and C and places the shared
application at Q. It does not alter any actual contact choice.

## 3. Equal-circle and true torque identities

In the actual orthonormal chart e=(v,-u), f=(-u,-v), with
u=cos(beta), v=sin(beta), the two directions into the third load T are

    (S0,-C0), (0,1), with S0=sin(alpha+beta)>0, C0<0.

Their strictly positive force sum has two positive components, so
T's actual unique circle corner is (A,B0), A,B0>1/2. Its actual
applications are exactly (A-1,B0-1) and (A-1+ell,B0-1).
I derived the other two circle-corner differences in the global
frame and took their scalar products with e,f. This gives the
displayed p,q1,r1,s1 without changing the original origin.

Equal radii yield the two linear equations in A,B0.
On the actual domain p>=2+1/sqrt(2), s1>=3,
1<=q1<=2+1/sqrt(2), r1<=1. Consequently

    Delta=p*s1-q1*r1>=4+sqrt(2)>0.

This positivity is needed on the physical domain only. The larger
polynomial rectangle contains nonphysical chord parameters; no
positivity of its extended determinant is silently assumed.

The true force magnitudes follow from the two component equations
at T, retaining its original positive circle load kappa:

    mB=kappa*A/S0,
    mC=kappa*(B0+A*C0/S0).

Substituting them in its actual origin-moment equation gives

    F=S0*(A-(1-ell)*B0)+ell*C0*A=0.

I independently expanded this identity. The chart reverses orientation,
which reverses all planar determinants together and leaves the zero
moment equation unchanged. No fictitious degree-two equation on another
body is used.

## 4. Whole-domain polynomial certificate

Put k=sqrt(2)-1 and use the exact square [0,1]^2 map in the source:

    t=k*x, H0=1+k^2*x, j=k*(1-x)*y,
    alpha=pi/4+2*atan(t),
    beta=pi/4+2*atan(j/H0).

The identity (k-t)/(1+k*t)=k*(1-x)/H0 shows that this map covers
the entire closed angular triangle alpha,beta>=pi/4,
alpha+beta<=3pi/4. The added boundaries are valid enlargements.
The half-angle trigonometric substitutions give precisely Da,Dw,
ca,sa,U,V,S,C,En in the source. In particular Da,Dw,V are positive.

With the displayed common denominator T0=Da*Dw*V, I independently
checked all four exact substitutions

    (p,q1,r1,s1)=(P,Q,T,W)/T0,
    ell=En/(Da*V),
    Delta=D/T0^2,
    (A,B0)=(An,Bn)/(2*T0*D).

It follows globally, wherever these physical denominators are defined,

    F=NF/(2*Da^3*Dw^2*V^2*D).

The exact polynomial division in the checker verifies the full identity

    G=-NF/(Da*Dw^2*V),

with zero remainder and equality after remultiplication. Combining
the preceding two identities gives the complete normalization

    G=-2*Da^2*V*D*F.

This is a whole algebraic identity; isolated parameter-point checks
are not used to infer it. On the actual domain D>0 follows from
Delta>0 and T0>0, so its sign is legitimate.

I checked the exact Q(sqrt(2)) implementation: field inversion uses
the rational norm; the sign decision for opposite rational and
irrational parts correctly compares their squares; sparse polynomial
arithmetic retains exact Fraction coefficients. The tensor Bernstein
formula and its full inverse have the correct binomial factors and
cover every coefficient of the bidegree (18,10) polynomial.
All 209 saved coefficients are proved strictly greater than 5/2 by
exact field comparisons. Their weighted Bernstein sum therefore
proves G>5/2 on the entire closed square.

It follows that F<0 at every actual candidate, contradicting the
unchanged true T2 torque F=0. This excludes the whole double-share
contact type before any completion-square placement is used.

## 5. Exact consequences and limits

The prior strict-turn result allows at most one genuine share per
loaded square. The new theorem allows at most one per transmitter.
Thus the remaining shared interfaces form a matching in the original
alternating six-cycle. If there are three, they cover all three loads
and all three transmitters and must be one of its two perfect
matchings. The actual incoming/outgoing support-functional rows
give respectively all chi_i=0 or all chi_i=1.

This does not set any remaining chord length to one, select a
preferred shared mean, erase an endpoint, or fix a transverse
transmitter position. The one-, two- and three-share completion
capacity problems remain open. No original gate is ticked, no new
ID is introduced, and no unrestricted radius or equality theorem
is asserted. No Lean compilation or CI was run.
