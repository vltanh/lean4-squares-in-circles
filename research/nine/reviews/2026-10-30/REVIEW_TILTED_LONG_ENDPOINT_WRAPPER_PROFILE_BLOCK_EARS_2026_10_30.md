# Tilted long-endpoint return profile: complete independent review

Date: October 30, 2026 UTC.

**Verdict: PASS at the full stated scope. No repair requested.**

Reviewed final frozen source:
`TILTED_LONG_ENDPOINT_RETURN_WRAPPERS_OBEY_THE_SHARP_SECTION_PROFILE_2026_10_30.md`.

Length: 19,575 bytes. SHA256:
`c7553b418c64c12bda69bcccb565e6f5d7cdd1613dbb8eecfe282ce6126a26c3`.

This review concerns that final source, including the explicit endpoint
positive-load argument in Section 5. It does not concern an earlier
provisional hash. I read the entire source, reconstructed the complete
geometric proof and original-force caller, and re-read the exact
coupled-height estimate in the expanded-cover source. All three stated
frozen input pins match.

I authored an earlier independent tangent proof for aligned endpoints,
but this tilted geometric parameter proof and its original-normal
caller are another author's work. In particular I checked the new
long-chord estimate rather than importing the aligned outer-corner
constraint into a tilted pose.

## 1. Geometric domain and actual entry bounds

The side-wrapper theorem explicitly assumes17/4<=q<=Q, actual parameters
a^2+b^2=1, a>399/400, 0<b<7/100, |s|<1/60,
-9/16<=t<-1/2, and the unchanged occupied chord constraint
(2+|s|)^2+t^2<=q. It puts p=(x,f)=(s+1+b,t+a), k=5/4-f,
d=sqrt(Q-(f+1)^2)-1. C is an actual physical boundary unit, with
the original support chart

    C=p+[0,1](-alpha,beta)+[r-1,r](beta,alpha),
    alpha,beta>0, alpha^2+beta^2=1, 0<=r<=1.

No whole-square floor, force equation or endpoint degree is inserted
into this geometric theorem. The slider is the complete closed
interval, including both geometric endpoints.

Direct substitution gives
87/200<f<1/2, 59/60<x<163/150, 3/4<k<163/200<7/8,
and7/16<d<51/100. The last upper comparison follows from the exact
positive square reserve3667/160000 for g(287/200)<151/100.
All uses of g in the proof have positive arguments below sqrt(Q).

## 2. Actual section existence and the two true edges

The contact point p has height below1/2, so C's bottom support is
below5/4. If its top were at or below5/4, the actual top vertex
would give beta+r alpha<=k<7/8. Hence
alpha>sqrt(15)/8>7/16 and
r beta<=beta(k-beta)/alpha<=k^2/(4alpha)<7/16.

The full chart would then lie in the strict/closed box

    -1/2<X<25/16, -5/8<Y<=5/4.

The x lower bound uses x-alpha-(1-r)beta>x-sqrt(2)
>59/60-17/12=-13/30. The x upper bound uses
25/16-(163/150+7/16)=23/600>0. The y lower bound uses
f-alpha>87/200-1>-5/8. Every point of this entire box has squared
norm strictly below1025/256, whereas q>=17/4 differs by63/256.
This contradicts an actual circle contact of C. Thus the line crosses
strictly between its two horizontal supports and the section is real,
nondegenerate and interior apart from its endpoints.

Solving the two unchanged own-coordinate strips at height5/4 gives

    ell=max(ell_1,ell_2),
    ell_1=x+(r-1-alpha*k)/beta,
    ell_2=x+(beta*k-1)/alpha.

Both are lower bounds on the actual x interval, with positive divisors.
Section existence was proved before identifying their maximum with
the actual endpoint, so an empty or extended supporting-line slice
is not used.

## 3. Upper-corner control of the first edge

The point P=p+n+r u is an actual upper corner. Its original own
coordinates satisfy
E=n.P=1-alpha*x+beta*f and
beta ell_1=u.P-1-alpha*(5/4). Corner containment gives
u.P<=sqrt(Q-E^2), with a real radicand even if that coordinate is
negative. Set T=1+alpha*(5/4)+beta*d>0.

I expanded the identity with alpha^2+beta^2=1 and
(d+1)^2+(f+1)^2=Q. It is exactly

    (T^2+E^2-Q)/alpha
      =2(z-x)+2(zd-xf)beta
       +alpha[z^2+x^2-d^2-f^2-2(d+f)/(1+beta)].

The conversion uses beta-1=-alpha^2/(1+beta), with no sign change.
The stated entry bounds give2(z-x)>49/150 and
zd-xf>=17/4800>0. The bracket is strictly greater than

    25/16+(59/60)^2-(51/100)^2-1/4-2(51/100+1/2)
      =-59/90000.

Multiplication by0<alpha<=1 preserves the uniform lower bound
-59/90000, including the case of a positive bracket. Hence the
whole quotient is greater than29341/90000>0. Since T>0,
sqrt(Q-E^2)<T, and therefore ell_1<d. This proof uses an actual
corner and covers every original angle and slider at once.

## 4. Long-chord control of the other edge

Put D=x-d>0. The actual occupied chord gives

    x+1=2+s+b<=b+sqrt(Q-t^2)=b+g(a-f).

With A=399/400<a and a-f=-t>0, strict decrease of g gives

    D<7/100+g(A-f)-g(1+f).

This is a comparison of the original coordinates. In particular the
false aligned constraint(x+1)^2+(1-f)^2<=q is never asserted for
a tilted endpoint.

For S(f)=g(A-f)+g(1+f), differentiation gives
S'(f)=(A-f)/g(A-f)-(1+f)/g(1+f)<0. The argument Y/g(Y)
is strictly increasing, and A-f<1+f throughout the closed floor
interval. At f=1/2,
S(f)>g(1/2)+g(3/2)>161/80+23/16=69/20;
the positive radical reserve is13/800.

Rationalizing the difference therefore yields

    D<L(f)=493/6900+(80/69)f.

The use of1+A<2 and1-A=1/400 has the correct adverse direction.
The function L(f)^2+(5/4-f)^2 is convex, so its maximum on the
full closed interval[87/200,1/2] is at an endpoint. I recomputed
both exact entries:

| f | L(f) | Quadratic value | Reserve below one |
| --- | --- | --- | --- |
| 87/200 | 3973/6900 | 7585357/7617600 | 32243/7617600 |
| 1/2 | 4493/6900 | 23483837/23805000 | 321163/23805000 |

Both reserves are positive. Thus D^2+k^2<1 on the entire actual
domain. Cauchy--Schwarz gives alpha D+beta k<1, which rearranges
to ell_2<d. Together with the first-edge result this proves the
complete strict side-wrapper profile.

## 5. Complete original contact-type cover

For a tilted physical endpoint B, the source retains vertices
q_0,q_0+u_B,q_0+v_B,q_0+u_B+v_B with
q_0=(s+1,t), u_B=(a,-b), v_B=(b,a), and p=q_0+v_B.
It assumes the actual original contact normal into the boundary
neighbor is strict northwest. Its geometric theorem must cover
both a neighbor vertex and a neighbor-side interior; it does.

The inward-own-face lemma is printed completely. In the outward own
frame[kappa-1,kappa] times[lambda-1,lambda], a neighboring unit
on the opposite side has a maximal-x vertex on that face. This
also holds for a shared side, because two overlapping length-one
closed intervals contain an endpoint of the neighbor's interval.
The adjacent corners have squared norm at most
q-2kappa+2lambda+2, and the opposite corner at most
q-4kappa+2lambda+5. Both are strictly below q under
kappa-lambda>1, lambda>=1/2; the contact vertex is also strictly
inside. Thus a physical boundary neighbor cannot occupy that
supporting halfplane.

The exact actual own coordinates of B obey
P_B>35541/24000 and |T_B|<401/3000, so
P_B-|T_B|>32333/24000>1. These follow directly from the stated
parameter interval; |a*t+1/2|<=1/16 is valid at the closed lower
t endpoint and at every a in the stated range. Hence the full
face lemma applies after the allowed own-axis reflection. It
excludes the common direction-u_B, including contact at a face
endpoint; it does not indiscriminately exclude the upper-inner vertex.

If p is a neighbor vertex, its minimizing normal cone and B's
maximizing normal cone are two closed arcs of the same length pi/2.
Their nonempty intersection at the original normal implies that an
endpoint of B's cone lies in the neighbor cone. Otherwise the second
equal-length arc would be strictly contained in the first's interior.
The endpoint-u_B is impossible by the face lemma, so v_B also
minimizes on the neighbor at p. Combining the original n with v_B,

    alpha*v_B+b*n=(0,alpha*a+b*beta),

gives a positive vertical minimizing direction. Therefore the actual
whole neighbor lies above y=f. This is a genuine floor conclusion,
not a replacement of the original force normal. The complete floor
theorem supplies its section and profile, strict for any nonaligned
neighbor.

If p is not a neighbor vertex, it is in the relative interior of an
actual side. The original common normal is then that side's unique
inward normal, giving precisely the full side chart above with
0<r<1. The strict side-wrapper theorem applies. The closed-slider
geometric proof already retains both endpoints. These alternatives
exhaust every actual contact and establish the physical profile
without a fictitious horizontal side on B.

## 6. Full original-force caller and both circle masks

The source separately states a whole-channel caller with genuine
unloaded U,V, full-degree-two endpoints A,B, and actual boundary
return neighbors wholly above the long axis. It proves rather than
assumes that A,B have positive total circle load: a zero-load B
would propagate the common normal through three internal bodies
U,V,B, giving endpoint center projection at least four, contrary
to the universal center bound. Reflection handles A. This argument
uses the complete actual endpoint stars and no angular balance.

The frozen contact-locus theorem then supplies the tilted endpoint's
actual lower-inner long mean, upper-inner return vertex, t<-1/2,
and the complete physical circle mask. The long gap gives endpoint
center distance at least three; at least one center has radius
at least3/2, and its actual farthest-corner inequality gives
q>=17/4. This supplies the geometric theorem's lower radius window.

For a tilted endpoint the possible physical circle corners are
z_-=q_0+u_B and z_+=q_0+u_B+v_B. At negative transverse own-center
coordinate only z_- is on the circle; at zero both original circle
atoms remain. The full resultant has m_x>0 and m_y<0. The latter
is a total-force consequence and is not assumed for each atom.

I checked the force/moment elimination. The return line through p
meets the original y=t line at x_0=t*m_x/m_y. The quotient m_y/m_x
is a convex combination of the two original corner slopes, weighted
by their positive x coordinates and original nonnegative weights.
It is at least(t-b)/(s+1+a). Both this lower slope and the actual
resultant slope are negative. Since t<0, the function r->t/r is
increasing there, so
x_0>=t(s+1+a)/(t-b), with the stated direction.

Writing tau=-t and X=s+1 gives the original normal quotient

    -n_x/n_y >= [tau(a-b)-b(X+b)]/[a(tau+b)].

The numerator is positive. Replacing a in the denominator by one
decreases the quotient. The remaining expression increases with tau,
decreases when b or X increases, and increases with a-b. Thus
a-b>37/40, b<17/240, tau>1/2 and X<61/60 give exactly
7401/10960>2/3, with reserve283/32880. The squared comparison
for a-b has reserve19/2880. This proves a strict global inward/up
normal over both complete physical circle masks.

The adjacent-cycle join must observe the caller boundary: its B--W
neighbor may be circle-clear, so the two-boundary-return whole-channel
caller is not invoked wholesale there. The printed slope calculation
itself is local to the endpoint being profiled. At tilted A, an
adjacent caller can supply the actual vertex, t, full equations and
two-circle mask from its existing endpoint reduction, reproduce the
reflected local calculation, and then apply the geometric profile.
Alternatively it can supply the needed strict global normal directly.
The source's final paragraph of Section 5 preserves this distinction.

## 7. Exact coupled floor budget and remaining obligations

I re-read the expanded-cover source's full coupled-height derivation.
Its parameter is exactly E=(w_A+w_B-2)/2, where w_i is the actual
horizontal width of the endpoint. It proves0<=E<1/30 and

    |y_A|+|y_B|<=1/8-E+(320/39)E^2.

For a square the vertical and horizontal widths agree, regardless of
the sign of its tilt. When the original endpoint center heights are
nonpositive, its actual highest horizontal support is
f_i=y_i+w_i/2. Therefore their sum is at least
7/8+2E-(320/39)E^2. For a tilted endpoint,
y_B=t+(a-b)/2 and w_B=a+b, so this actual height is exactly t+a,
as used throughout the profile proof. For an aligned endpoint it is
y_i+1/2. The excess is positive whenever E>0, since
(320/39)E<32/117<2.

This is a common horizontal-section profile at actual endpoint
heights; no endpoint is rotated into an independently convenient
floor. Any later assembly still needs an actual section order and
its own occupied-width or separation hypothesis. Neither a set gap
nor a whole adjacent/five-load cycle exclusion is asserted solely
from this profile theorem.

All exact arithmetic checks were rational identities or fixed radical
comparisons in the displayed continuous proof. No numerical pose
search, parameter mesh, original mean or normal replacement, force
deletion, physical-circle mask reduction, original ledger mutation,
Lean/Lake build or CI execution entered this review.
