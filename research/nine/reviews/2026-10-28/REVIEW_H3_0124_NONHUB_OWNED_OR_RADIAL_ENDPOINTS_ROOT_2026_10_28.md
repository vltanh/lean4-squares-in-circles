# Complete root review: non-hub-owned side-owned or radial H3.0124 endpoints

Date: October 28, 2026. Reviewer: root.

**Root verdict: accepted at the full stated interface, without correction.**
I read the complete source and rederived its actual vertex reduction,
weak junction signs, two endpoint coordinate estimates and strict joint
angle contradiction. This is a mathematical review of all the displayed
domains, not an inference from the author's arithmetic record.

Reviewed source:

`INNER_PENTAGON_H3_0124_NONHUB_OWNED_OR_RADIAL_ENDPOINTS_EXCLUSION.md`

SHA-256:
`c72a8bc51f9c76bd5b6c2d44ad05b6e96f5c8807aab257c27baef8f5a15d5c44`.

The exact conclusion excludes both non-K-owned endpoint normals when
each endpoint either owns that normal or has two physical circle corners.
A unique-corner free endpoint remains outside this conclusion. No original
fine or coarse flag is changed by this review.

## 1. Original stars, balanced path and complete contact geometry

The source uses the original relabeling K=3 and (E1,E2,E3,E4)=(2,1,0,4).
The eight actual edges are the three consecutive boundary links, the two
K endpoint links, and HK,HE2,HE3. K and H remain unloaded degree three;
E1,E4 are loaded degree two and E2,E3 are loaded degree three. Summing
these six full equations cancels exactly those eight internal forces and
leaves all four full positive-total boundary resultants. All nine physical
units remain. No false K-E2 edge or degree-two equation at H is used.

The previously fully read balanced four-boundary-path theorem therefore
applies at its whole physical-mask scope. Its all-pairs endpoint distance
excludes equal or adjacent K vertices. Because neither selected endpoint
normal is a K axis, both actual K applications are vertices, so they are
opposite. Their distance is exactly sqrt(2), not a relaxed bound.

I checked the claimed lower-arc order against the selected physical
embedding. The interior H spoke occurs on the interior K boundary arc
between the two endpoint spokes. At a coincident endpoint it has the
same order in the disjoint physical inward tangent sectors. An actual
normal lies along a short inward segment of its neighboring square, so
its order agrees with that sector order. No new normal is selected here.

## 2. Full K3 moments, including coincident applications

In the diagonal chart p1=(x-sigma,h), p4=(x+sigma,h), the two moment
signs for every actual lower-arc port P are

    det(P-p1,n)<=0, det(P-p4,n)>=0.

I rechecked the entire side means: on the lower-left side the exact
values are -t and 1-t; on the lower-right side they have the same weak
signs. At the bottom vertex n_y<=-|n_x| gives both signs directly.
The closed side endpoints are included.

When the H port is distinct, the two full K3 torque equations directly
give nonnegative endpoint normal heights. If H shares p1, torque about
p1 first gives n4_y=0 and torque about p4 gives nonnegative total
y force at p1. In the left vertex cone, the earlier E1 normal has
at least the later H normal's y component. A positive weighted average
cannot be nonnegative if its maximum is negative. Thus n1_y>=0.
The reflected p4 coincidence gives the other endpoint result. This
checks the grouped argument without silently deleting a force.

Consequently n1=(-b1,a1), n4=(b4,a4), 0<=ai<=bi, bi>=sigma is
valid at every actual weak junction. The original non-K-axis boundaries
are strict; retaining the weak enlargement only strengthens the scope.
The actual lower-arc path is counterclockwise. The complete degree-free
boundary moment theorem then supplies det(p1,n1)>0 and det(p4,n4)<0.
Neither internal loaded body needs a two-force hypothesis for that use.

## 3. The actual inward points and full endpoint properness

For a square, any inward unit normal at its support application has its
whole inward unit segment in the square. At an owned side this is the
unit normal segment; at a vertex, the two nonnegative unit components
are individually at most one. This is the precise radius-free lemma
used from the radial bridge source.

If x>=sigma, the real point p4+n4 has x coordinate at least 3/sqrt(2),
whose squared excess over the largest allowed R is 47/256. The reflected
argument excludes x<=-sigma. Therefore X1=sigma-x and X4=sigma+x are
strictly positive and sum to sqrt(2). The moment signs then imply h>0.

Both true loaded-two endpoints have their actual boundary-path neighbors.
The complete properness input gives qi=pi+ell_i ni=t_i Fi with ell_i>=0,
t_i>0 for either physical circle mask and all individual weights. It is
used only to put F1 strictly upper-left and F4 strictly upper-right.
No concurrence is assumed to lie inside a two-corner square.

## 4. Entire endpoint-owned slider and the scalar inequality

For the left endpoint I rederived the orthogonal coordinates

    P=(-X,h), n=(-b,a), k=(-a,-b),
    N=P.n=bX+ah>0, K0=-P.k=bh-aX>0.

Its real owned-side shape is P+[0,1]n+[-rho,1-rho]k. The original
singleton convention has rho in the relative interior; the calculations
retain even both enlarged endpoints. Since F.k<0, its center's k
coordinate cannot be positive. All its physical far corners are on the
outer n face, and with Z=K0+rho>=1/2 the full relations are exactly

    R^2=(N+1)^2+Z^2,
    c_E=(N+1/2)n-(Z-1/2)k,
    X=bN-aK0>=bN-aZ.

The equality Z=1/2 is the full two-physical-corner mask and does not
force equal weights. The displayed center has nonnegative y, and its
x coordinate is at most -X-(b-a)/2<0. Thus its angle parameter delta
is in [0,pi/2), while phi=atan(a/b) lies in [0,delta].

Putting v=delta-phi, r0=d+1/2, the exact circle equation gives

    (r0-r)(r0+r+1)=r(cos(v)+sin(v)-1).

For v in [0,pi/2], r<=r0. Bounding the right side by r sin(v)
and using r0+r+1>2r gives r>=r0-sin(v)/2, including v=0.
Substitution into X yields the claimed parenthesis
(1+sin(delta)cos(delta))cos(phi)+sin(delta)^2 sin(phi).
Cauchy's inequality bounds it by sqrt(1+2sc+s^2). The exact difference
of squares between c+6s/5 and that quantity is (2/25)s(5c-7s).
It is nonnegative throughout delta<pi/6 because tan(delta)<1/sqrt(3)<5/7.
Thus X>=d cos(delta)-(3/5)sin(delta) on the complete required interval.

This reproduces the operative scalar proof instead of importing a fan
hub, a missing positive spoke, or a support-distance hypothesis.

## 5. Every free endpoint with two physical circle corners

The actual two-corner square has shape [d,d+1]e+[-1/2,1/2]Je. A
physical circle corner cannot be a shared contact, so its free incoming
application is P=d e+epsilon Je/2. Its inward vertex normal has the
strict form A e-epsilon B Je, A,B>0. The origin moment is exactly
-epsilon(dB+A/2). The positive left endpoint moment forces epsilon=-1.

I checked the lifted angles without identifying the normal, center and
resultant. The selected K cone puts n in [3pi/4,pi]. The inward normal
is counterclockwise from e by an angle in (0,pi/2); P is clockwise
from e by an angle in (0,pi/2). In the resulting lift, P's known strict
upper-left angle forces e strictly into that quadrant as well. Hence

    X=d cos(delta)-(1/2)sin(delta)
      >=d cos(delta)-(3/5)sin(delta).

All original circle weights remain free, including either zero weight.
This is a geometric shape/moment argument and never replaces the full
circle resultant by a radial vector. Reflection gives the right endpoint.

## 6. Actual lower arc, complete angular domain and final contradiction

The two actual centers are upper-left and upper-right. Their original
counterclockwise three-link path uses the complementary lower arc of
length pi+delta1+delta4. This is the physical embedding order already
checked; alternatively the opposite upper arc would put all four ordered
positive-total resultants in an open half-plane, contradicting their sum.
The ordered disjoint center/corner intervals preserve the same choice.

Each real boundary link has center angle less than theta=acos(9/25).
Thus delta1+delta4<alpha=3theta-pi. The exact triple-angle value is
cos(alpha)=13959/15625, giving 0<alpha<pi/6 and sin(alpha)<9/20.
This supplies the whole angular range before the scalar estimate is
used. There is no circular assumption that either delta was small.

On [0,alpha], g(t)=d cos(t)-(3/5)sin(t) is positive, decreasing and
concave. For fixed argument sum, the minimum of the two-term sum is
at its endpoint pair. The strict sum bound therefore gives

    X1+X4 >= g(delta1)+g(delta4)
            >g(0)+g(alpha)>1431/1000>10/7>sqrt(2).

I rechecked d>9/10 on the complete declared radius interval. The exact
final rational reserves are 17/7000 and, for the squared radical
comparison, 2/49. This contradicts the unchanged K diagonal identity.
All weak angular endpoints and all actual side means have been retained.

## 7. Arithmetic, literal input pins and exact remaining scope

The independent root calculation is
`/tmp/pr11_root_h3_0124_nonhub_owned_radial_checks.py`; its JSON record is
`/tmp/pr11_root_h3_0124_nonhub_owned_radial_checks.json`.
It verifies all eight literal input pins, nine strict Fraction reserves,
the triple-angle identity and the complete scalar square expansion.
The geometric proof above supplies the full continuous-domain checks.
No numerical pose sample or compilation is involved.

I accept the entire stated owner/mask interface unchanged. The remaining
neither-K-owned row has at least one genuinely free endpoint with a unique
physical circle corner. Its other application may have a variable shared
side mean; this review does not discard that row using a fixed-point
normal argument. A separate complete independent review remains required
before this source is entered into an accepted checkpoint. The original
H3.0124 flag, other load masks, all shared metadata and remote state remain
unchanged.
