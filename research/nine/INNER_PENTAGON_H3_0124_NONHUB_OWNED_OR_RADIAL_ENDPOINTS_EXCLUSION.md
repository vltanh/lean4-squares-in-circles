# The non-hub-owned H3.L0124 endpoints cannot both be side-owned or radial

Date: October 28, 2026. Author: hexagon.

**Status: complete hand exclusion of the stated original endpoint family,
frozen for full independent and root review.** This is a partial owner/mask
exit for the original H3.L0124 family. It does not declare that family or
its graph parent closed.

All nine actual unit squares, all original forces, physical circle masks,
individual zero corner weights and actual side means remain. The two
unloaded bodies keep their complete degree-three equations. In particular
the interior body is not contracted to a transmitter or removed to make
the other body a four-spoke fan hub.

## 1. Original graph, full loads and the exact theorem

The exterior pentagon is 0--1--2--3--4--0 and the physically interior
clear body H has the three original spokes H0,H1,H3. The positive circle
loads are exactly {0,1,2,4}. For this proof write

    K=3, E1=2, E2=1, E3=0, E4=4.

The complete positive edges are

    E1--E2--E3--E4, K--E1, K--E4,
    H--E2, H--E3, H--K.

Thus K,H are unloaded of true degree three; E1,E4 are loaded of true
degree two; E2,E3 are loaded of true degree three. The actual exterior
face is K,E1,E2,E3,E4,K, with all three H spokes on its interior side.
The original circle origin remains O=0 throughout. Work in the whole
declared range 79/40<=R<=sqrt(1105)/16.

Let p1,p4 be the original K endpoint applications and n1,n4 the original
unit normals directed from K into E1,E4. Assume neither n1 nor n4 is
a side axis of K. At each endpoint assume, independently, that either:

* its actual normal is a side axis of that endpoint square; or
* that endpoint has two physical containing-circle corners.

The second alternative permits a genuinely free vertex/vertex normal
and either individual circle weight to vanish. It does not require the
whole resultant to be radial.

**Theorem.** This entire original endpoint family is impossible.

The excluded family includes both endpoint-side-owned contacts, one
endpoint-side-owned contact with the other physically radial/free, and
two physically radial/free contacts. The remaining non-K-owned feature
is a free endpoint having a unique physical circle corner; at least one
such endpoint must be present outside the theorem's hypotheses.

## 2. Opposite K vertices and the complete inner-spoke order

Sum the six full body force equations. All eight original pair forces
cancel with their equal opposites, leaving

                       F1+F2+F3+F4=0.                 (1)

Each Fi is the full nonzero positive-total circle resultant, with all
of its individual weights retained. The actual loaded boundary path
E1--E2--E3--E4 and FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md therefore
give |p1-p4|>1 for every actual endpoint application pair on K.
Since the two present normals are not K axes, both applications are
K vertices. They must be opposite vertices.

Rotate the whole physical packing, leaving O fixed, and if necessary
reverse the original graph-preserving reflection to write

    sigma=1/sqrt(2), c_K=(x,h),
    p1=(x-sigma,h), p4=(x+sigma,h).                  (2)

Reflect vertically so the actual HK application lies on the lower K
arc between these vertices. This is the arc on the interior side of
the actual exterior pentagon. To justify its use at weak junctions,
use the selected physical center/contact embedding. H is inside that
exterior face, so its K spoke occurs between the endpoint spokes on
the interior arc. If its application coincides with p1 or p4, its
unchanged tangent sector is after E1 or before E4 in that same arc.
The distinct incident unit tangent interiors are disjoint. Actual
normal directions, which point along short inward segments of their
neighbor units, retain this physical sector order. No normal is chosen
again and no coincident original application is discarded.

For any other lower-arc K application P with actual outward normal n,
the two exact signs are

    det(P-p1,n)<=0, det(P-p4,n)>=0.                  (3)

For example, on the lower-left side P=p1+t*(sigma,-sigma), its axis
normal is (-sigma,-sigma), and the determinants are -t and 1-t.
The lower-right side has the same two signs. At the bottom vertex
the normal satisfies n_y<=-|n_x|, giving (3) directly. The side
endpoints and the whole actual mean intervals are included.

Group the actual K forces at either endpoint if HK coincides there.
The full K3 moments about p4 and p1 give respectively a nonnegative
y component for the left and right groups. Within the left group
the endpoint n1 comes first and its y component is at least that of
any later lower-arc normal; within the right group n4 comes last
and has at least the earlier components. Positivity of every actual
group magnitude consequently gives

    n1=(-b1,a1), n4=(b4,a4),
    0<=ai<=bi, ai^2+bi^2=1, bi>=sigma.             (4)

If HK is at neither endpoint, this is just (3) in the full three-force
moment without grouping. If a group has two forces, the same physical
sector order just established supplies the stated monotonicity inside
the left or right vertex normal cone. The non-K-owned hypotheses make
the K-side-axis boundaries strict, but the weak enlargement in (4)
is sufficient for every later estimate.

The occupied lower K-arc order is counterclockwise from p1 to p4.
The original exterior pentagon and the occupied H branches to E2,E3
preserve this order when continued through their actual circle spokes.
Equivalently, cut the physical annulus between the exterior cycle and
the circle at an endpoint spoke: disjoint strands preserve the linear
order E1,E2,E3,E4. The compatible junction routing can avoid the
finitely many circle spokes. Thus the actual boundary path follows
counterclockwise circle order in these coordinates.

The degree-free boundary-contact moment theorem and the two unchanged
endpoint torque equations now give

                    det(p1,n1)>0, det(p4,n4)<0.       (5)

There is no degree-two equation at either E2 or E3 in this argument.

## 3. The circle origin lies strictly between the two port abscissae

This step uses no universal-hub premise. Every support application of
a unit square has its entire inward unit segment in that square.
Applied to the actual endpoint squares, it gives

                         pi+[0,1]*ni subset Ei.

If x>=sigma, the real point p4+n4 would have first coordinate at
least 2*sigma+b4>=3/sqrt(2)>R. The last strict bound is uniform,
since 9/2-1105/256=47/256>0. This contradicts containment. The
reflected argument at p1 excludes x<=-sigma. Consequently

    -sigma<x<sigma,
    X1=sigma-x>0, X4=sigma+x>0, X1+X4=sqrt(2).       (6)

The first moment sign in (5) is b1*h-a1*X1>0. Hence h>0.
The reflected sign is b4*h-a4*X4>0.

Each endpoint has its actual boundary-path neighbor as a boundary
neighbor. The complete true-loaded-two properness theorem therefore
gives

    qi=pi+ell_i*ni=t_i*Fi, ell_i>=0, t_i>0.           (7)

This includes both physical circle masks and zero individual weights;
no in-body assertion is used for a radial two-corner endpoint. By
(4),(6), q1 and F1 lie in the strict upper-left quadrant, and q4 and
F4 in the strict upper-right quadrant.

## 4. The exact endpoint inequality when the endpoint owns its normal

It suffices to treat E1; reflection gives the right endpoint. Write

    P=(-X,h), n=(-b,a), k=Jn=(-a,-b),
    0<=a<=b, a^2+b^2=1, X>0,
    E=P+[0,1]n+[-rho,1-rho]k.                        (8)

The original non-K-owned side contact is a singleton in the relative
interior of E's side by the existing strict singleton convention.
The estimates allow even the enlarged endpoints 0<=rho<=1. Set

    N=P.n=b*X+a*h>0,
    K0=-P.k=b*h-a*X>0.                              (9)

The second sign is the actual endpoint moment (5). By (7), the full
circle resultant has strictly negative k component. The center's
n coordinate is N+1/2>0, so all physical circle corners are on the
outer n face. Its k coordinate must be nonpositive. Otherwise all
physical circle corners and their positive-total resultant would have
positive k component. Therefore, with Z=K0+rho>=1/2, the exact full
physical mask and radius relation are

    R^2=(N+1)^2+Z^2,
    c_E=(N+1/2)n-(Z-1/2)k,
    X=b*N-a*K0>=b*N-a*Z.                            (10)

The equality Z=1/2 is the physical two-corner mask and remains even
if one individual weight is zero. The center has nonnegative world
y component and strictly negative x component: directly,

    (c_E)_x=-X-b/2-(1/2-rho)*a
            <=-X-(b-a)/2<0.

Write c_E=(-r*cos(delta),r*sin(delta)), 0<=delta<pi/2, and put
phi=arctan(a/b). The own-frame equations in (10) give

    0<=phi<=delta,
    N+1/2=r*cos(delta-phi), Z-1/2=r*sin(delta-phi).

The following scalar estimate is the complete coordinate calculation
of FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md, Sections 6--7, reproduced to
make clear that it needs no other contact to K. Put

    d=sqrt(R^2-1/4)-1>9/10, r0=d+1/2,
    v=delta-phi.

The exact circle equations give

    (r0-r)*(r0+r+1)=r*(cos(v)+sin(v)-1),
    r>=r0-(1/2)*sin(v).                             (11)

The inequality includes v=0. For v>0, use r<=r0,
r0+r+1>2*r, and cos(v)+sin(v)-1<=sin(v). As soon as
0<=delta<pi/6, equations (10)--(11) yield

    X>=r0*cos(delta)
       -(1/2)*(cos(delta)*sin(delta-phi)+cos(phi)+sin(phi))
     >=d*cos(delta)-(3/5)*sin(delta).                (12)

For completeness, with s=sin(delta),c=cos(delta), the expression in
parentheses is (1+s*c)*cos(phi)+s^2*sin(phi), at most
sqrt(1+2*s*c+s^2). Its latter upper bound c+(6/5)*s follows from

    (c+(6/5)*s)^2-(1+2*s*c+s^2)
      =(2/25)*s*(5*c-7*s)>=0,

since delta<pi/6 and 1/sqrt(3)<5/7. Section 6 below establishes
this complete angular range before (12) is used.

## 5. The same, stronger inequality for a physically radial free endpoint

It remains to allow an endpoint which has two physical circle corners
and does not own its incoming normal. Such a square is the actual
radial S square

    E=[d,d+1]e+[-1/2,1/2]k, k=Je.

The containing-circle corners cannot be shared with K. The actual
free incoming point is therefore one of its two inner vertices
P=d*e+epsilon0*k/2, epsilon0 in {-1,1}. Its unchanged inward normal
from K has the strict form

    n=A*e-epsilon0*B*k, A,B>0, A^2+B^2=1.

In this right-handed frame the actual moment is

    det(P,n)=-epsilon0*(d*B+A/2).

For the left endpoint (5) forces epsilon0=-1. Thus

                       P=d*e-k/2, n=A*e+B*k.          (13)

The point P=(-X,h) is strictly upper-left. Its angle is clockwise
from e by arctan(1/(2*d)), while n is counterclockwise from e by
arctan(B/A). The actual K cone (4) puts n between angles 3pi/4
and pi. These facts force e, and hence the actual center
c_E=(d+1/2)e, into the upper-left quadrant. More explicitly, use
the lift e=arg(n)-arctan(B/A) in (pi/4,pi). Subtracting
arctan(1/(2*d)) stays in (-pi/4,pi); because it is the actual
strict upper-left P direction, it lies in (pi/2,pi). Hence
pi/2<arg(e)<pi.

Write e=(-cos(delta),sin(delta)), 0<delta<pi/2. Equation (13)
gives the exact unchanged endpoint coordinate

    X=d*cos(delta)-(1/2)*sin(delta)
      >=d*cos(delta)-(3/5)*sin(delta).               (14)

This proof uses the physical two-corner shape and the original
endpoint moment only. It does not replace the two circle weights
by equal weights or place its radial concurrence inside the square.
The properness in (7) still supplies the upper-quadrant resultant
with both zero-weight endpoints retained. Reflection gives (13)--(14)
at the right endpoint.

## 6. The actual three boundary links give the joint angular range

Sections 4--5 put the two actual endpoint centers at

    c1=(-r1*cos(delta1),r1*sin(delta1)),
    c4=(r4*cos(delta4),r4*sin(delta4)),
    0<=delta1,delta4<pi/2.

Their full resultants are likewise strictly in the respective upper
quadrants by (7). The actual ordered boundary path uses the complementary
lower center arc, of length pi+delta1+delta4. This follows from the
physical order in Section 2. It also follows directly from (1): the
four resultant directions preserve the physical boundary order, and
a path in the upper arc between the two upper endpoint resultants
would place all four in an open half-plane. The disjoint ordered
center/corner intervals retain the same lower-arc choice.

Every boundary center has norm greater than 5/4 in the whole radius
window. Two touching unit centers have distance at most sqrt(2), so
their minor angle is less than theta=arccos(9/25). Thus the three
actual links give

    pi+delta1+delta4<3*theta,
    delta1+delta4<alpha:=3*theta-pi.                 (15)

The complete exact triple-angle comparisons from the balanced-path
theorem are

    0<alpha<pi/6,
    cos(alpha)=13959/15625>89/100,
    sin(alpha)<9/20.                                (16)

In particular each delta_i is in the range needed for (12), and
(12) or (14) holds at each endpoint without a new frame assumption.

## 7. The actual K diagonal is strictly too short

On [0,alpha] put g(t)=d*cos(t)-(3/5)*sin(t). It is positive,
strictly decreasing and concave, since d>9/10 and alpha<pi/6.
For a fixed sum of its two arguments, concavity makes the g-sum
smallest at an endpoint pair. Using the strict sum bound (15),

    X1+X4 >= g(delta1)+g(delta4)
           > g(0)+g(alpha)
           = d*(1+cos(alpha))-(3/5)*sin(alpha)
           > (9/10)*(1+89/100)-(3/5)*(9/20)
           =1431/1000>10/7>sqrt(2).                (17)

The last two strict reserves are 17/7000 and 2/49 after squaring
the positive radical comparison. Equation (6) instead says exactly
X1+X4=sqrt(2). This contradiction proves the theorem.

No hidden endpoint is removed: delta_i=0, a_i=0, a full radial mask,
a zero individual circle weight, and every retained owned-side mean
are all within the estimates. The other H forces and both internal
loaded third forces enter the full global balance unchanged. No
physical H contact with an endpoint is assumed or suppressed.

## 8. Precise residual and source pins

The original H3.L0124 domain remains open outside this theorem.
Endpoint normals owned by K are a separate family. When neither is
K-owned, the only family left by the present full exclusion has at
least one free endpoint with a unique physical circle corner. The
usual fixed-tip selector can constrain that family only when its
other actual application is fixed; no variable shared boundary-side
mean is discarded here. No claim of a whole feature closure for that
residual is made.

| Exact input | SHA-256 | Literal use |
| --- | --- | --- |
| SIX_BODY_INNER_PENTAGON_LOAD_COVER.md | fa877c9d7d25c57a7c8cf438a429465b5952cb8db6628c57d9d93695b33dd434 | Original H3.L0124 graph, loads, outer face and reflection |
| FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md | 6c38d162e1f2c435cf65a8b4a58a7001fe9489c65b3510159fee2687b9753708 | Entire balanced four-boundary path and its exact angular bounds |
| BOUNDARY_CONTACT_ORIGIN_MOMENT_ORIENTATION.md | 851417d7fcd12ccb93a6f7f09ba7d7b2bf9bccc61c82fee3457b5ee4cee47e9a | Degree-free physical boundary-edge moment signs |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 0d61292a0aa57084b88b4a72754fc78e123e8b684dac09be966fb074ab58e877 | True endpoint loaded-two properness with an actual boundary neighbor |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | 6154eee2ab1114d063b0dbd1a2800c3522cbb1b46ec44a258c1c89d8ffb9e975 | Only the radius-free inward unit-segment Lemma 3.1 |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | 2625b3a2b730525a6397bc90232e78c5e1aac8091381c1f5e5fc8a71ef1da449 | Actual boundary path/corner order and physical masks |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | eb26f19b27dc7327f80a64ccfd1febb542c5915aadcf95227e35765b20d3509a | Selected physical embedding, initial singleton convention and weak-junction order |
| FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md | 32dcd0afd0883e4272e95b26278d8c90af0c02639b522fd5c960941bb34dba02 | The reproduced endpoint coordinate estimate only; no universal-hub radius premise |

This is a hand physical/force theorem. No pose sample, numerical
configuration, extra contact, shortened star, changed mean, normal
reselection, motion, Lean compilation, CI, ledger edit or remote
mutation is a premise.
