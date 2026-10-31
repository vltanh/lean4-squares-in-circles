# The positive-channel S123 hole is empty when the actual root depth is at least one fiftieth

Date: October 27, 2026.

**Status: complete physical hole theorem and conditional canonical
slider consequence, submitted for full independent and root review.**
Every actual M frame and mask is included. Its whole unique-opposite-M
original caller is stated in Section7. A positive-channel radial-M
caller with smaller V remains explicitly outside this theorem.

## 1. Exact original physical chart

Keep the same actual ring A--B--M--C--U--A with its original leaf
and all three extra units. Use the actual own axes of A, and put

    d=1+epsilon,       0<epsilon<1/60,
    R^2=(d+1)^2+1/4,
    1/50<=V<13/50,       F=1-V,
    A=[r-1,r] times[-V,F],       |r|<=epsilon,
    n=(x,-t), f=(t,x),       t>0, x>0, x^2+t^2=1,

    r*x+V*t=epsilon,       T=V*x-r*t>0.

Thus the actual A--U point is E=(r,-V)=epsilon*n-T*f.
This is the strict-channel feature; no zero-angle variable side
mean is replaced by this corner.

The actual B, C and U and their original contact points are

    W=sqrt(R^2-(F+1)^2),       1/2<W<1,       u=1-W,
    B=[-W,u] times[F,F+1],
    C=[d,d+1]n+[-1/2,1/2]f,
    U=[epsilon,d]n+[z,z+1]f,

    S=p_AB=(-J,F),       J>0,
    Q=p_BM=(u,Y),        F<=Y<F+1,
    P=p_CM=X*n+(1/2)f,  d<=X<=d+1,
    D=p_CU=d*n-T*f.

Each displayed contact belongs to its two actual squares, and
-T remains in the full original U interval. The B-to-M normal
is the actual owned East axis. The complete radial-side theorem
gives M wholly in n>epsilon. In particular

    Q_n=u*x-Y*t>epsilon,
    Q_f=u*t+Y*x>=Y>=F>37/50.                         (1)

The first inequality also implies t/x<u/F<25/37, hence t<3/5.
All physical M masks and all actual C means X remain.

**Theorem 1.1.** No whole additional unit lies on the bounded side
of this original five-cycle.

## 2. The exact occupied A/B/C pieces

All five contacts E,S,Q,P,D are distinct. E has norm less than
sqrt((1/60)^2+(13/50)^2), S and Q have height at least F,
and P has height at most1/2 and norm at least sqrt(d^2+1/4).
D has negative world height and differs from E by n; its f
coordinate -T differs from P's1/2. The signs of the S,Q
horizontal coordinates distinguish those contacts as well.

Use the full center/contact homotopy and winding subtraction
from CONTACT_RING_HOLE_AREA.md. The actual center/contact loop
is Jordan, with each open spoke in its actual square interior.
Its clockwise contact polygon is E--S--Q--P--D--E. A further
unit inside contributes its full area one to the free hole.

Subtract the actual inward occupied triangles

    E,(r,F),S inside A;
    S,(u,F),Q inside B;
    P,d*n+f/2,D inside C.

Each auxiliary corner is on the inward side of its clockwise
contact chord, and each triangle lies in its actual square.
The same zero/one winding justification as the complete
zero-channel hole theorem applies. The pieces have disjoint
open interiors.

For the actual M chord, set

    q=Q_n, p=Q_f,
    a0=X-q>0, b0=p-1/2>0,
    ell^2=a0^2+b0^2=|P-Q|^2<=2.

Introduce only for the area calculation the point
I=q*n+(1/2)f. It is not asserted to belong to M. Inserting
I between Q and P subtracts the right-triangle area a0*b0/2.

The clockwise area after these insertions, and after canceling
the collinear I--P--(d*n+f/2) segments, is exactly

    H0(Y)
      =[d+(d+1)T-r(1+F)+2uF-uY
           -(u*x-Y*t)(1-u*t-Y*x)]/2.                (2)

This follows directly from the determinants of
E,(r,F),(u,F),Q,I,d*n+f/2,D. The cancellation is algebraic
and retains all actual means X,Y in the preceding physical
subtraction.

## 3. A universal quarter bound for the actual M chord

If ell<=1, the unremoved triangle term is at most

    a0*b0/2<=ell^2/4<=1/4.

If ell>1, the complete actual-square chord lemma in
CONTACT_RING_HOLE_AREA.md Section2 supplies an inward occupied
M piece of area at least sqrt(ell^2-1)/2. It has winding one
and is disjoint from the occupied A/B/C pieces. Hence the
remaining term is at most

    ell^2/4-sqrt(ell^2-1)/2<=1/4,

because for v=sqrt(ell^2-1) in[0,1] the difference from1/4
is v(v-2)/4<=0.

Thus every actual M orientation, side mean and physical circle
mask satisfies

    area(hole)<=H0(Y)+1/4.                           (3)

No M-owned normal or radial concurrence was used. The auxiliary
right-triangle point is only a scalar area comparison, never a
new physical support point.

For fixed original epsilon,V,t,r,u,T, differentiation of (2)
in its scalar Y comparison gives

    H0'(Y)=t[1-2(u*t+Y*x)]/2<0

throughout F<=Y<=the actual Y. Indeed (1) gives the same
positive normal projection at Y=F, and therefore
u*t+F*x>=F>37/50. Consequently

    H0(Y)<=H0(F)
      =[d+(d+1)T-r(1+F)+uF
          -q0(1-p0)]/2,                             (4)

where q0=u*x-F*t and p0=u*t+F*x. This is a comparison
at fixed original scalar data; no actual B mean is changed.

## 4. Complete exact scalar certificate

The following larger closed-domain statement is the entire
remaining scalar assertion:

    0<=epsilon<=1/60, 1/50<=V<=13/50, 0<=t<=3/5,
    d=1+epsilon, F=1-V, x=sqrt(1-t^2),
    r=(epsilon-V*t)/x,
    R2=(d+1)^2+1/4,
    W=sqrt(R2-(F+1)^2), u=1-W,
    T=V*x-r*t, q0=u*x-F*t, p0=u*t+F*x.

Whenever the original necessary guards hold,

    |r|<=epsilon, 1/2<W<1, q0>epsilon, T>0,           (5)

one has

    3/4-H0(F)>0.                                    (6)

The exact standalone checker is

    certificates/s123_positive_channel_hole_certificate.py.

It evaluates this complete three-variable box by outward integer
interval arithmetic with N=2^40. Rational inputs use floor/ceiling;
products take all four endpoint products; squares retain zero
when appropriate; positive reciprocals and square roots use
outward endpoints, with integer square root for the latter.
All actual square-root radicands and denominators are positive.

A whole box is discarded only if one of (5) is impossible
throughout it, or if its W radicand is strictly negative
throughout. Specifically the r, W, q0 and T guards use interval
bounds with the indicated strict/weak signs. If a radicand's
lower interval endpoint is negative but its upper endpoint
nonnegative, clamping only that lower endpoint to zero enlarges
the enclosure of all feasible actual roots.

A feasible box is accepted only if the lower bound of (6)
is strictly positive. Otherwise bisect a longest normalized
integer side, comparing

    60 width(epsilon), floor(25 width(V)/6),
    floor(5 width(t)/3),

with the first side on a tie. The integer midpoint and both
closed children are retained, and the lower child is visited
first. All rational endpoints are initially rounded outward.

The entire exact tree has:

| Terminal class | Boxes |
| --- | ---: |
| Strict positive lower bound in (6) | 285 |
| Impossible |r|<=epsilon guard | 74 |
| Impossible q0>epsilon guard | 43 |
| Impossible1/2<W<1 guard | 3 |

There are404 internal splits,405 terminal boxes,809 visited
boxes and maximum depth15. No unresolved or precision endpoint
is accepted. The uniform positive lower numerator for (6)
over the285 accepted boxes is

    19715476/1099511627776>0.                         (7)

The executable asserts all counts, depth and the exact minimum.
No pose sampling or numerical optimizer is used. Equations(2)--(7)
give area(hole)<1, proving Theorem1.1.

The scalar comparison includes t=0 only as a closed endpoint
of its larger box. It does not apply the strict contact formula
E=(r,-V) to a different actual zero-angle side mean; the entire
zero-angle domain has its separate accepted hand theorem.

## 5. The actual inner rectangle and canonical slider

At the existing secondary radius minimizer, let b=z+1 be the
actual f-top of U. Then

    b>=1/2, or U has an actual physical M contact.   (8)

This is proved by the original same-nine motion, not by choosing
a transmitter mean. The contact polygon has winding one throughout

    (epsilon,d) in n times (-T,1/2) in f.             (9)

To check this literally: A and its chord lie in n<=epsilon.
The B chord has world height at least F; where n>epsilon its
f coordinate is at least(F+t*n)/x>1/2. Its actual Q has
q<1/2<d and p>1/2. The M chord Q--P stays at f>=1/2.
The C chord has n>=d, and the U chord is precisely the
bottom segment f=-T. These actual barriers give (9), including
all possible extra contacts outside the chosen edges.

If b<1/2 and U is closed-disjoint from M, translate U by a
sufficiently small positive amount along f. A and C remain
separated by their unchanged n supports; B is above the
newly occupied strip, whose world height is below1/2.
Every newly occupied interior point outside the core lies
in the already proved empty hole (9). Thus all other original
units and the real leaf remain disjoint.

The U transverse center is b-1/2<0, so this move strictly
decreases both its containing-circle radius contribution and
its squared center norm. This contradicts the existing
secondary minimum and proves (8).

If the actual M is wholly in f>=1/2, it cannot touch U
when b<1/2, and therefore (8) yields b>=1/2.
No positive multiplier is assigned to a possible new UM
physical contact.

## 6. Original unique-opposite strict-M consequence

The complete source
S123_OWNED_EAST_STRICT_MIDDLE_REMAINING_DOMAIN.md (27eee13e)
gives, in the unique-opposite physical M mask,

    P=X*n+f/2,
    v=b1*n+a1*f, w=a1*n-b1*f,
    M=P-w+[0,1]w+[0,1]v,
    a1,b1>0, a1^2+b1^2=1,
    b1<12/25, a1>6/7, X+b1<8/5,
    Q=(X-a1)n+(1/2+b1)f.

Its actual Q_n>epsilon implies X-a1>0. Hence its world height
is at most1/2+b1<49/50, whereas the original B mean has
Y>=F=1-V. Thus V>1/50 in every strict-channel unique-mask
row as well as at t=0. This is exactly the extra depth
hypothesis used in Section1.

M lies wholly at f>=1/2, so Section5 gives U.top_f>=1/2
at the original canonical packing. The physical lower M edge
from Q to P has f height

    1/2+(b1/a1)(X-d)

at n=d. Since Q_n<1/2<d<=X and U's actual bottom is at most
-T<0, actual nonoverlap gives U.top_f at most this height.
The same exact frame bounds yield

    (b1/a1)(X-d)<(7/6)b1(3/5-b1)<=21/200.

Consequently this entire unique-opposite positive-channel row
has the unchanged physical strip

    [epsilon,d]n+[-79/200,1/2]f subset U.             (10)

The separate full independent review of27eee13e remains
required in an original caller chain. Its physical radial-M
row at positive t is not asserted here to satisfy V>=1/50.

## 7. Retained completion scope

This source proves the whole central-hole exclusion under its
explicit depth hypothesis and the exact canonical strip consequence
for the stated unique-opposite M caller. It includes both genuine
root types wherever those complete actual hypotheses hold.

It does not prove that every exterior extra is away from D_(1/8),
does not replace the positive-channel root/leaf geometry by its
zero-angle specialization, and does not supply a final exterior
arc-routing bound. A positive-channel radial M with smaller V
requires a separate argument.

All actual loads, normals, means, physical masks and all nine
units remain. No compilation, CI, remote action or shared
metadata edit is performed.

