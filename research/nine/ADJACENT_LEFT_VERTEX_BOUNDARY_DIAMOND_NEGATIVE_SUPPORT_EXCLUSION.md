# Two boundary pages cannot straddle adjacent left root vertices at negative support

Date: October 28, 2026 UTC. Author: fan_low continuation.

**Status: complete new force-free hand theorem, frozen for full root and
separate independent review.** The theorem uses four actual unit squares
and their physical supports and contacts. It has no force equation,
degree, load, positive-graph, radial-leaf or upper-radius premise. All
orientations, support endpoints and actual side means are retained.

The original low aligned fan is a separate caller. In particular this
proof does not turn either of its actual degree-four bodies into a
three-force star. It does not assume the missing house long-page edge.

## 1. The entire physical domain

Let X,U,K,W be distinct actual closed unit squares with pairwise disjoint
open interiors, all contained in the same origin-centered circle of
radius R>=2. Suppose U and W physically touch that circle. In one
orthonormal frame about its unchanged origin suppose

    X=[epsilon,epsilon+1] times [-b,a],
    -1/15<=epsilon<=0,
    a+b=1,       1/3<=b<=21/50.                       (1)

Thus 29/50<=a<=2/3. The original X-to-U supporting normal is strict
Northwest, and the original X-to-K supporting normal is strict
Southwest. Their actual common applications are therefore the fixed
physical points

    Q=(epsilon,a),       P=(epsilon,-b),
    X intersect U={Q},   X intersect K={P}.             (2)

Assume also the actual physical contacts and support

    U intersect K nonempty,
    W subset {y<=-b},       X intersect W nonempty,
    K intersect W nonempty.                            (3)

No degree or force is imposed on any of these four units. Both contacts
involving W may have their original full side means or endpoints.

**Physical theorem.** The complete configuration (1)--(3) is impossible.

The proof covers the closed epsilon and b endpoints in (1) and R=2.
It needs the two strict root-vertex normals in (2); it does not claim
that an original West-axis normal has the same feature. That distinct
interface has its separate low-transverse theorem.

## 2. A complete screen allowing a small positive rightward reach

We first prove a reusable physical screen. Let V be an actual unit
square with

    min_V y=b,       1/3<=b<=21/50,
    -1/15<=epsilon<=0.

Suppose the minimum-y support contains an actual point (x,b) with
x>=epsilon, and V contains an actual point with first coordinate at
most epsilon+D. Assume

    0<=D<=27/1000,
    b>=81/200  implies  D<=1/500.                     (4)

**Screen.** Every corner of V has squared norm strictly below four.
Both actual points may be side means, may coincide, and are not moved.
There is no upper bound on x among the hypotheses.

Write B=21/50 and E=1/15. If V is parallel to the displayed axes,
then V=[z,z+1] times [b,b+1]. The two actual points give

    epsilon-1<=z<=epsilon+D.

Since D<=27/1000<1/15, every corner has absolute first coordinate
at most 16/15 and height at most 71/50. Thus

    |corner|^2 <= (16/15)^2+(71/50)^2
                 =70969/22500<4.                     (5)

This includes every aligned endpoint and minimum-side mean.

Otherwise the displayed minimum point is V's unique lowest vertex.
Its complete actual frame is

    V=(x,b)+[0,1]u+[0,1]v,
    u=(p,q),       v=(-q,p),
    p,q>0,        p^2+q^2=1.

The actual point whose first coordinate is at most epsilon+D gives
the full unchanged horizontal interval

    epsilon<=x<=epsilon+D+q.                          (6)

We use the whole-frame inequalities

    p+q<=sqrt(2)<17/12,
    p^2+2pq<13/8,       q^2+2pq<13/8.                (7)

For example,

    13/8-(p^2+2pq)=((13q-8p)^2+p^2)/104>0;

interchanging p,q gives the other identity. These bounds do not
sample or subdivide the square's orientation.

At (x,b), (6) gives |x|<=16/15, so

    |(x,b)|^2<=29569/22500<4.                         (8)

At (x,b)+v, the horizontal coordinate is between epsilon-q and
epsilon+D, so (5) applies again. At (x,b)+u its absolute first
coordinate is at most D+p+q: the possible negative lower endpoint
has magnitude at most E, whereas p+q>=1. Consequently

    |(x,b)+u|^2
       <=(D+p+q)^2+(b+q)^2
       <D^2+(17/6)D+1+B^2+13/8+2B
       <=3718629/1000000<4.                           (9)

The exact reserve in (9) is 281371/1000000.

For the remaining opposite corner

    Z=(x+p-q,b+p+q),

its squared norm is convex in the original x. It suffices to bound
both endpoints of (6), as comparison values only.

At x=epsilon, (7), |p-q|<=1 and b<=B give

    |Z|^2
       =2+b^2+epsilon^2+2b(p+q)+2epsilon(p-q)
       <=2+B^2+E^2+(17/6)B+2E
        =19711/5625<4.                               (10)

At x=epsilon+D+q, its first coordinate is epsilon+D+p. The sign
epsilon<=0 and D+p>=0 give, including a negative resulting coordinate,

    (epsilon+D+p)^2
       <=epsilon^2+(D+p)^2
       <=E^2+D^2+2D+p^2.

Therefore

    |Z|^2
       < E^2+D^2+2D+1+b^2+13/8+(17/6)b.              (11)

For the entire first height interval 1/3<=b<=81/200, use D<=27/1000
in (11). Its right side is at most

    17980643/4500000
       =4-19357/4500000<4.                           (12)

For the entire second interval 81/200<=b<=21/50, use D<=1/500.
The right side is at most

    8999659/2250000
       =4-341/2250000<4.                             (13)

These two continuous monotone estimates include their common height
endpoint. Equations (8)--(13) control every actual corner over the
whole interval (6). This proves the screen, including D=0. Convexity
of the open disk then puts the whole closed actual V strictly inside
the radius-two disk.

## 3. Two complete support and corner facts

### 3.1. Opposed projections from an actual support point

If a unit T has an actual minimum-m support point Y, and unit u has
m.u<0, then

    max_(Z in T) u.(Z-Y)<1.                           (14)

Here is the full support-span argument. At a vertex Y, write the two
orthonormal inward axes f,g. Then m.f,m.g>=0. Since m.u<0, at least
one of u.f,u.g is negative. Only the other can contribute positively
to the support span, and its component is strictly below one. A
component equal to one would instead make u an inward axis and
m.u nonnegative. At a side-interior Y, the inward normal axis has
negative u-component. Only a tangential interval of length at most
one contributes positively. Its projection is strictly below one
because u has a nonzero normal component. Side endpoints are the
vertex case. This proves (14) at every possible actual point or mean.

Apply (14) to U at Q with u=South and its strict Northwest incoming
normal, and to K at P with u=North and its strict Southwest incoming
normal. The complete actual support statements are

    min_U y>-b,       max_K y<a.                      (15)

They use no force magnitudes, equilibrium or circle weights.

### 3.2. A leftward unit based at the upper port is circle-clear

Suppose Q is a vertex of an actual unit T contained in x<=epsilon.
Its full frame can be written, including aligned endpoints,

    T=Q+[0,1](-c,s)+[0,1](-s,-c),
    c,s>=0,       c^2+s^2=1.

Put delta=-epsilon, so 0<=delta<=1/15 and a>=29/50>delta. We have

    |Q|^2=delta^2+a^2<=101/225<(67/100)^2.             (16)

The exact last reserve is 1/90000. Each adjacent corner is within
distance one of Q, hence has norm below 167/100<2. The opposite
corner has squared norm

    delta^2+a^2+2+2(delta+a)s+2(delta-a)c
       <=delta^2+a^2+2+2(delta+a)
        =(1+delta)^2+(1+a)^2
       <=(16/15)^2+(5/3)^2
        =881/225<4.                                 (17)

Thus every corner of this entire leftward frame lies strictly inside
radius two. It cannot be the physical boundary U in (1)--(3).

## 4. Both actual root contacts must be side-interior contacts

At P the root X occupies the open Northeast quadrant locally. If P
were a vertex of K, K's local right-angle interior sector could not
meet that quadrant. Every such right-angle sector is contained either
in the closed left half-plane or in the closed lower half-plane.
The actual entire unit K would therefore satisfy respectively

    K subset {x<=epsilon},       or       K subset {y<=-b}.

The second alternative contradicts its actual contact with U, by
(15). In the first, reflect W across the horizontal axis. Its actual
X contact is a minimum-height point with x>=epsilon, while its actual
K contact has x<=epsilon. Section 2 with D=0 proves that this entire
actual W is circle-clear, also a contradiction.

Thus P is not a K vertex. It cannot be in int(K), since X has an
interior sector there. It is in the relative interior of a K side.
The original supporting normal is therefore the unique K side axis;
it has not been reselected.

Likewise, at Q the root X occupies the open Southeast quadrant.
If Q were a U vertex, its local right-angle sector would put the
entire U either in x<=epsilon or in y>=a. The first is impossible
by Section 3.2, and the second cannot touch K by (15). Thus Q too
is a relative-interior side point, with its original normal uniquely
owned by U. This argument includes all aligned vertex endpoints.

The two unchanged actual frames consequently have exactly the form

    K=P+[0,1]n+[-kappa,1-kappa]j,
    n=(-r,-t),       j=(t,-r),
    r,t>0,          r^2+t^2=1,       0<kappa<1;

    U=Q+[0,1]m+[-rho,1-rho]k,
    m=(-c,s),       k=(-s,-c),
    c,s>0,          c^2+s^2=1,       0<rho<1.          (18)

These offsets are exact geometrical side positions. They are not a
chosen pair-force mean or a substitute for an original application.

## 5. The upper physical circle corner controls the lower hub's reach

### 5.1. The complete physical U mask

The near-side corners Q-rho*k and Q+(1-rho)*k are within distance
one of Q, so (16) puts them strictly inside radius two. The lower
far corner is

    Z_-=Q+m+(1-rho)k.

Its squared norm is convex in 1-rho in [0,1]. Its endpoint Q+m
is within distance one of Q, and its other endpoint Q+m+k is the
leftward opposite corner bounded by (17). Thus Z_- is strictly
inside radius two as well, for the full original rho interval.

The only possible physical circle corner of U is therefore exactly

    Z_+=Q+m-rho*k,       |Z_+|=R>=2.                 (19)

This treats the physical mask, independently of every individual
circle coefficient. In particular a possible second physical circle
corner has been excluded by its actual norm, not by a zero weight.

Since |Z_+-Q|=sqrt(1+rho^2), (16),(19) imply

    sqrt(1+rho^2)>=2-|Q|>133/100,
    rho^2>7689/10000>49/64,
    rho>7/8.                                         (20)

The exact reserve in the second comparison is 131/40000.

If additionally b>=81/200, then a<=119/200 and

    |Q|^2<=1/225+(119/200)^2<(3/5)^2,                (21)

with exact reserve 551/360000. In that complete height interval,

    sqrt(1+rho^2)>7/5,       rho^2>24/25.              (22)

### 5.2. The actual U--K contact and a whole continuous maximum

The extrema of the exact frames (18) are

    max_K y=-b+kappa*r,
    min_U y=a-(1-rho)c.

Their actual contact implies

    kappa*r+(1-rho)c>=1,
    kappa*r>rho,                                     (23)

where the strict second inequality uses c<1 and 1-rho>0. This is
a full-square projection consequence; it does not select any new
U--K contact point or move an original shared mean.

The complete rightward reach of K is

    max_K x=epsilon+D,       D=(1-kappa)t>0.

By (23), r>rho and

    D<(1-rho/r)sqrt(1-r^2),       rho<r<1.             (24)

For fixed rho, the derivative of the right side has the sign of
rho-r^3: explicitly its derivative is

    (rho-r^3)/(r^2 sqrt(1-r^2)).

Its sole maximum on the complete closed interval [rho,1] is at
r=rho^(1/3); both endpoint values are zero. Therefore

    D<(1-rho^(2/3))^(3/2).                            (25)

This is a single whole-interval maximum, with no angular mesh or
coefficient certificate.

The first bound in (20) gives

    rho^2>49/64>(91/100)^3,
    D<(9/100)^(3/2)=27/1000.                          (26)

The cube comparison has exact reserve 6027/500000. In the entire
second height range b>=81/200, (22) instead gives

    rho^2>24/25>(197/200)^3,
    D<(3/200)^(3/2)<1/500.                            (27)

The first reserve in (27) is 34627/8000000; the final comparison
follows by squaring, with reserve

    (1/500)^2-(3/200)^3=1/1600000>0.

Thus the unchanged actual K satisfies both bounds (4), over every
rho,r,kappa and every actual U--K support feature.

## 6. The actual lower boundary page is impossible

Take the unchanged actual X--W contact in (3). It has height -b
and first coordinate at least epsilon. The unchanged actual K--W
contact has first coordinate at most

    max_K x=epsilon+D.

Reflecting the whole coordinate description across the horizontal
axis turns W into exactly the V of Section 2. Its minimum height
is b, its original minimum-height point is retained, and (26)--(27)
give the full support bounds (4). Every actual W corner is therefore
strictly inside radius two. This contradicts W's physical contact
with the original circle of radius R>=2.

This proves the physical theorem on all of (1)--(3). The original
square X is not assumed unloaded, U and W need not have degree two,
and K is not assigned any equilibrium equation. Every additional
force, actual square and physical zero-weight contact may remain.

## 7. Exact inputs and intended original callers

All scalar inequalities, sector cases, actual-point bounds and
continuous maxima needed by this theorem are printed above. The
support-span fact (14) is also the complete geometric lemma in

| Source | SHA256 | Exact relation |
| --- | --- | --- |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Section 1's support-span fact, completely rederived in Section 3.1; no triangle-force or degree premise is imported. |

For the low aligned fan, use X=2, K=J and the actual two pages
{U,W}={1,3}. Both page assignments have the real contacts U--K and
W--K, and the theorem needs neither page's force equation. The
unchanged degrees 2(4), J4, 1(2), 3(3), 4(2), L1 therefore remain.
A separate complete caller must establish (1) and the original
normal cover; this manuscript does not supply them by assertion.

For a house with root X=A and other hub K=D, both page-to-K contacts
are needed. The actual short page T has DT, while the long branch is
B--C--D and has no BD edge. The theorem does not contract that path
or assert the absent B--D contact. Any house use must verify its own
two real contacts before invoking (3).

The author derived the side-owner cover and reach estimate from the
actual unit sectors, the physical upper circle corner and the whole
U--K vertical overlap. Root asked for the degree-free kernel and an
exact original-domain join; root did not supply these inequalities.
The new lower screen extends the separate previously frozen
NEGATIVE_SUPPORT_LOW_TRANSVERSE_BOUNDARY_NEIGHBOR_EXCLUSION.md at its
printed hypotheses; that earlier proof is not a mathematical premise
of the fully printed screen here.

The rational identities and reserves were checked with exact fraction
arithmetic. No numerical pose, sampled orientation, computational
exclusion packet, new normal selection, changed mean, Lean execution,
CI, workflow, metadata, commit or remote operation is used. Full root
and independent review of these exact bytes remains necessary before
any original-family adoption.
