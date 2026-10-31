# A radius-dependent central disk and the exclusion of six boundary neighbors

Date: October 27, 2026.

**Status: accepted complete uniform physical proof after full root and
separate independent reviews.** See
REVIEW_CENTRAL_DISK_SIX_BOUNDARY_NEIGHBORS_ROOT_2026_10_27.md and
REVIEW_CENTRAL_DISK_SIX_BOUNDARY_NEIGHBORS_TRIANGLE_BRIDGES_2026_10_27.md.
Their mathematical source pins precede this acceptance-only header.
The two geometric theorems below concern
all nine actual unit squares and use no force equation. Their stated
three C3.335 bouquet consequences keep every original force and degree.
No original gate or shared ledger is changed here.

Let nine closed unit squares with pairwise disjoint open interiors be
contained in the same closed circle centered at O, of radius

    2 <= R <= sqrt(1105)/16 < 25/12.

Write

    r = (9/5)R - 251/100,
    h = r-1 = (9/5)R - 351/100,
    t = 1/2-h = 401/100 - (9/5)R.                     (1)

In particular

    109/100 <= r < 31/25 < 5/4,
    9/100 <= h < 6/25 < 1/4,
    t > 13/50 > 0.                                   (2)

**Central-disk theorem.** No actual one of the nine squares contains
the entire closed disk D_h. Consequently every actual square center c
satisfies |c|>t.

**Boundary-neighbor theorem.** No actual square physically touches six
distinct squares which touch the containing circle. These are physical
contacts and physical circle corners, without any positivity condition
on their stress weights.

The first statement strengthens the fixed quarter-disk obstruction at
lower radii. The proof uses one circle of radius r determined by the
actual R, and an exhaustive analytic own-frame cover. It introduces
no sampled poses, numerical subdivisions or parameter gates.

## 1. A whole-orientation inner-circle measure bound

Let S be any actual unit square in D_R with

    dist(O,S) >= h.                                    (3)

We prove that the angular measure of

    int S intersect {x:|x|=r}

is strictly greater than pi/4. Connectedness is not asserted at an
outer-face tangency: removing an isolated circle point from the open
intersection does not change its angular measure. This convention
retains the exact equality in (3).

Choose signs and order of the actual own axes so that its center
coordinates satisfy x>=y>=0. Put

    a=x+1/2, b=y+1/2, A=a-1, B=b-1,
    S=[A,a] times [B,b],
    a>=b>=1/2, q=a^2+b^2<=R^2.                       (4)

This is the entire physical orientation and position domain. The
nearest point has coordinates (max(A,0),max(B,0)).

### 1.1. Uniform inner-corner and quadratic bounds when a>r

In this case A>h>0, and -1/2<=B<1/2 because b<=R/sqrt(2)<3/2.
Put d=sqrt(R^2-1/4)-1 as usual. Then

    A<=d<R-53/50.                                    (5)

For the strict last comparison, rationalize

    R-sqrt(R^2-1/4)
       =(1/4)/(R+sqrt(R^2-1/4))
       >1/(8R)>3/50,

using R<25/12. The following difference is positive throughout the
whole interval R>=2:

    r^2-(R-53/50)^2-1/4 >= 109/2000.                 (6)

Indeed at R=2 it equals 109/2000. Its derivative is
(18/5)r-2(R-53/50), positive at R=2 and increasing thereafter.
Thus

    A^2+B^2 <= d^2+1/4 < r^2.                         (7)

For the angle comparison define

    E_0=A^2+B^2+sqrt(2) A B.

At fixed q from (4), let s=a+b. Direct expansion gives

    E_0=(1-1/sqrt(2))q+s^2/sqrt(2)
               -(2+sqrt(2))s+2+sqrt(2).              (8)

This is convex in s. On the full fixed-q domain a>=b>=1/2, its
maximum is attained at one of b=1/2 and a=b. Enlarging to both
endpoints is valid even if an endpoint does not satisfy (3) or a>r.

At b=1/2, write D=sqrt(q-1/4)-1. Since a>r in the actual domain,
q>r^2+1/4, so D>h>0. Also D<=d<61/60. Therefore

    E_0=D^2+1/4-D/sqrt(2)
        <D^2+1/4-(7/10)D
        <=2059/3600 <11881/20000 <=r^2/2.             (9)

The quadratic bound follows from convexity on [0,61/60]: its
endpoint values are 1/4 and 2059/3600. The exact last reserve is
3979/180000.

At a=b=v=sqrt(q/2), one has v>4/5 because
q>r^2+1/4>=14381/10000>32/25. If v<=1, then

    E_0=(2+sqrt(2))(v-1)^2<7/50<r^2/2.

If v>=1, it suffices to bound this expression at v=R/sqrt(2).
The exact positive comparison is

    r-sqrt(4+2sqrt(2))*(R/sqrt(2)-1)>3/1000.          (10)

To check it without approximation, use

    sqrt(2+sqrt(2))<231/125,
    sqrt(4+2sqrt(2))>2613/1000.

The first follows by squaring and sqrt(2)<99/70; the second follows
by squaring and sqrt(2)>707/500, with reserve 231/1000000 in the
last squared comparison. The left side of (10) is consequently
greater than

    -(6/125)R+103/1000 >3/1000

because R<25/12. Both sides compared in (10) are nonnegative.
Squaring therefore gives

    (2+sqrt(2))(R/sqrt(2)-1)^2 < r^2/2.

The fixed-q endpoint cover proves

    E_0<r^2/2                                         (11)

throughout the whole a>r domain.

### 1.2. Both possible inner-face arc lengths exceed pi/4

For a>r set

    alpha=arccos(A/r), beta=arcsin(B/r),
    gamma=arcsin(min(b/r,1)).

Equations (4),(7) show that the closed-circle intersection has angular
interval

    [beta,min(alpha,gamma)].

Its open-interior intersection differs only in the finite endpoints.
In particular (7) gives beta>-alpha even when B is negative. The
quantity in (11) satisfies

    (sqrt(2)A+B)^2 < r^2-B^2.

It follows, also when the expression on the left before squaring
is negative, that

    A<r cos(beta+pi/4).

Here |B|<=1/2 and r>=109/100 imply |beta|<pi/4, so cosine is
being compared on its decreasing interval. Thus

    alpha-beta>pi/4.                                  (12)

If b<=r, the strip-width estimate is

    gamma-beta=arcsin(b/r)-arcsin((b-1)/r)
       >=2 arcsin(1/(2r))>2 arcsin(2/5)>pi/4.          (13)

The difference is nondecreasing for b>=1/2 because b>=|b-1|;
continuity includes b=r. The final strict comparison is the same
sin(pi/8)<2/5 identity as in the fixed quarter-disk arc theorem.
If b>r, gamma=pi/2 and beta<pi/4 give (13) directly.
Both possible interval lengths are therefore strictly above pi/4.

### 1.3. The complete outer-face domain a<=r, including equality in (3)

Here A,B<=h. If B<=0, (3) gives max(A,0)>=h, while A<=h.
Hence A=h and a=r. The other upper endpoint b lies in [1/2,1].
Every point on the positive-x circle branch with B<=y<=b also
satisfies x>=h: indeed |y|<=1 and h^2+1<=r^2. Its angular
interval is

    [arcsin(B/r),arcsin(b/r)].

The measure is at least the strict strip bound (13). The point
(r,0), when present, is on the outer side and is deleted from
the open interior. This is one point of measure zero. The cases
B=0 and original side endpoints are included.

Otherwise

    0<B<=A<=h<1/4,
    k^2=A^2+B^2>=h^2.                                (14)

The closed first-quadrant circle intersection has endpoints

    max(arccos(a/r),arcsin(B/r)),
    min(arccos(A/r),arcsin(b/r)).                     (15)

It suffices to show that each of the four upper-minus-lower
differences exceeds pi/4. The two same-coordinate strip differences
have (13). The inner-inner difference is at least

    pi/2-2 arcsin(h/r)>pi/2-2 arcsin(1/5)>pi/4.        (16)

For the outer-outer difference put

    L(A,B)=arcsin((1+A)/r)+arcsin((1+B)/r)-pi/2.

Fix k^2 and vary A from B=k/sqrt(2) to its actual value, with
B=sqrt(k^2-A^2). Comparing the two positive derivative terms and
squaring shows that the derivative's sign is the sign of

    (A-B)*[(A+B-h)^2+(k^2-h^2)(A+B+1)].              (17)

This expression is nonnegative by (14). It follows directly by
factoring the comparison, using r^2-1=2h+h^2; no additional
force or orientation condition is used. Continuity covers an
endpoint A=h, where an arcsine derivative can be infinite.

Consequently

    L(A,B)>=2 arcsin((1+k/sqrt(2))/r)-pi/2
       >=2 arcsin((1+h/sqrt(2))/(1+h))-pi/2
       >2 arcsin((4+1/sqrt(2))/5)-pi/2>pi/4.          (18)

The ratio decreases with h, and h<1/4. The final exact squared
reserve against sin^2(3pi/8) is (16-9sqrt(2))/100>0.
Thus even k=h gives a strict final bound. Equations (13),(16),(18)
prove that the interval (15) has angular length greater than pi/4.
Removing its actual face endpoints does not change that measure.

This completes the exhaustive a>r / a<=r proof of the measure claim
under the closed distance premise (3).

## 2. All eight actual other squares exclude a closed central disk

Suppose one original unit H contained the entire closed D_h.
The open disk of radius h is then in int H. Every one of the
eight other actual closed squares S must satisfy dist(O,S)>=h.
If one had a point of norm below h, that point would be in int H,
and interior points of S approaching it would give open overlap.

Section 1 gives angular measure strictly greater than pi/4 for
each of the eight sets int S intersect {|x|=r}. These measurable
sets are pairwise disjoint because the actual square interiors
are disjoint. Their total measure would exceed 2pi. This is
impossible on one circle, and proves the central-disk theorem.

If an actual square center c had |c|<=t=1/2-h, every one of its
own center coordinates would have absolute value at most t.
Every side would be at distance at least h from O, and that
square would contain the closed D_h. The theorem therefore gives

    |c|>t                                               (19)

for every one of the original nine squares. The equality case
has been excluded, rather than weakened to a strict-disk input.

## 3. Six actual boundary neighbors cannot fit in the available angle

Let H be an actual unit with center c and let B be any physical
boundary unit touching H, with center b. Their actual common point
and circumradii give

    |b-c|<=sqrt(2).

Since an actual B corner has radius R,

    |b|>=R-1/sqrt(2)>R-71/100=:rho.                   (20)

Equations (19)--(20) give c!=0 and |b|>rho, |c|>t.
The exact polynomial

    F(R)=rho^2+t^2+(rho*t)/3-2

satisfies

    F(2)=17/2000,
    F'(R)=(7/5)rho-(49/15)t,
    F'(2)=7/15,
    F''(R)=182/25>0.                                 (21)

Thus F(R)>=17/2000 throughout the entire actual interval R>=2.
The expression x^2+y^2+xy/3 is strictly increasing in each
positive variable. By (19)--(21),

    |b|^2+|c|^2+(|b||c|)/3>2.

Combining this with |b-c|^2<=2 and the cosine rule gives the
strict center-direction bound

    cos(angle(b,c))>-1/6,
    angle(b,c)<arccos(-1/6)<5pi/9.                    (22)

The last exact trigonometric comparison follows from sin(pi/18)>1/6:
if s=sin(pi/18) were at most 1/6, then
sin(pi/6)=3s-4s^3<3s<=1/2, a contradiction.

Every boundary neighbor's center direction consequently lies in
the same open interval of length 2 arccos(-1/6)<10pi/9 about
the original nonzero direction of c.

The full force-free theorem `CENTERED_INNER_ARC.md` says that
distinct physical boundary units in this original radius window
have minor center angular separation strictly greater than 2pi/9.
If H had six such neighbors, order their directions in the
displayed interval. Every one of the five consecutive differences
is greater than 2pi/9, since their minor separation is. The total
span would exceed 10pi/9, contrary to (22). This proves the whole
boundary-neighbor theorem.

No boundary unit was assumed to have a positive circle multiplier.
No contact at H was required to carry a positive force. The circle
center, every square frame and all nine original units stayed fixed.

## 4. Three entire original C3.335 bouquet domains are excluded

For the original window 79/40<=R<=sqrt(1105)/16, the accepted
same-nine theorem `NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md` first
gives R>2. This retains that source's reviewed five-charge proof
and its declared prerequisite status. The new Sections 1--3 are
analytic and make no assertion that this inherited lower-bound
source is table-free or that the global prerequisite audit is closed.

Consider the actual common-root bouquet with cyclic orders 3,3,5.
Its two intact triangles at H have four distinct true degree-two
loaded tips. Those four actual physical boundary units all touch H.
The entire five-body block is also retained at H, at its original
degree and with all chords and all possible circle masks.

The complete two-petal theorem
`TWO_INTACT_PETALS_NO_UNLOADED_NEIGHBOR.md` excludes every genuinely
unloaded degree-two neighbor of H. A true degree-two triangle tip
is loaded by the actual touching-neighbor obstruction. An unchanged
true degree-three vertex with two physical edges among its neighbors
is loaded by `NO_UNLOADED_DIAMOND_HUB.md`.

These exact degree rules supply two further distinct boundary
neighbors in each of the following whole original domains:

| Five-body block and actual root | Two further actual boundary neighbors of H |
| --- | --- |
| C5, its root H | Both immediate cycle neighbors have true degree two and cannot be unloaded by the two-petal theorem. |
| House, a hub A=H; edges AT,DT,AD,AB,BC,CD | Roof T is a true loaded degree-two triangle tip. Lower B is a true degree-two neighbor of the two-petal root, so it is loaded too. |
| Fan, an inner path vertex 2=H; hub J and path 1--2--3--4 | Endpoint 1 is a true loaded degree-two triangle tip. Vertex 3 retains true degree three; its neighbors J,2,4 have the two actual edges J2 and J4, forcing its load. |

The indicated vertices are private five-block bodies and are
different from all four intact tips. Each row therefore gives
six distinct physical boundary neighbors of the same actual H,
contradicting Section 3. The reflected house-hub and fan-inner
placements are included by their original graph automorphisms.

The C5 conclusion needs no choice between its remaining internal
private load masks. Every whole root equation, all actual side
means, and all nine physical units remain. The fan-hub bouquet
already excluded by its eight-boundary-body count stays excluded;
it is not counted as a new domain.

Thus the six previously surviving bouquet graph domains in
`MIXED_C3_335_COMPLETE_ATTACHMENT_REMAINDER.md` lose exactly C5,
house-hub and fan-inner. The whole graph domains still requiring
work are the house roof, house lower vertex and fan endpoint
bouquets, and the seven previously listed middle-triangle chains.
This is ten original graph domains, not new IDs. The entire
C3.335.b0 coarse cell is not declared closed here.

The boundary-neighbor theorem is also available in any other
original graph once six distinct physical boundary neighbors
have been proved at their true degrees. No physical motion,
force deletion, normal reselection, numerical pose search,
new scalar certificate, Lean compilation, CI, remote mutation,
or shared-ledger edit is used.
