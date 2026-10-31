# The entire upper-B nonpositive North interval is impossible by ordered boundary concurrences

Date: October 29, 2026 UTC. Author: house continuation.

**Status: complete proposed uniform hand theorem, frozen for separate
full independent review.** This excludes the whole original upper-B
North interval e<=x<=0, including both endpoints, every actual BC/CD
owner and mean, and every physical C circle mask. In particular the
previous residual open interval e<x<0 is excluded all at once.

The proof uses the real BC edge and the protected physical order of
the original house. It does not assume an ABC or BD triangle, does not
apply a two-force equation to A or D, and does not infer physical
clearance of D from its zero circle load. The three original extra
units are retained; the contradiction already occurs in the unchanged
six-body component.

## 1. Complete original statement

All actual unit squares have disjoint open interiors and lie in the
same unchanged disk about O=0. Suppose

    2<=R<=sqrt(17)/2,
    d=sqrt(R^2-1/4)-1, 14/15<d<=1,
    e=d-1 in(-1/15,0],
    1/2<=a<=2/3, b=1-a in[1/3,1/2],
    A=[e,d] times [-b,a],
    L=[d,d+1] times [-1/2,1/2].                     (1)

L is the original genuine radial S leaf, with its unchanged inner
application (d,0), positive radial load and actual edge AL. The full
original positive graph is exactly

    AT, DT, AD, AB, BC, CD, AL.                      (2)

The actual degrees are A4,D3,T2,B2,C2,L1. The positive circle loads
are exactly T,B,C,L; D has zero total circle coefficient and may
still physically touch the circle. All original positive forces,
circle coefficients and torques are retained. Use the common already
selected certificate with its compatible protected physical embedding.

The unchanged A-to-B normal is North, with actual application or full
mean

    P=(x,a), e<=x<=d.                               (3)

The unchanged A-to-T normal is South, at an arbitrary original mean
on A's lower side. Hence the actual whole T lies in y<=-b<0.
Every original normal and application of AD,DT,BC,CD is unrestricted
apart from the actual original equations and geometry.

**Theorem.** Necessarily x>0.

There is no annulus premise, including at
e^2+a^2=(R-sqrt(2))^2, and no assumption that any C concurrence lies
in its square. Both interior and exterior physical-two-corner
concurrences will be included explicitly.

The numeric bound d>14/15 in (1) follows already at R=2:
sqrt(15)/2>29/15, since 15/4-(29/15)^2=11/900>0.
The upper bound d<=1 is exactly R<=sqrt(17)/2. Thus both radius
endpoints in the statement are retained.

## 2. A nonpositive original mean forces B's unique physical circle corner

Suppose x<=0. Then

    -1/15<x<=0,
    |P|^2<1/225+4/9=101/225<(67/100)^2.             (4)

If B were parallel to A, its entire actual frame would be

    B=[x-rho,x+1-rho] times [a,a+1], 0<=rho<=1.

Every corner would have absolute first coordinate at most 16/15
and second coordinate at most 5/3. Its squared norm would therefore
be at most

    (16/15)^2+(5/3)^2=881/225<4<=R^2.

That contradicts B's physical boundary status. This excludes the
entire parallel support-side interval, with both rho endpoints and
all original means present.

B is therefore tilted and its unique minimum-y point is P. Write its
complete actual frame as

    u=(p,q), v=(-q,p),
    p,q>0, p^2+q^2=1,
    B=P+[0,1]u+[0,1]v.                              (5)

Set alpha=P.u=xp+aq and beta=P.v=-xq+ap. We have beta>0.
If alpha<=0, its whole own-coordinate interval [alpha,alpha+1]
would have absolute value at most one, by (4). The other interval
[beta,beta+1] would have absolute value below 167/100. Every actual
B corner would then have squared norm below

    1+(167/100)^2=37889/10000<4,

again impossible. Hence

    alpha>0, beta>0,
    Z=P+u+v is B's unique physical circle corner,
    F_B=chi*Z, chi>0.                               (6)

Here F_B is the entire unchanged outward circle-load vector, with
the conventional common factor absorbed into chi. Physical uniqueness
in (6) is a geometric conclusion, not an assumption that follows from
having only one positive individual coefficient.

## 3. The actual loaded B2 and C2 stars have positive proper concurrences

B and C physically touch on their actual positive BC edge. Each is
loaded and has its true full degree two. Apply Lemma 2.1 of
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md separately to these two
unchanged stars. Its literal premise is only one physical boundary
neighbor, not a triangle on the two neighbors of the tip.

Their two actual pair-force lines are nonparallel. They have positive
proper concurrences Q_B and Q_C: each is a positive multiple of its
own entire circle-load vector, and for every actual point or full
mean M with original outward unit normal n,

    M-Q_i=ell*n, ell>=0.                            (7)

Coincident applications are expressly included, with the concurrence
equal to that actual point and the corresponding coefficients zero.
Variable shared-side means remain the original means in (7).

Because B has the unique physical corner (6), the same lemma gives
Q_B in B. Its original B-to-A normal line is the vertical line
through P. Thus, for some lambda>0,

    Q_B=lambda*Z,
    (Q_B)_x=x, (Q_B)_y>=a>=1/2.                     (8)

Let g be the original B-to-C unit normal, let mu>0 be its magnitude,
and let nu>0 be the original AB magnitude. The entire B2 equation is

    chi*Z-nu*North+mu*g=0.                          (9)

If x=0, (8) gives Z_x=0 and (9) gives g_x=0. The two pair-force
lines would be parallel, contrary to the complete lemma. This
excludes the zero-mean endpoint. Henceforth

    x<0, Z_x<0, g_x=-chi*Z_x/mu>0.                  (10)

Define theta_B=arg(F_B)=arg(Q_B)=arg(Z), with the ordinary lift in
(0,2pi). From (4),(8),

    pi/2<theta_B<3pi/4.                             (11)

Indeed the second coordinate of Q_B is at least 1/2 whereas the
absolute value of its negative first coordinate is below 1/15.

The actual B center is

    c_B=P+(u+v)/2=(P+Z)/2.

Both summands have negative first coordinate and strictly positive
second coordinate, by (1),(5),(6),(8),(10). Its actual angle phi_B
therefore satisfies

    pi/2<phi_B<pi.                                  (12)

We will also need a uniform lower bound for the entire C concurrence:

    |Q_C|>1/2.                                      (13)

Here are all the mask and application cases, without an interior
assumption for an exterior concurrence.

* If C has one physical circle corner, the complete lemma places
  Q_C in C. Every point Y of a physical boundary unit satisfies
  |Y|>=R-sqrt(2)>=2-sqrt(2)>1/2, by its actual diameter and one
  circle corner. This proves (13).
* If the two C applications coincide, their concurrence is that
  actual point of C, so the same diameter argument proves (13),
  whatever the physical mask.
* In the remaining physical-two-corner case, choose the actual
  radial own frame C=[d,d+1] times [-1/2,1/2]. The full rectangle
  calculation in the cited lemma gives

      Q_C=tau*(d+1,eta), |eta|<=1/2,
      tau>=d/(d+1)>0.

  Consequently its first coordinate in that actual own frame is
  at least d>14/15>1/2. This includes tau>1, either zero individual
  corner coefficient and the endpoints eta=+/-1/2. It proves (13)
  for every remaining physical C mask.

The two-corner coordinates in this paragraph are orthonormal radial
coordinates of the actual C, not the ambient coordinates of (1).
The norm statement (13) is invariant under that coordinate choice.

## 4. Protected physical order puts the entire C resultant well to the left

We first establish the actual angular lift, rather than selecting a
favorable abstract drawing of (2).

The block in (2) is the theta graph with the three actual A-to-D
paths AD, A--T--D, and A--B--C--D. In its compatible selected
embedding, the exterior cycle must include A--T--D because T is a
physical boundary unit with a protected outward circle spoke. It
must include A--B--C--D for the same reason using B or C. Hence
the actual exterior cycle is

    A--B--C--D--T--A.                               (14)

The real AL strand and a real L circle spoke provide an exterior
access at A. The other actual physical boundary spokes are preserved
simultaneously by the same compatible embedding. Their annular order
is the order of (14), with L inserted at A. This is precisely the
frame-independent fact proved in Sections 2 and 4.1 of
TILTED_S_ROOT_HOUSE_TCB_AND_INNER_FAN_COMPLETE_DOMAIN_EXCLUSION.md.
Its proof requires no tilted root or high coordinate. Zero-load
physical circle contacts of D are retained as additional protected
spokes between C and T; they do not alter the indicated subsequence.

For clarity, the corner-to-center passage and the resultant passage
use whole physical angular intervals. The force-free center theorem
CIRCLE_CONTACT_ANGULAR_ORDER.md gives, for any two distinct physical
boundary units, minor center angular separation strictly greater
than pi/5. GENERAL_BOUNDARY_CHORD_OUTER_CYCLE_ORDER_EXCLUSION.md,
Section 4, gives angular distance strictly less than pi/12 from
each physical circle corner to its own actual center direction.
Both sources apply on the larger original window
79/40<=R<=sqrt(1105)/16, which contains (1).

One may check the latter one-square estimate directly. In outward
own coordinates at a circle corner, write

    z=(A_0,B_0), A_0>=B_0>=1/2,
    A_0^2+B_0^2=R^2,
    c=(A_0-1/2,B_0-1/2).

The tangent of their acute angular deviation is
(A_0-B_0)/(2R^2-A_0-B_0). At fixed R it is largest at B_0=1/2,
where it is 1/(2sqrt(R^2-1/4)). Since R^2>=4>2+sqrt(3), this is
strictly smaller than tan(pi/12)=2-sqrt(3).

Put the open interval of radius pi/12 around each physical center
direction. These intervals are pairwise disjoint, because their
two radii total pi/6<pi/5. All physical circle corners of a unit
lie in its own interval, including a zero-coefficient physical corner.
The direction of its nonzero full circle resultant lies in the same
interval: it is a positive sum of vectors in an open cone of width
pi/6<pi. No mask is replaced by just one selected corner.

Moving the chosen corners within these disjoint intervals to their
centers preserves the protected cyclic order. Now the actual L
center has angle zero. By (12), the B center is in the open upper
left quadrant. The entire T is below y=-b<0, so its center is in
the open lower half-plane. These observed positions fix the common
orientation of the protected subsequence. With lifts in (0,2pi),

    0=phi_L<phi_B<phi_C<phi_T<2pi.                   (15)

In particular no opposite choice of orientation or supplementary
arc has been tacitly chosen for C. Each non-L center has circular
distance greater than pi/5 from phi_L=0. Its whole radius-pi/12
interval therefore stays in (0,2pi). The corresponding ordinary
intervals follow the order (15). Thus, for
theta_C=arg(F_C)=arg(Q_C),

    theta_B<theta_C<2pi,
    theta_C>phi_C-pi/12
           >phi_B+pi/5-pi/12
           >37pi/60.                               (16)

The second strict comparison uses the actual center separation of
B and C. That lower bound holds for their positive counterclockwise
gap in (15) whether or not the gap is itself the minor one.

The real BC contact now supplies an upper bound. Theorem A.2 of
ACUTE_LOADED_CONTACT_GRAPH.md applies because
R^2>=4>2+sqrt(3). Every physical B circle corner has strictly positive
dot product with every physical C circle corner. Summing with the
unchanged nonnegative coefficients, positive in total on both bodies,
gives

    F_B.F_C>0.                                      (17)

Let Delta=theta_C-theta_B. Equations (11),(16) give
0<Delta<2pi-theta_B<3pi/2. On this entire interval, cos(Delta)>0
from (17) forces Delta<pi/2. Hence

    37pi/60<theta_C<theta_B+pi/2<5pi/4.              (18)

This whole interval is contained in (7pi/12,17pi/12). Consequently

    cos(theta_C)<-sin(pi/12)<-1/4.                  (19)

For the last exact comparison,
sin(pi/12)=(sqrt(6)-sqrt(2))/4>1/4:
sqrt(6)>1+sqrt(2) is equivalent to 3>2sqrt(2), and then to 9>8.
No numerical angle sample enters (15)--(19).

Combining the full-mask norm estimate (13) and (19),

    (Q_C)_x=|Q_C|*cos(theta_C)<-1/8.                 (20)

## 5. The two original proper BC rays give the opposite order

Let M be the original actual BC application or its complete original
shared-side mean. The B-to-C normal is the same original g from (9),
and the C-to-B normal is -g. Apply (7) at these exact two ends:

    M-Q_B=ell_B*g, ell_B>=0,
    M-Q_C=-ell_C*g, ell_C>=0.

Subtracting these unchanged mean identities gives

    Q_C-Q_B=(ell_B+ell_C)*g.                         (21)

This remains valid when one or both coefficients vanish. There is
no need to strengthen properness to strict properness or to move a
mean to a selected side endpoint. By (8),(10),(21),

    (Q_C)_x>=x>=e>-1/15.                            (22)

But (20) says (Q_C)_x<-1/8<-1/15. This is a contradiction.
It excludes every x<0 in the stated original interval, including
x=e. The endpoint x=0 was excluded directly in Section 3. Therefore
the whole nonpositive interval is impossible, and x>0 as claimed.

## 6. Reusable geometric content and exact original scope

The argument is an ordered two-tip obstruction: an actual vertical
incoming normal at a loaded upper tip with a small negative horizontal
application makes its other outward normal point right. If its real
loaded boundary neighbor follows it in the protected circle order,
the center separation and acute contact force that neighbor's entire
positive proper concurrence into a left half-plane. The unchanged
two-ended proper contact identity then contradicts that direction.

The actual whole circle resultant, rather than a unique-circle
surrogate, is used at C throughout. Thus the same proof covers every
BC/CD side owner, both full shared-side intervals, coincident C
applications, physical-two-corner exterior concurrences, either
zero individual corner coefficient, and both sharp radius endpoints.
No extra D normal, geometric clearance or equation was introduced.

For the original low aligned house with upper B North and lower T
South, (1)--(3) are exactly its original chart and force features.
Thus this theorem discharges the entire upper-B North nonpositive
interval, including the last e<x<0 branch left by the earlier
positive-upper-moment cap argument. The present source does not
itself assemble the strictly tilted root, high aligned root, West,
Northwest or positive North/Northeast cases into an original-family
closure. That full source/review join is a separate reviewable step.

## 7. Exact complete operative sources

| Complete source | SHA256 | Literal operative scope |
| --- | --- | --- |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Complete Lemma 2.1, applied only to the actual full loaded B2 and C2 stars with their real physical boundary BC neighbor; distinct/nonparallel conclusions, proper rays, unique-mask interior concurrence, coincident applications, and full two-corner lower radial coordinate including exterior and zero-weight endpoints |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 | Whole force-free Lemma 2.1 giving strict pi/5 separation for actual physical boundary centers, with all masks and zero loads |
| GENERAL_BOUNDARY_CHORD_OUTER_CYCLE_ORDER_EXCLUSION.md | 13abf52906294b994c078598985d656b65d4267faa67a6b7b17ee8bc25c11273 | Full protected corner/center order passage and Section 4 one-square strict pi/12 deviation; the angle proof is also displayed here, and no unrelated graph-family exit is imported |
| ACUTE_LOADED_CONTACT_GRAPH.md | e6ce319da0dfb6b3d885584e521edc15834132a349674a3b580771e54d236f59 | Complete Theorem A.2 at the actual BC physical contact and its full positive weighted-sum consequence, including zero individual circle coefficients |
| TILTED_S_ROOT_HOUSE_TCB_AND_INNER_FAN_COMPLETE_DOMAIN_EXCLUSION.md | 4550f191a5c3d93eed4ca8516f9ecff4932e53be4019e1cd54d54ca83425a802 | Only the complete frame-independent protected block/leaf order in Section 2 and the actual house exterior theta cycle in Section 4.1; no tilted-coordinate or high-coordinate premise is imported into the aligned caller |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Entire compatible selected physical embedding and simultaneous protected circle spokes/accesses, including every weak junction and zero-load physical boundary square |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original complete positive graph, two-ended equal-and-opposite pair applications, full true-tip force/torque equations, unchanged shared-side means and nonnegative circle weights |

All listed complete sources have been read at their literal scopes.
No older review is counted as a review of this new geometric join.
The parent requested work on the entire remaining negative North
branch; the author supplied the angular/proper-ray argument and its
estimates. No pose sampling, new computational packing certificate,
Lean/Lake, CI, ledger edit, staging, commit or remote mutation was
performed for this source.
