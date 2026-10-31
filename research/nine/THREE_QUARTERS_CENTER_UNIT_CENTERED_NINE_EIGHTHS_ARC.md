# Every unit with center radius at least three quarters contains the same closed centered inner arc

Date: October 28, 2026 UTC. Author: pentagon_audit continuation, now in
construction role.

**Status: complete new whole-domain hand theorem, frozen for separate
independent review and root adoption.** The original inner radius and
halfwidth are unchanged. The center-radius threshold is reduced from
27/20 to 3/4. The theorem applies to physical circle-clear units as
well as boundary units. It introduces no force, degree, graph, mask
or side-ownership hypothesis.

## 1. Complete physical statement

Retain the original circle origin and radius interval

    79/40<=R<=sqrt(1105)/16.

Let E be any actual closed unit square contained in that circle, with
actual center c satisfying

    r=|c|>=3/4.

Put

    Q=1105/256, rho=9/8, beta=atan(7/20).

**Theorem.** Every radius-rho point whose angular distance from the
actual direction c/r is at most beta lies in int(E). Thus the entire
closed centered arc, including both angular endpoints, lies in the
open interior of the actual unit.

The statement includes r=3/4, both original containing-radius
endpoints, every unit orientation and every original physical
one-/two-corner circle mask. No circle contact is required. A
physical circle corner with zero force coefficient remains untouched.
Every application or full shared-side mean in a larger packing is
unchanged.

Only the upper bound R^2<=Q enters the proof. In particular no
radius-two lower theorem or physical boundary-center lower bound
is silently assumed. The original full window above is an explicit
valid domain of this theorem.

## 2. Complete uniform upper bound for the actual center

Choose the signs and order of E's own orthonormal coordinates so its
center has coordinates r(x,y), with

    x,y>=0, x^2+y^2=1.

These are coordinates of the same actual square about the same
origin. Its farthest actual corner gives

    r^2+r(x+y)+1/2<=Q.                                (1)

Write t=x+y, so 1<=t<=sqrt(2), and set

    L(t)=28/15-(7/20)t>0.

The exact identity is

    L(t)^2+t L(t)+1/2-Q
      =-(91/400)t^2+(14/25)t-19121/57600
      =:P(t).                                       (2)

P is concave. Its minimum on the whole closed interval is therefore
at an endpoint. The two strict endpoint bounds are

    P(1)=31/57600>0,

    P(sqrt(2))=-(91/200)+(14/25)sqrt(2)-19121/57600
                >3799/1440000>0.                    (3)

For the second use sqrt(2)>141/100, whose squared reserve is
119/10000. The comparison function z^2+tz+1/2 is strictly
increasing for z>=0. Equations(1)--(3) therefore imply the
whole-orientation strict bound

    r<L(t).                                         (4)

No lower center-radius assumption is used in this section except
r>0 to define its direction.

## 3. A complete inward-coordinate inequality with a strict reserve

For all the same actual r,x,y,

    (r-135/128)x+(3/8)y<=1/2-11/1840<1/2.             (5)

Indeed 28/15-135/128=1559/1920<13/16. Using(4) and x>=0,
the left side of(5) is at most

    (13/16)x-(7/20)x^2-(7/20)xy+(3/8)y.

The following exact identity holds when x^2+y^2=1:

    1/2-(13/16)x-(3/8)y+(7/20)x^2+(7/20)xy
      =(9/20)(x+(7/18)y-65/72)^2
        +(23/720)(y-85/92)^2+11/1840.                (6)

To verify it, the right side expands to

    (9/20)x^2+(7/20)xy+(1/10)y^2
       -(13/16)x-(3/8)y+2/5.

Its difference from the left side is
(1/10)(x^2+y^2-1), exactly zero. Both squared-term coefficients
are positive. This proves(5), including x=0 or y=0.

Sections2--3 reproduce the complete affine and completed-square
argument in the accepted table-free centered-arc proof. There is
no Bernstein table, orientation mesh or sampled inequality here.

## 4. The full closed arc at the new center threshold

The exact angle beta has

    cos(beta)=20/sqrt(449)>15/16,
    sin(beta)=7/sqrt(449)<1/3.                        (7)

The squared integer reserves are respectively 1375 and 8:

    400*256-225*449=1375>0,
    449-49*9=8>0.

For any actual angular displacement |tau|<=beta, write v for the
radius-rho point and c for the actual center. In E's own frame its
two relative coordinates are

    Delta_1=(rho cos(tau)-r)x-rho sin(tau)y,
    Delta_2=(rho cos(tau)-r)y+rho sin(tau)x.           (8)

We prove both coordinates lie strictly between -1/2 and 1/2 by two
complete closed center-radius ranges.

### 4.1. The entire lower range 3/4<=r<=rho

The squared length of the actual displacement, independently of
the own-frame orientation, is exactly

    |v-c|^2=r^2+rho^2-2r rho cos(tau).

By(7), r>0 and|tau|<=beta,

    |v-c|^2<r^2+rho^2-(15/8)r rho=:G(r).             (9)

G is a convex quadratic in the actual center radius. Its maximum
on the full closed interval[3/4,9/8] is at one of the two endpoints.
Those exact values are

    G(3/4)=63/256<1/4,
    G(9/8)=81/512<1/4.                              (10)

Their positive reserves below 1/4 are respectively 1/256 and 47/512.
Thus |v-c|<1/2 on this entire closed range. Each own-coordinate
absolute value is at most that displacement length, so

    |Delta_1|<1/2, |Delta_2|<1/2.

This argument includes r=3/4, r=rho and both angular endpoints.
It bounds the displacement of every actual arc point, without
choosing a favorable square orientation.

### 4.2. The entire upper range r>=rho

Now rho cos(tau)-r<=0. Since x,y>=0, the positive part of
either coordinate in(8) is bounded above by

    rho sin(beta)<3/8<1/2.                           (11)

For the other sign use the complete inward inequality(5):

    -Delta_1
       <=(r-rho cos(beta))x+rho sin(beta)y
       <=(r-135/128)x+(3/8)y
       <=1/2-11/1840<1/2.                           (12)

Exchanging x,y and reversing tau gives the same strict bound for
-Delta_2. All axes x=0 or y=0, r=rho and|tau|=beta remain
included. The lower and upper arguments overlap at r=rho.

Equations(9)--(12) put both coordinates in the strict open unit
interval for every r>=3/4. This proves membership in int(E)
for the whole closed centered arc, including both endpoints.

## 5. Whole-window boundary consequence and exact packing exports

Every physical boundary unit in the original full radius interval
satisfies the new center threshold. An actual containing-circle
corner is at distance 1/sqrt(2) from its center, so

    |c|>=R-1/sqrt(2)
        >79/40-17/24
         =19/15>3/4.                                (13)

Thus every original boundary unit, including throughout the strict
low-radius window and at R=79/40, has the same complete closed
centered radius-9/8 arc in its actual open interior. Its total
circle coefficient and each individual corner coefficient are
irrelevant. This consequence does not shorten any body equation.

The theorem also gives the following precise arbitrary-unit
consequences in an interior-disjoint packing:

* Any two distinct units whose actual center radii are at least 3/4
  have minor center-angle separation strictly greater than 2beta.
  Otherwise their two closed centered arcs would meet at a point
  in both actual open interiors.
* In a minor angular interval between two such centers with
  length at most 4beta, no third actual center with radius at
  least 3/4 can lie between them. The two successive strict
  separations would have sum greater than 4beta.

These are physical angular consequences, with all original units
retained. They do not assert that every unit in an arbitrary
nine-square packing meets the center threshold. Any caller must
prove it separately for each participating nonboundary unit.
A unit whose center radius is below 3/4 is not removed, moved
or counted by either stated corollary.

## 6. Provenance, frozen inputs and review boundary

The first version of this construction used the valid threshold 5/6:

    FIVE_SIXTHS_CENTER_UNIT_CENTERED_NINE_EIGHTHS_ARC.md
    SHA256 261dec786c74ecd8eddf3daaff7a627f703ef1b4f7c06c773f5e9d98d373022b

Its exact bytes are preserved as construction provenance. Root then
supplied the whole-displacement comparison(9), the clean stronger
threshold 3/4 and both exact endpoint values(10). The author checked
the complete new radius split, its strict margins, every actual
coordinate and all angular endpoints. That contribution is explicitly
construction input from root, not an independent audit. The present
full theorem requires a separate complete independent review.


The existing accepted source whose full current proof was read is

    BOUNDARY_UNIT_CENTERED_NINE_EIGHTHS_ARC.md
    SHA256 b1f647212d0a1fe44e3cce2f3ea6e2ba12591131445aa1518da063e74c3a118b

Its declared center threshold is27/20; its original inner radius,
closed halfwidth and full high-boundary exports remain unchanged.
This manuscript changes none of its bytes or caller pins.
Its table-free coordinate calculation is printed in full again
in Sections2--3, so the present proof has no hidden conditional
old radius or center premise.

The new contribution is the complete low-center displacement estimate
(9)--(10), joined to the fully printed old coordinate inequalities
on r>=rho. Its two closed radius branches prove strict interior
membership at every own frame and angular endpoint. Section5 spells
out the larger full-window physical boundary scope and the exact
conditional packing consequences.

This theorem does not close an original graph, load family, parent
or coarse gate. A later house or capacity caller must supply its
whole original physical configuration and every required actual
center threshold before applying it.

No original force, degree, support normal, application, shared mean,
physical circle mask, zero weight or completion unit was changed.
No numerical pose search, computational exclusion certificate,
Lean/Lake execution, compilation, CI, workflow, metadata edit,
staging, commit or remote action was used. The author will not
independently review this new construction; a separate reviewer
must check the full theorem at its frozen bytes.

