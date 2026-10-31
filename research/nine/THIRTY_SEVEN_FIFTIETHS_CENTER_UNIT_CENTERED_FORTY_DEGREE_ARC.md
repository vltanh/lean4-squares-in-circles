# A closed forty-degree inner arc for every unit with center radius at least 37/50

Date: October 28, 2026 UTC. Author: root continuation.

**Status: complete proposed uniform geometric hand theorem, frozen for a
separate independent full review. No original gate is declared closed.**
The proof strengthens both the center threshold and the angular width
of the earlier centered radius-9/8 arc. It gives one condition applying
to arbitrary actual units, without any degree, force, load, physical
circle-contact or side-owner premise. All original units remain.

## 1. Complete statement

Let E be an actual closed unit square contained in the disk about O
of squared radius at most

    Q=1105/256.

Let c be its actual center and assume

    r=|c|>=37/50.

Set

    rho=9/8, theta=pi/9.

Then the entire **closed** radius-rho arc centered at the actual
direction c/r, of halfwidth theta, lies in int(E). In particular
both angular endpoints lie in the open actual square. The total
width is exactly2pi/9, or forty degrees.

The conclusion holds at r=37/50, at r=rho, for every own frame and
every containing-radius endpoint. The only containing-radius premise
is R^2<=Q. A physical circle contact is not required; every physical
mask and every individual zero circle coefficient is retained.
No application, actual force, selected normal or side mean is varied.

## 2. Two exact elementary angle bounds

On the interval0<theta=pi/9<pi/6, the triple-angle formulas imply

    cos(theta)>109/116, sin(theta)<13/38.              (1)

Here is a rational verification, without a trigonometric table.
The polynomial4u^3-3u is strictly increasing for u>1/2, and
cos(3theta)=1/2. At the proposed lower endpoint,

    4(109/116)^3-3(109/116)-1/2=-111/390224<0.

Thus the cosine bound follows. The polynomial3v-4v^3 is strictly
increasing on[0,1/2], and sin(3theta)=sqrt(3)/2. Its positive value
at13/38 satisfies

    [3(13/38)-4(13/38)^3]^2-3/4
        =44281/188183524>0.

This proves the sine bound. In particular all comparisons keep
their strict reserves at tau=theta and tau=-theta.

## 3. A sharper whole-orientation affine bound for the actual center

Choose signs and order of the actual own axes of E so the coordinates
of its center are r(x,y), with

    x,y>=0, x^2+y^2=1, t=x+y in[1,sqrt(2)].

Its farthest actual corner gives

    r^2+r t+1/2<=Q.                                  (2)

Put

    L(t)=2243/1200-(141/400)t.

This is positive on the whole displayed t interval. The exact identity

    L(t)^2+t L(t)+1/2-Q
      =-(36519/160000)t^2+(132337/240000)t
         +(2243/1200)^2+1/2-1105/256
      =:P(t)                                        (3)

is a concave quadratic. Its minimum on the entire closed interval
occurs at an endpoint. At those endpoints,

    P(1)=31/57600>0,

    P(sqrt(2))>207277/360000000>0.                    (4)

For the second comparison use sqrt(2)>707/500, with squared reserve
151/250000, in the positive linear term of(3); its quadratic term
uses t^2=2 exactly. This gives the displayed rational number.

Since z^2+t z+1/2 is strictly increasing for z>=0, (2)--(4) prove

    r<L(t).                                         (5)

This bound includes all orientations and uses no lower bound on r.

## 4. One completed-square identity controls every inward coordinate

For the same x,y, the following exact identity holds:

    1/2-(13/16)x-(117/304)y
          +(141/400)x^2+(141/400)xy
      =(37/80)(x+(141/370)y-65/74)^2
        +(12679/296000)(y-6825/7771)^2
        +3497/29529800.                              (6)

Indeed expansion of the right side minus the left side is exactly

    (11/100)(x^2+y^2-1)=0.

Both square coefficients and the constant reserve are positive.
In fact3497/29529800>1/10000, with difference27201/1476490000.

The constants in(1),(5) also satisfy

    2243/1200-(9/8)(109/116)=56519/69600
       =13/16-31/69600<13/16,

    (9/8)(13/38)=117/304.

Consequently(5)--(6), including x=0 or y=0, give the uniform bound

    (r-rho cos(theta))x+rho sin(theta)y
       <=1/2-3497/29529800<1/2.                      (7)

There is no lower center-radius or sign assumption on
r-rho cos(theta) in this argument. Exchanging x,y gives the same
inequality for the other coordinate. The single identity(6) covers
the entire orientation interval; no angle subdivision is used.

## 5. The complete low-center range, with a strict Euclidean reserve

First suppose

    37/50<=r<=rho.

For every actual angular displacement |tau|<=theta, the squared
distance between c and the corresponding radius-rho point is

    r^2+rho^2-2r rho cos(tau)
      <r^2+rho^2-2r rho(109/116)=:G(r).              (8)

The strict inequality follows from(1), since r>0. G is a convex
quadratic, so its maximum on the whole closed r interval is at
an endpoint. The two exact endpoint values and reserves are

    G(37/50)=288491/1160000,
    1/4-G(37/50)=1509/1160000>0,

    G(9/8)=567/3712,
    1/4-G(9/8)=361/3712>0.                           (9)

Thus every point of the entire closed arc has distance strictly less
than1/2 from c. The open center disk of radius1/2 lies in int(E),
regardless of its actual frame. This proves the theorem throughout
the whole low-center interval, including both center endpoints.
No continuity or limiting argument is used to add an endpoint.

## 6. The complete high-center range and both coordinate signs

Now suppose r>=rho. In the same actual own frame, the two coordinates
of the radius-rho point relative to c are

    Delta_1=(rho cos(tau)-r)x-rho sin(tau)y,
    Delta_2=(rho cos(tau)-r)y+rho sin(tau)x.           (10)

Because r>=rho and cos(tau)<=1, their first radial term is
nonpositive. Their outward bounds therefore satisfy

    Delta_1,Delta_2<=rho sin(theta)<117/304<1/2.

For either sign of tau, (7) gives

    -Delta_1
      <=(r-rho cos(theta))x+rho sin(theta)y
      <=1/2-3497/29529800<1/2.

Exchange x,y for the other inward bound. All four comparisons are
strict, including the own-axis and angular endpoints. Both actual
coordinates belong to(-1/2,1/2), proving membership in int(E).

Sections5--6 exhaust r>=37/50. Their overlap at r=rho is retained.

## 7. Uniform packing and boundary-path consequences

### 7.1. At most eight units can have center radius at least 37/50

In an interior-disjoint packing, the closed centered arcs supplied
by the theorem for distinct qualifying units are disjoint: any
common arc point would belong to both actual open squares.
Consequently every successive angular gap between qualifying
center directions is strictly greater than2pi/9. This is strict
even if the arcs would only share an endpoint, because their
closed endpoints lie in the open squares.

Nine qualifying centers would have nine successive positive gaps
whose sum is2pi but whose sum is strictly greater than2pi. Therefore
there are at most eight such actual units. In particular every
packing of nine actual units in the displayed disk has at least
one actual center c with

    |c|<37/50.                                       (11)

This conclusion does not say that O belongs to that unit. It does
not identify the unit with a graph hub or a loaded/unloaded vertex.
No such additional claim is used or credited.

### 7.2. All physical boundary units qualify in the full original window

When79/40<=R<=sqrt(1105)/16, every actual physical boundary unit
has center radius at least R-1/sqrt(2). Since1/sqrt(2)<17/24,

    |c|>79/40-17/24=19/15>37/50.                    (12)

Thus every such boundary unit has the full closed forty-degree arc
on the same radius-9/8 circle. No positive circle coefficient is
needed; the physical corner, including a zero-weight corner, stays.

### 7.3. A contact between two boundary units cannot skip another qualifying center

Let U,V be two distinct physically touching boundary units in that
full radius window, with actual centers u,v. Their common physical
point gives |u-v|<=sqrt(2). Set r=|u|, s=|v|, and let gamma be their
minor angular separation. By(12) and the exact cosine identity,

    cos(gamma)
      =(r^2+s^2-|u-v|^2)/(2rs)
      >=1-1/(rs)>136/361>1/3>cos(2pi/5).

For the final exact comparison use
cos(2pi/5)=(sqrt(5)-1)/4<1/3, since sqrt(5)<7/3.
Therefore

    gamma<2pi/5<4pi/9.                               (13)

If a third actual center with radius at least37/50 lay strictly
between those two center directions in their minor interval, its
two successive arc separations would each exceed2pi/9. Their sum
would exceed4pi/9, contradicting(13). Thus every actual center in
that minor interval, other than u,v, necessarily has radius<37/50.

This is an angular conclusion about actual centers and actual units.
It does not by itself give a capacity bound for centers inside the
small disk, route arbitrary additional units, or exhaust a graph
family. All participating units remain in any later caller.

## 8. Provenance and review boundary

The preceding accepted table-free centered-arc proof is

    BOUNDARY_UNIT_CENTERED_NINE_EIGHTHS_ARC.md
    SHA256 b1f647212d0a1fe44e3cce2f3ea6e2ba12591131445aa1518da063e74c3a118b.

The simultaneously constructed threshold extension is

    THREE_QUARTERS_CENTER_UNIT_CENTERED_NINE_EIGHTHS_ARC.md
    SHA256 c511df67ca7857c3aa85d62c768cb87da428c7eaedd4328d6a9d6bf36dcba16a.

The latter combines pentagon_audit's broader center-domain observation
with root's full-displacement convex quadratic. Both files remain
unchanged. The present proof is printed in full and uses no theorem
from either source as an unverified premise. Its changes are the
sharper affine bound(3), new completed-square identity(6), exact
forty-degree angle comparisons, lower threshold37/50, and their
explicit whole-packing and boundary-path consequences.

The few rational values in(1),(4),(6),(9) are displayed arithmetic
identities within whole-interval analytic inequalities. There is no
enumeration of geometric boxes, pose sample, angle mesh, generated
coefficient table or computational geometric exclusion certificate.
The existing certificate replacements retain their own prior scopes;
this theorem does not claim another retirement without a literal
reviewed caller.

No original flag, metadata ledger, Lean source, workflow or remote
branch is changed. The root author cannot supply the separate
independent review required for adoption. The global sharp theorem,
original equality cases and all remaining families stay open.
