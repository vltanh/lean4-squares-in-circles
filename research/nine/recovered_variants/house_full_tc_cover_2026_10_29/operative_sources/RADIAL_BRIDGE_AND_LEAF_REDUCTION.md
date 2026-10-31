# n=9: radial bridges, a four-square central cover, and exact boundary-leaf elimination

**Status: proved hand necessary-condition theorems for the unrestricted physical stress.**
These results apply to arbitrary individual square orientations. They use the
physical force/application-point certificate of
[PHYSICAL_CONTACT_STRESS.md](PHYSICAL_CONTACT_STRESS.md), not an assumed
common coordinate frame. They restrict **every bridge and every loaded leaf**
of that certificate, rather than a small tilt or radius window.

**Not proved here:** the sharp inequality for all cyclic/branching cores and
all unstressed-square completions. Consequently the unrestricted n=9 optimum
and global equality classification remain OPEN. No Lean compilation or
independent full manuscript audit is claimed.

## 1. Setup and graph conventions

Put Q = 1105/256. Translate the disk center to the origin and write its
radius R. For a nine-square packing of interest, R <= sqrt(Q). Also
R > sqrt(2): otherwise its disk has area at most 2*pi < 8, while the
nine interior-disjoint unit squares have total area nine.

At an unrestricted global minimizer, use the physical stress of
PHYSICAL_CONTACT_STRESS.md. Aggregate all positive collinear forces on a
shared side into one force at their weighted-average point in the actual
shared segment. Let G be the resulting **simple positive body-pair graph**.
An edge e = i -> j has weight mu_e > 0, unit normal d_e pointing from i
into j, and a genuine common application point p_e. Square i is on the
lower side and j on the upper side of the supporting line:

    d_e . x <= d_e . p_e   (x in S_i),
    d_e . x >= d_e . p_e   (x in S_j).

The graph need not be planar; the separate contact-incidence graph is.
A **bridge** always means a bridge of this positive body-pair graph,
not an arbitrary contact, a selected SAT row, or an incidence spoke.
Circle atoms have weights lambda_ik >= 0 and vertices v_ik on |v| = R.
The physical center and angular equations, for J(x,y)=(-y,x), are

    2 sum_k lambda_ik v_ik + sum_e s_ie mu_e d_e = 0,                (1)
    2 sum_k lambda_ik v_ik . J(v_ik-c_i)
        + sum_e s_ie mu_e d_e . J(p_e-c_i) = 0.                   (2)

Here s_ie = +1 at the tail and -1 at the head. The total circle weight
is one. All statements below remain true after retaining and normalizing
one connected positive component.

## 2. Cut force and cut moment: every bridge is radial

**Lemma 2.1 (moment identity about the disk center).** For every square,

    sum_e s_ie mu_e d_e . J p_e = 0.                              (3)

*Proof.* Dot (1) with J c_i and add it to (2). The circle terms become
2 sum lambda_ik v_ik . J v_ik = 0. The contact terms give (3). QED.

For an arbitrary set A of bodies, sum (1) and (3). Internal edge terms
cancel, because both bodies use the **same physical application point**:

    2 sum_{i in A,k} lambda_ik v_ik
        + sum_{e across A} s_Ae mu_e d_e = 0,                     (4)
    sum_{e across A} s_Ae mu_e d_e . J p_e = 0.                   (5)

**Theorem 2.2 (radial bridge law).** If e is a bridge, then

    d_e . J p_e = 0.                                             (6)

Thus its force line passes through the disk center. If p_e != 0,
its normal is parallel to p_e. This is exact, with no angle estimate.

*Proof.* Delete the bridge and take A to be either component. Its only
positive crossing edge is e. Equation (5), with mu_e > 0, gives (6).
QED.

Both cut components carry positive total circle weight. Indeed, if the
circle weight alpha_A on one side were zero, (4) would say mu_e d_e=0.
Moreover their circle-contact barycenters are oppositely directed on the
bridge force line. Writing alpha_B for the other weight gives

    mu_e <= 2 R min(alpha_A, alpha_B).                            (7)

This follows from (4) and |sum lambda v| <= R sum lambda.
These are cut constraints, not an assertion that each circle vertex
itself lies on the bridge line.

**Necessary limitation:** a nonbridge edge can be nonradial. In the
record witness's seven-body cycle, horizontal forces act at height
45/128, so their force lines do not pass through zero. Do not apply
(6) to all contacts.

## 3. Every bridge touches a tiny central disk

**Lemma 3.1 (inward unit segment in a square).** Let a unit square S
have support point p in unit outward-normal direction d. Then

    p - t d belongs to S for every 0 <= t <= 1.                  (8)

*Proof.* In orthonormal square coordinates, each component of p-c is
in [-1/2,1/2]. If d has a nonzero component, support maximization
places that coordinate of p-c at the endpoint with the same sign.
Subtracting t times that component moves inward by at most one,
since t <= 1 and every component of a unit vector has absolute
value at most one. A zero component does not move. Both coordinates
therefore stay in the unit square. QED.

**Theorem 3.2 (central endpoint of every bridge).** Define

    delta(R) = max(R-2, 0).                                      (9)

At least one square incident to every positive bridge meets the closed
disk |z| <= delta(R). The other incident square has p_e as its unique
nearest point to the origin whenever p_e != 0 and labels are chosen
so that it lies on the outer side.

*Proof.* If p_e=0, both incident squares contain the origin. Otherwise,
by Theorem 2.2 choose the sign of the normal and the two labels so that
p_e=r d, r=|p_e|>0. Write S for the inner body, with d.x <= r, and T
for the outer body, with d.x >= r. The width of T in direction d is
at least one. Disk containment therefore implies

    r + width_T(d) <= R, hence r <= R-1.                         (10)

By Lemma 3.1, S contains the whole segment p_e-t d, 0<=t<=1.
If r<=1, it contains zero. If r>1, it contains (r-1)d, whose norm
is at most R-2. This proves the asserted central endpoint.
For T, every x has |x| >= d.x >= r, with equality only at x=r d=p_e.
Thus p_e is its unique nearest point. QED.

**Corollary 3.3 (central bridge squares are geometrically circle-clear).**
No square meeting the disk in (9) touches |z|=R when R>sqrt(2).
In particular every such square has zero circle stress weight.

*Proof.* If z is a point of that square with |z|<=delta(R), and v is a
point of the same square with |v|=R, then

    |v-z| >= R-delta(R) = min(R,2) > sqrt(2).

This exceeds the diameter sqrt(2) of a unit square. QED.

This conclusion concerns **physical circle clearance**, not merely a
chosen multiplier that happens to be zero.

## 4. There are at most four central bridge squares

Let C be the set of all nine squares meeting |z|<=delta(R). Their
centers satisfy

    |c| <= delta(R) + sqrt(2)/2 < 19/24.                         (11)

For R<=2 the bound follows directly from sqrt(2)/2<17/24. For R>2,
use the exact comparisons

    Q < (25/12)^2,        1/2 < (17/24)^2,

which imply delta(R)+sqrt(2)/2 < 25/12-2+17/24 = 19/24.

**Lemma 4.1.** Five points in the open disk of radius 19/24 cannot
have pairwise Euclidean distances at least one.

*Proof.* If one is zero, its distance to every other is below one.
Otherwise order the five polar angles. Some successive angular gap
is at most 2*pi/5. For the associated radii r,s in [0,a], a=19/24,
the squared distance r^2+s^2-2rs cos(theta) is separately convex in
r and s, so its maximum on that rectangle occurs at a corner. Since
cos(2*pi/5)=(sqrt(5)-1)/4>1/4, that maximum is strictly below

    max(a^2, (3/2)a^2) = 1083/1152 < 1.

This contradicts the required separation. QED.

Every pair of interior-disjoint unit squares has centers at distance
at least one, because their open inscribed disks of radius 1/2 are
disjoint. Applying Lemma 4.1 to (11) gives:

**Theorem 4.2 (four-square bridge cover).** There is a set C of at
most **four** physically circle-clear squares such that **every
positive body-pair bridge has an endpoint in C**. In graph language,
C is a vertex cover of the bridge set. In particular:

- a bridge cannot join two circle-loaded squares;
- an edge joining two squares outside C lies on a positive-stress
  cycle, if that edge is positive;
- the full packing still has nine squares, including every square
  with zero stress. At least five bodies lie outside C, but some
  may be unstressed; no lower bound on the number of cyclic bodies
  follows merely by counting these five.

This does NOT make C a vertex cover of all positive edges or all
physical contacts. It is a cover of **bridges only**.

## 5. Choose away point-only vertex/vertex bridges off the origin

At a point-only contact where p is a vertex of both squares, the two
right-angle tangent cones share no ray; otherwise the intersection
would contain a segment. Consequently there is an open interval of
common support-normal directions strictly exposing p in both squares.
This is the local construction already used in
PHYSICAL_CONTACT_STRESS.md, Section 2.2.

If p!=0, choose such a normal d **not parallel to p**. Removing the
at most two radial unit directions from a nonempty open interval
leaves a choice. Make these choices for all the finitely many such
pairs before the physical active-gradient argument. The same strict
center-expansion direction and <=27-atom existence proof apply.

**Theorem 5.1 (cycle condition for off-origin corner/corner forces).**
A physical minimizing stress can be chosen so that every positive
point-only vertex/vertex edge at p!=0 lies on a cycle of its positive
body-pair graph. It cannot be a bridge, by Theorem 2.2 and the chosen
nonradial normal.

The assertion is an **existence of a suitable certificate**, not a
claim about every possible stress certificate. Contacts at p=0 are
excluded from this normal-choice argument; their incident squares
are already among the central bodies.

## 6. Complete geometry of any circle-loaded degree-one body

Consider a circle-loaded square L of degree one in the positive
body-pair graph. It may have other actual contacts carrying zero
stress; those physical obstacles must not be forgotten. Its only
positive edge is a bridge. Let lambda_L>0 be its total circle weight.
By Corollary 3.3, L is the outer, not the central, endpoint. Thus
its contact point is p=r d, r>0, with L on the outer side and d
pointing outward from the origin. Put

    T = sqrt(R^2 - 1/4).

**Theorem 6.1 (two and only two loaded-leaf forms).** Exactly one of
the following forms occurs, modulo frame signs and quarter-turns.

**D: radial diagonal leaf.** There is one circle-contact vertex
carrying positive stress, namely R d. The opposite vertex is the
bridge contact. Necessarily

    p = (R-sqrt(2)) d,
    c_L = (R-1/sqrt(2)) d,
    mu = 2 lambda_L R.                                         (12)

The square diagonal is parallel to d. Both side axes make an
unsigned angle pi/4 with d.

**S: radial side-normal leaf.** There are two adjacent loaded circle
vertices, with equal weights lambda_L/2, namely

    T d + (1/2) Jd,       T d - (1/2) Jd.

Necessarily

    p = (T-1) d,
    c_L = (T-1/2) d,
    mu = 2 lambda_L T.                                         (13)

The square sides are parallel/perpendicular to d and p is the
**midpoint** of its inner side. This midpoint belongs to the actual
shared segment or point contact with its neighbor.

*Proof.* Use square coordinates so the center has nonnegative
coordinates (a,b). Since R>sqrt(2), the center is not zero. The
farthest corner is unique when a,b>0; when exactly one coordinate
is zero, the two adjacent corners on the far face are the only
possible circle contacts. No other square vertices can carry
positive circle weight.

If there is only one positive circle atom v, force balance gives
v=R d. The circle tangent at v strictly exposes this corner: a
second point with projection R onto d would be outside the circle.
Thus d is not a side normal. Its opposite support point p is the
opposite corner. Both p and v lie on the same radial line, and
the difference of opposite unit-square corners has length sqrt(2).
Therefore v-p=sqrt(2)d and (12) follows. This also forces a,b>0
in appropriate own-frame signs, so the other circle corners are
strictly interior to the disk in this case.

Otherwise choose coordinates with c_L=(a,0), a>0. Put T=a+1/2.
The two circle vertices are v_+=(T,1/2), v_-=(T,-1/2), and
R^2=T^2+1/4. Their weighted mean has the form (T,eta), where
-1/2<=eta<=1/2. Force balance makes d parallel to this mean.
Since R>sqrt(2), T>1.

If eta>0, the unique negative support point of L in direction d
is (T-1,-1/2). Its first coordinate is positive and its second
negative, so it cannot equal a positive multiple r d of (T,eta).
That contradicts the radial bridge law. If eta<0 the reflected
argument applies. Therefore eta=0, the two weights are equal,
d is the square side direction, and radiality puts p at (T-1,0).
This gives (13). QED.

**Corollary 6.2 (where a leaf can attach).**
- For a D leaf, r=R-sqrt(2)<1 at R<=sqrt(Q). Its neighbor contains
  the origin, by Lemma 3.1.
- For an S leaf, its neighbor meets the disk of radius
  max(T-2,0). This is a stronger exact bound than (9).
- Under the normal selection of Theorem 5.1, a D leaf cannot have
  a vertex/vertex bridge. Its vertex meets the relative interior
  of its neighbor's side, so their frames differ by exactly pi/4
  modulo square symmetries.

These are complete leaf formulas, not small-angle approximations.
A leaf can be eliminated from symbolic center/angle bookkeeping by
replacing it with the corresponding radial load and one of the two
exact contact radii in (12)--(13). Its physical occupied square must
still be retained when checking completion by the other bodies.

## 7. Gate impact and exact remaining work

**Closed by this manuscript:** O3.1g.1 cut force/moment identities;
O3.1g.2 radial bridge law and the four-square circle-clear bridge
cover; O3.1g.3 a certificate with no off-origin vertex/vertex
bridges; O3.1g.4 the complete S/D loaded-leaf normal forms.

The current unrestricted input is therefore stronger than mere
planarity and <=27 terms: bridges are radial, their inner endpoints
belong to at most four circle-clear central squares, off-origin
corner/corner positive edges are cyclic in a suitable certificate,
and every loaded leaf has one of two explicit radial geometries.

**Still OPEN:** a sharp q>=Q theorem for the remaining realizable
cyclic/branching core together with all unstressed-square completions.
These reductions do not bound the optimum merely by labeling a graph.
In particular, a stress component can use fewer than all nine squares;
the presence and nonoverlap of the remaining squares are essential.

The accompanying exact regression script checks physical examples,
all their circle/contact force and torque equations, bridge cuts,
normal-choice algebra, and the rational constants. Such regressions
are not a proof of universal optimality or an independent review of
the general arguments above. No Lean or CI is run.
