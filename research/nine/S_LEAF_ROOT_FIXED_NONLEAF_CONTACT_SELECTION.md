# Fixed nonleaf contacts at an S-leaf root have side owners

Date: October 26, 2026.

**Status: complete uniform hand selection candidate, pending fresh
independent full review.** This theorem removes both the physical
triangle premise and the boundary-neighbor degree premise from the
earlier two selection sources. The remaining collinear determinant
degeneracy is excluded by the actual singleton geometry and the
existing strict point-normal convention.

It is a whole-feature reduction. It does not close a whole original
gate or replace a variable shared-side mean by fixed data.

## 1. Exact theorem and retained physical scope

Use the original nine contained interior-disjoint unit squares and
the common selected physical certificate, with
\[
 79/40\le R\le\sqrt{1105}/16,\qquad
 d=\sqrt{R^2-1/4}-1,\quad
 \epsilon=\max(d-1,0)<1/60,\quad r=R-\sqrt2.
\tag{1}
\]
Let B have exactly three actual positive pair neighbors:

* a genuine radial S leaf L;
* an actual unit A meeting the closed disk of radius epsilon;
* a physically circle-touching unit K.

Assume that both physical intersections B-A and B-K are singleton
points. There is no physical A-K contact premise. The actual
positive degrees and all forces at A,K are unrestricted. The total
circle weight at K may be zero.

**Theorem 1.1.** One common physical certificate can be selected
before multiplier extraction so that neither of these two singleton
nonleaf contacts has a free vertex/vertex normal. Each has a genuine
side owner. This holds simultaneously for every eventual tuple
satisfying the hypotheses, together with all earlier finite generic
conditions.

A positive-length physical intersection does not satisfy the singleton
hypothesis, even if its eventual aggregate mean is an endpoint.
Every such variable shared-side chart remains outside this reduction.

The only structural inputs are the full genuine S-leaf chart in
RADIAL_BRIDGE_AND_LEAF_REDUCTION.md, the existing strict common
point-normal and matched-junction conventions in
PHYSICAL_BODY_GRAPH_UNCROSSING.md, Section 2, and the finite
determinant-selection framework in
GENERAL_FIXED_TIP_NORMAL_SELECTION.md. No loaded-body concurrence,
contact-radius gap, or physical triangle theorem is required.

## 2. A vertex at a singleton contact cannot use its own side axis

We first record the exact selected-normal fact used below.

**Lemma 2.1.** Suppose two distinct actual units X,Y have physical
intersection exactly the point Q, and Q is a vertex of X. The
actual selected separating normal from X toward Y is not parallel
to either side axis of X.

Indeed, a common normal parallel to a side axis of X makes a whole
adjacent edge of X a support edge through Q.

If Q is in the relative interior of a side of Y, that side must be
parallel to the support edge of X. It extends in both tangential
directions from Q, whereas the adjacent X edge extends in one
of them. Their physical intersection therefore contains a segment
of positive length, contrary to the singleton assumption.

Otherwise Q is also a vertex of Y. A physical point-only
vertex/vertex contact uses the prescribed strict common normal
chosen before extraction. That normal strictly exposes Q in X,
as well as in Y. A side-axis normal of X exposes an entire X
edge and is not strict. It therefore does not belong to the
allowed common-normal interval.

A point of Y's open interior is incompatible with physical
nonoverlap, so these cases are exhaustive. The lemma includes
a zero-origin junction: strict exposure still holds there even
though the separate nonradial condition is unavailable.

This lemma is about singleton physical intersections in the
selected certificate. It makes no assertion about endpoint means
of a positive-length shared side.

## 3. The genuine root equations and coincident applications

Write e for the actual leaf direction. The true leaf supplies
\[
 p_L=de,\qquad h_B(e)=d,\qquad
                 L=[d,d+1]e+[-1/2,1/2]Je.
\tag{2}
\]
The root B is physically circle-clear. Let
\[
                    p=B\cap A,\qquad q=B\cap K,
\]
and let n,m be the actual selected unit normals from B toward A,K.
Its unchanged true degree-three equations are
\[
 \gamma e+\mu n+\nu m=0,\qquad
 \mu\det(p,n)+\nu\det(q,m)=0,\qquad
 \gamma,\mu,\nu>0.
\tag{3}
\]
Taking a determinant of the force equation with e and eliminating
the two pair magnitudes gives the necessary identity
\[
       D(n,m)=\det(e,n)\det(q,m)
                    -\det(e,m)\det(p,n)=0.
\tag{4}
\]
No force equation at A or K is used.

If p=q, torque about that point makes p collinear with e.
The positive sum of the two supporting normals is -gamma e,
so p is the actual minimum-e support of B. Its full width w
gives
\[
 p=(d-w)e,\qquad1\le w\le\sqrt2,\qquad
              |p|\le\max(\sqrt2-d,d-1)<r.
\tag{5}
\]
For the strict inequality use
\(d>9/10\), \(\sqrt2<57/40\), \(r>11/20\), and
\(d-1<1/60\). Every point of the actual physical boundary
unit K has norm at least r, by its circle corner and diameter
sqrt(2). This contradicts p in K.

Thus an eventual positive star in the theorem always has p distinct
from q. Geometric tuples with p=q can remain unconditioned in
the pre-extraction list; their actual star is excluded by (5).
No independence of parameters at a common junction is assumed.

## 4. Complete collinear-vertex geometry

### 4.1. The actual leaf application is not a singleton nonleaf contact

At de, the physical radial S leaf occupies a local half-plane.
If both B and another unit contained that point, their disjoint
tangent sectors, each of angle at least pi/2, would have to be
the two exact quadrants filling the complementary half-plane.
After a rigid change of coordinates, they would be
\[
 [d-1,d]\times[0,1],\qquad
 [d-1,d]\times[-1,0].
\tag{6}
\]
These units share the whole horizontal unit segment ending at de,
contrary to the singleton premise. If either additional tangent
sector were a half-plane, there would be no room for the other
unit's positive-area sector. Thus de cannot be p or q.

### 4.2. The tilted collinear vertex contradicts the near-origin unit

If B is tilted relative to e, its true leaf application is its
unique maximum-e vertex. Its full chart is
\[
 B=de+[0,1]u+[0,1]v,\qquad
 e=-a u-b v,\quad a,b>0,\quad a^2+b^2=1.
\tag{7}
\]
Neither adjacent nonleaf vertex is collinear with e. The opposite
vertex is collinear only if a=b=1/sqrt(2).

In that exceptional frame, the two own coordinates of the origin
are d/sqrt(2), both strictly between 1/4 and 3/4. The lower
bound follows from \((9/10)(2/3)>1/4\), and the upper from
\((61/60)(17/24)=1037/1440<3/4\).
Therefore the whole closed disk of radius 1/4 about the origin
lies in int(B). The actual point of A in the epsilon disk would
lie in int(B), forcing interior overlap. This excludes that
physical geometry with no degree or force hypothesis at A.

### 4.3. The only remaining collinear vertex is near the origin

The aligned chart is
\[
 B=[d-1,d]\times[t-1/2,t+1/2],\qquad |t|\le1/2,
                         \quad e=e_x.
\]
A nonleaf vertex lies on the e axis only at a transverse endpoint.
After reflection it has the exact form
\[
 B=[d-1,d]\times[0,1],\qquad P=(d-1,0).
\tag{8}
\]
The other radial vertex de was excluded in Section 4.1. Also
\[
                              |P|=|d-1|<1/10<r.
\tag{9}
\]
Hence this collinear nonleaf vertex cannot belong to the physical
boundary unit K. A free contact at P can only be the edge to A.

## 5. The collinear determinant degeneracy is absent

Use (8), and consider another actual singleton contact Q on B
with its selected outward normal m. Suppose
\[
                              Q-P\parallel m.
\tag{10}
\]
The points are distinct in an eventual star by Section 3.

At a side-interior point Q, the side normal is perpendicular to
the side. The line in that direction from P reaches it only at
an endpoint: the top-side case would need its left endpoint,
the right-side case its bottom endpoint, and the other two sides
give only P itself. Thus only the other three vertices remain.

The vertex Q=de has already been excluded by the singleton premise.

At Q=(d,1), the outward normal cone and (10) force
\(m=(1,1)/\sqrt2\). The support height is \((d+1)/\sqrt2\).
Any unit on its far side has projection width at least one and
therefore maximal m-projection at least
\[
             (d+1)/\sqrt2+1>34/15>21/10>R.
\tag{11}
\]
This contradicts containment. The strict comparison uses
\(d>9/10\) and \(1/\sqrt2>2/3\).

At Q=(d-1,1), (10) forces m=e_y, a side axis of B.
But Q is a vertex of B and the physical B-K intersection is a
singleton. Lemma 2.1 excludes exactly this selected normal,
whether the other unit has a vertex or a side at Q.

Thus (10) is impossible for every actual allowed singleton normal.
The conclusion is uniform at d=1 and needs neither a degree-two
neighbor nor a physical triangle. No contact-radius theorem or
eventual circle multiplier is used.

## 6. Every free-normal determinant is genuinely avoidable

Suppose p distinct from q and the edge at p is free. If the other
normal m is fixed and not parallel to e, write
\[
 D(n,m)=\det(W,n),\qquad
                  W=\det(q,m)e-\det(e,m)p.
\tag{12}
\]
If W=0, then p is collinear with e. Section 4 leaves only
p=P from (8). Substitution into W=0 then gives
det(q-p,m)=0, precisely the impossible degeneracy (10).
Hence W is nonzero.

Its determinant has at most two zeros among unit normals. Remove
those roots from the actual nonempty open interval of strict
common normals. This makes the necessary identity (4) fail.

If m is instead parallel to e, the genuine force equation (3),
with mu>0, requires n parallel to e. Its at most two directions
can be removed directly. There is no division by a vanishing
determinant.

The same reasoning applies with the contacts exchanged. A free
contact at q cannot even have the near-origin collinear exception,
because q belongs to the physical boundary unit K and (9) excludes
that point.

If both contacts are free, p and q are distinct physical junctions.
Their strict-normal parameters are independent under the existing
matched-junction convention. Choose m nonparallel to e. Equations
(12) and Section 5 make W nonzero for every such allowed m, so
one can then choose n with D nonzero. The same finite avoidance
works inside every open subrectangle of the two parameter intervals.
Thus the nonzero set of D is open and dense in their product.

Lemma 2.1 already holds on the full earlier strict-normal domain;
it is not a new condition imposed on extracted stresses. At a
four-square junction the matching of the two opposite-pair
parameters is preserved. A single free edge still ranges over an
open interval, and distinct physical junctions remain independent.

## 7. Simultaneous preselection and preservation

Before applying the physical multiplier theorem, prelist every
ordered physical tuple (L,B,A,K) with the radial S pose (2), the
near-origin point at A, physical boundary contact at K, and the
two singleton B contacts. This is finite among the nine fixed
actual units. It includes every possible final genuine leaf and
true degree-three root; positivity and those eventual degrees
need not be assumed at the prelist stage.

Coincident-point tuples receive no new condition and have the
eventual-star exclusion (5). For every other free-contact tuple,
Section 6 supplies a nonzero linear factor, a finite forbidden
parallel direction, or a genuinely nontrivial two-variable factor.
Intersect their finitely many open dense complements with all
earlier allowed generic conditions.

All factors use fixed physical points and the actual radial leaf
direction. None depends on extracted magnitudes, eventual side
means or a degree at A,K.

The existing uncrossing preserves surviving point normals and
creates only shared-side forces. It cannot create an unlisted
physical singleton contact or turn a shared segment into one.
Conic thinning deletes atoms and edges, and every possible final
tuple was already prelisted. Any eventual star with a surviving
free contact would contradict (4) or the force-equation parallel
alternative. Coincident applications are impossible by (5).

This proves Theorem 1.1 in one common compatible certificate,
with no normal change after extraction.

## 8. Exact reusable consequences and limits

For the original adjacent-root C4
A-B-C-D-A with genuine S leaves at A,B and positive loads at C,D,
the near-origin premise holds at each opposite root. Therefore:

* at B, if its actual intersections with A,C are both singleton,
  both edges have genuine side owners;
* at A, if its actual intersections with B,D are both singleton,
  both edges have genuine side owners.

These conclusions hold simultaneously in the whole original
M6.B4L2.C4.ADJACENT.LCD.SS domain. If both roots meet the
singleton/singleton premise, all three edges AB,BC,AD have
side owners. The positive CD edge, both true degree-three root
equations and all three completion squares remain.

At the S tip root B of the hub/tip diamond, the genuine leaf root
H is its near-origin neighbor and the loaded hub K is physically
boundary. The same singleton conclusion applies with the actual
degrees H4,B3,K3,C2 unchanged. Its physical H-K triangle need
not be imported.

More generally, K may have any positive degree and even zero total
circle weight. Every additional force at A,K is retained. These are
whole-feature consequences, not claims that any original entire
gate is closed.

All positive-length shared contacts, every remaining owner/owner
chart, every actual mask, zero individual corner weight and arbitrary
completion unit remain to be treated under the original labels.
No new gate ID, coefficient certificate, numerical pose search,
scalar packet, force deletion, Lean or CI is used.
