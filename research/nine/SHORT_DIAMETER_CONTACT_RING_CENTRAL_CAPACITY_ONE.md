# A physical contact ring of center diameter below three encloses at most one unit

Date: October 26, 2026.

**Status: accepted complete geometric transfer after fresh full-source and
physical-scope reviews in REVIEW_SHORT_DIAMETER_RING_AND_FIVE_JOIN_ROOT_2026_10_26.md
and REVIEW_SHORT_DIAMETER_RING_AND_FIVE_C6_2026_10_26.md.**
The two new steps are a winding-preserving
center-chain replacement and a missing-face-zone extraction for that
possibly nonconvex chain. The remaining continuous inner-pair inequalities
are the already audited geometric lemmas identified precisely below.
No number of ring bodies, boundary-circle contact, positive load, common
frame, or convex center polygon is assumed.

Put
\[
Q=\frac{1105}{256},\qquad M=\frac{91}{60},\qquad
k=\frac{3721}{7200},\qquad e=k-\frac12=\frac{121}{7200}.
\tag{1}
\]

## 1. Complete statement and enclosure convention

Let \(S_0,\ldots,S_{n-1}\) be distinct actual unit squares with pairwise
disjoint open interiors, all contained in the disk \(D_{\sqrt Q}\)
about the fixed origin. Consecutive squares have actual contact points
\[
p_i\in S_i\cap S_{i+1},
\]
with indices modulo \(n\). Write \(c_i\) for their actual centers and
\[
\Gamma=c_0p_0c_1p_1\cdots c_{n-1}p_{n-1}c_0.
\tag{2}
\]
Assume
\[
|c_i-c_j|<3\qquad(i\ne j).
\tag{3}
\]

An **enclosed extra** here means an actual unit square \(T\), disjoint
in open interior from every \(S_i\), such that the winding number of
(2) about every point of \(\operatorname{int}T\) is nonzero. The usual
positively oriented Jordan contact ring gives winding one. The theorem
also permits weak junctions: it is enough that an arbitrarily small
physical Jordan routing converges to (2), and every compact subset of
each proposed extra interior remains on its bounded side. Since the
limit curve lies in the closed ring squares, it stays a positive distance
from such a compact subset; the winding is therefore stable and equals
one there. This is the weak enclosure convention used in
SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md, Section 3.

**Theorem.** Under these hypotheses, at most one pairwise
interior-disjoint enclosed extra exists.

The theorem counts the whole central free union, even if further actual
contacts subdivide it. It does not require those free components to be
connected to each other. The same original ring and the same winding
hypothesis apply to every proposed extra.

A basic metric consequence used throughout is
\[
|c_i|<M,\qquad |c_i-c_j|\ge1\quad(i\ne j).
\tag{4}
\]
For the first inequality, an actual unit with center radius \(\rho\)
has a corner giving
\[
\rho^2+\rho+\frac12\le Q,
\]
whereas
\[
M^2+M+\frac12-Q=\frac{31}{57600}>0.
\]
For the second, each square contains the open disk of radius one half
about its center.

Every point of an extra interior avoids every closed ring square.
Indeed an open neighborhood of a point in a closed unit square meets
its open interior. This observation also makes every winding number
above well defined.

## 2. The actual center chain retains the enclosure

For every enclosed \(T\),
\[
\operatorname{dist}(c_i,T)\ge\frac12.
\tag{5}
\]
Otherwise the open incircle of \(S_i\) would meet the interior of \(T\).
Also every actual contact gives
\[
|c_{i+1}-c_i|
\le |c_i-p_i|+|p_i-c_{i+1}|
\le\sqrt2.
\tag{6}
\]

The elementary clear-endpoint chord lemma in
C7_CENTER_POLYGON_LOCALIZATION.md, Section 2, has no C7 or convex-polygon
premise: a segment of length at most \(\sqrt2\), whose endpoints have
distance at least one half from a unit square, avoids that square's
open interior. Its proof concerns only the chords of the square's
radius-one-half parallel body. Thus (5)--(6) show that every edge of
the closed center chain
\[
\Gamma_c=c_0c_1\cdots c_{n-1}c_0
\tag{7}
\]
avoids \(\operatorname{int}T\).

Replace each two-spoke path \(c_i p_i c_{i+1}\) by its center edge.
The boundary of the replacement triangle avoids
\(\operatorname{int}T\): two sides lie in actual ring units, and the
third avoids it by the chord lemma. The connected set
\(\operatorname{int}T\) is consequently wholly inside or wholly outside
a nondegenerate replacement triangle. The inside alternative is
impossible, because
\[
\operatorname{area}\triangle(c_i,p_i,c_{i+1})
\le\frac12\,\frac1{\sqrt2}\,\frac1{\sqrt2}
=\frac14<1.
\tag{8}
\]
A degenerate triangle has winding zero directly. Thus every replacement
has zero winding about every point of \(\operatorname{int}T\).
The center chain (7) has the same nonzero winding as (2).

This argument proves exactly the topological fact needed below.
It does not assert that (7) is simple or convex, that its vertices are
in radial order, or that the edges of its convex hull satisfy (6).

It also proves the outgoing-ray property used in the local geometric
lemmas. Any ray beginning at a point of an enclosed extra interior and
continuing to infinity must meet the actual occupied ring: otherwise
the winding of (2) would stay nonzero along the whole ray, although
it is zero sufficiently far away. In particular, the first ring encounter
after leaving that extra belongs to a true \(S_i\), not to an auxiliary
hull edge.

## 3. A missing middle-face zone for a nonconvex center chain

This section replaces every use of convex polygon containment in the
parallel-pair and far-face-extraction proofs.

First translate and rotate just for this local statement so that
\[
T=[-1,0]\times[-1/2,1/2].
\]
Suppose no vertex of (7) lies in its left middle-face zone
\[
Z_L=\{(x,y):x\le-3/2,\ |y|\le1/2\}.
\tag{9}
\]
The center \((-1/2,0)\) of \(T\) has nonzero winding under (7), while
a sufficiently distant point on its leftward horizontal ray has winding
zero. Hence that ray meets a center edge at a point \((x,0)\) with
\(x\le-1\); no center edge can enter \(\operatorname{int}T\).

Such an intersection is not a center vertex. Its clearance (5) would
force \(x\le-3/2\), contrary to (9). A horizontal edge cannot overlap
this ray either: an endpoint on the ray would again belong to (9), and
an edge with both endpoints to its right cannot reach it. Therefore some
intersection is in an edge interior with one endpoint \(A\) above and
one endpoint \(B\) below the horizontal axis.

Both endpoints have first coordinate strictly below \(-1\).
At least one has first coordinate at most \(-1\); by reflecting the
second coordinate if necessary, call it \(B\). Its clearance and the
absence of (9) imply \(B_y<-1/2\). If \(-1\le A_x\le0\), clearance
would imply \(A_y\ge1\), so the edge's vertical span would exceed
\(3/2>\sqrt2\). If \(A_x\ge0\) and \(A_y\le1/2\), clearance would
give \(A_x\ge1/2\), with horizontal span at least \(3/2\). If
\(A_x\ge0\) and \(A_y>1/2\), the horizontal span is at least one
and the vertical span exceeds one. All contradict (6). Equality of
the remaining endpoint's first coordinate with \(-1\) likewise forces
its vertical coordinate to have magnitude at least one and is impossible.

We have proved the actual endpoint representation
\[
A=(-1-u,1/2+v),\qquad
B=(-1-w,-1/2-z),
\tag{10}
\]
where
\[
u,w,v,z>0,\quad u^2+v^2\ge\frac14,\quad
w^2+z^2\ge\frac14,\quad
v+z\le\sqrt2-1<\frac12.
\tag{11}
\]
Moreover \(u,w>1/4\), because
\(\sqrt2-1<\sqrt3/4\). The latter comparison follows, for example,
from \(\sqrt2>45/32\) by squaring.

No convexity was used. Reflection gives the right-face version, and
a rigid motion gives every own-face version. These local translations
are used only for clearance, edge length and winding; whenever a
center norm about the fixed disk origin is used below, the coordinates
are returned to that fixed origin.

## 4. Parallel extras are impossible

Take two parallel interior-disjoint extras. After a local rigid motion
and, if necessary, an interchange of coordinate axes, their positions
are
\[
T=[-1,0]\times[-1/2,1/2],\qquad
U=[g,g+1]\times[t-1/2,t+1/2],\quad g\ge0,
\tag{12}
\]
with arbitrary real stagger \(t\).

Use the left zone of \(T\) and the right zone of \(U\). The proof of
PARALLEL_INNER_PAIR_DIAMETER_EXTRACTION.md, Sections 2--4, uses only
actual vertices in these zones or the endpoints (10)--(11).
Its Section 1 convex-containment step has now been supplied by
Section 3 for the actual center chain. The complete remaining alternatives
are as follows.

* If both zones contain actual centers, their horizontal difference
  is at least \(g+3\ge3\).
* If exactly one zone is empty, (10)--(11) on that side and a center
  in the opposite zone force one of the two cross distances to exceed
  three. The exact estimate is
  \[
  9-(5/2+u)^2\le9(1/4-u^2)\le9v^2
  \]
  for \(1/4<u\le1/2\), and its lower-endpoint counterpart.
  If both cross distances were at most three, the vertical gap
  \(1+v+z\) would be at most \(3(v+z)\), contrary to \(v+z<1/2\).
* If both zones are empty, each of their two endpoint pairs obeys
  \(2u+v>9/10\). A cross diagonal selected according to the sign of
  \(t\) has squared length strictly greater than
  \[
  5+\frac{18}{5}+\frac12=\frac{91}{10}>9.
  \]

Every point so extracted is an actual ring center. Each alternative
contradicts (3). This proves the parallel case without any assertion
about a convex center polygon.

## 5. The whole nonparallel far-face extraction also transfers

The local ray and corner lemmas
C7_INNER_SIDE_CORNER_RESTRICTIONS.md and
C7_INNER_OUTSIDE_FACE_CORNER_EXCLUSION.md are already stated for
arbitrary finite physical rings. Their only global input is (4)
and the outgoing-ray property. They therefore give, for every enclosed
unit and pair:

* both own center-coordinate magnitudes are less than \(k\);
* every own vertex has norm greater than
  \(d_0=\sqrt{5/2}-M>19/300\);
* if one own center coordinate has magnitude at least \(1/2\), the
  other's magnitude is less than \(3/8\);
* the relative frame angle satisfies
  \[
  0\le\theta\le\pi/4,\qquad \sin\theta<4/15.
  \tag{13}
  \]

Now choose an actual square-owned SAT normal of a nonparallel pair,
directed from its left unit \(T\) to its right unit \(U\).
Rotate and reflect about the fixed disk origin so that
\[
C_T=(-\alpha,\beta),\qquad
C_U=\xi u+\eta v,\quad
u=(c,s),\quad v=(-s,c),\quad
c=\cos\theta,\quad s=\sin\theta>0.
\tag{14}
\]
All four own coordinates have magnitude less than \(k\).
The original owned separator gives
\[
\alpha+\xi c-\eta s\ge\frac{1+c+s}{2}.
\tag{15}
\]
In particular, exactly as in Section 2 of
C7_INNER_PAIR_FAR_FACE_CENTERS.md,
\[
\alpha>\frac12-2e>\frac9{20},\qquad
\xi>\frac12-e\frac{1+s}{c}>\frac9{20}.
\tag{16}
\]

For completeness, the only polygon premise of that source's
Section 1 is the missing-zone extraction now proved in Section 3.
Indeed, for an own coordinate \(a\ge9/20\), an empty outward zone
would give endpoints
\[
A=(a+1/2+u,b+1/2+v),\quad
B=(a+1/2+w,b-1/2-z)
\]
with (11). Setting \(X=a+1/2\ge19/20\), \(V=v+z\), their mean squared
norm is at least
\[
F_X(V)=X^2+
X\left(\frac12+\sqrt{\frac14-V^2}\right)
+\frac12+\frac V2-\frac{V^2}{4}.
\tag{17}
\]
This function increases in \(X\) and is concave in
\(0\le V\le\sqrt2-1\). Its endpoint estimates are
\[
F_{19/20}(0)=\frac{941}{400}>M^2,\qquad
F_{19/20}(\sqrt2-1)>\frac{11529}{5000}
=M^2+\frac{497}{90000}.
\tag{18}
\]
The exact comparisons used for the second endpoint are
\[
\sqrt2-1>33/80,\quad
(\sqrt2-1)^2<43/250,\quad
\sqrt{1/4-(\sqrt2-1)^2}>279/1000.
\]
They are the fixed elementary radical comparisons in the cited source.
Thus an empty zone contradicts (4).

Applied to the two outward faces in (14)--(16), this supplies two
distinct actual ring centers
\[
C_L=C_T-(1+\delta)e_x+t e_y,\qquad
C_R=C_U+(1+\varepsilon)u+r v,
\tag{19}
\]
with
\[
\delta,\varepsilon\ge0,\qquad |t|,|r|\le1/2.
\]
Write \(g\ge0\) for the excess in (15). Then the exact gap identity is
\[
(C_R-C_L)_x=
\frac32(1+c)+g+\delta+\varepsilon c+(1/2-r)s.
\tag{20}
\]
The actual-center diameter bound (3), not any polygon perimeter bound,
now gives
\[
r>\frac12-\frac32\tau,\qquad
\tau=\tan(\theta/2).
\tag{21}
\]
This is the complete geometric output required by both subsequent
nonparallel branch exclusions.

## 6. Exact scope of the continuous branch inequalities

The following table lists every imported local argument and the inputs
it actually uses. No row requires seven ring bodies, positive circle
loads, actual circle contact of a witness, or convexity of (7).

| Accepted source and part | Inputs used here | Output |
| --- | --- | --- |
| CENTER_COVER_PIERCING.md, Sections 1--4 | An actual unit, a disjoint actual ray witness, their full supports and SAT owners | The orientation-uniform radial-tail bound |
| C7_INNER_SIDE_CORNER_RESTRICTIONS.md | Ring-center norm \(<M\) and an actual outgoing witness | Own-coordinate bound \(<k\), vertex norm \(>d_0\), initial angle bound |
| C7_INNER_OUTSIDE_FACE_CORNER_EXCLUSION.md | The same ray enclosure and \(<M\), with the previous own-coordinate and vertex bounds | Outside-face restriction and (13) |
| C7_INNER_PAIR_FAR_FACE_CENTERS.md, Sections 1--3 | The missing-zone endpoints from Section 3 above, \(<M\), actual pair SAT, and (3) | (16)--(21) |
| C7_SHARP_BALANCED_RADIAL_TAIL.md | Two actual disjoint units and an outgoing-ray encounter, with \(9/20\le a\le k,\ 2a/3\le b\le a\) | Its continuous exact lower norm \(F_R(a,b)\) |
| C7_OUTSIDE_INNER_RAY_WITNESS.md, scalar estimate (3) | The scalar range \(0<b<11/20\) only | \(1/(16b^2)+(b+1)^2>58/25>M^2\) |
| C7_RIGHT_OUTSIDE_INNER_EXCLUSION.md, Sections 1--5 | (4), whole actual corner containment in \(D_{\sqrt Q}\), (13)--(21), actual ray witnesses and full SAT | Exclusion of \(\xi\ge1/2\) |
| C7_LEFT_OUTSIDE_INNER_EXCLUSION.md, Sections 1--4 | The same inputs, the balanced local tail lemma, and the remaining \(\xi<1/2,\alpha>1/2\) | Exclusion of that entire remaining case |

Here are the final branch joins explicitly.

First, \(|\beta|,|\eta|<1/2\): if either secondary magnitude were
at least \(1/2\), the outside-face restriction would force its main
magnitude below \(3/8\), contradicting (16). If
\(\alpha\le1/2\) and \(\xi\le1/2\), then \(\eta>-1/2\) and \(s>0\)
would make the left side of (15) strictly smaller than its right side.
The exhaustive cover, retaining the original separator owner, is
therefore
\[
\xi\ge1/2
\quad\hbox{or}\quad
\xi<1/2,\ \alpha>1/2.
\tag{22}
\]

In the first branch, C7_RIGHT_OUTSIDE_INNER_EXCLUSION.md first shows
\(\eta=-b\), \(3/16<b<3/8\). It localizes every actual ray witness to
the center cap \(x>36/25\), whose diameter is less than one under (4).
Thus that witness is the actual far-face unit \(C_R\), because two
distinct actual unit centers are at distance at least one.
Its full-frame support and (21) then give the incompatible bounds
\[
r<\frac35-\frac{b}{2k},\qquad
r>\frac12-\frac{3e}{2(1/2-b)}.
\tag{23}
\]
The difference, lower minus upper, is the concave function
\[
f(b)=\frac{b}{2k}-\frac1{10}-\frac{3e}{2(1/2-b)}
\]
with positive endpoint values
\[
f(3/16)=\frac{4109}{5581500},\qquad
f(3/8)=\frac{136499}{2232600}.
\tag{24}
\]
That source's witness-frame bounds use only
\(\rho^2+\rho(\cos\psi+\sin\psi)+1/2\le Q\);
equality at a circle corner is never needed.

In the second branch put \(a=\xi,\ d=1/2-a\). The complete left-branch
source proves
\[
0<d<e,\qquad \eta=-b,\qquad
9/50<b<5/12<a,
\]
and again identifies every actual outgoing witness with the actual
far-face unit. Its two final uniform bounds are
\[
r> \frac12-4(e-d),\qquad
r<W(d)<\frac{17}{40}+\frac{43}{10}d.
\tag{25}
\]
For clarity, the function here is
\[
W(d)=\frac{(11/10)a}{2a+1}
+\frac{\sqrt{M^2-(a+1)^2}}{a+1},
\qquad a=1/2-d.
\]
Its strict concavity and the displayed endpoint tangent are proved in
that source on the full interval \(0\le d\le e\). The upper minus lower
bound in (25) is at most
\[
-\frac3{40}+\frac{43}{10}e
=-\frac{197}{72000}<0.
\tag{26}
\]
The difficult upper-normal witness alternative in that proof is
excluded by an actual corner \(w\) satisfying \(|w|^2>Q\), which
contradicts the whole-square containment assumed in Section 1.
It does not assume a load or a circle equality for that corner.

All parallel and nonparallel possibilities are now excluded.
The theorem follows.

## 7. Physical use and exact limits

The proof supplies a reusable capacity-one theorem for a whole physical
contact ring once its actual center diameter is strictly below three.
It is not a claim that diameter below three alone gives a disk cover of
radius \(3/2\); that stronger covering assertion is unnecessary.

For an application with weak contacts, the required winding must be
established for every compact portion of every proposed central extra,
as stated in Section 1. The source then uses all the same actual squares.
It never replaces them by a convex hull, by aligned squares, or by
fictitious independently placed ray witnesses.

In particular, the present theorem can be combined with
CHANNEL_CAP_OCCUPANCY_TRANSMITTER_CENTER_BOUND.md only after its
actual cap-occupancy hypothesis and full fifteen-pair cover have been
proved. That physical join is separate from this geometric statement.

The transferred scalar proofs use whole continuous domains and fixed
elementary inequalities. This source adds no parameter grid, coefficient
packet, numerical enclosure, Lean compilation or CI.

