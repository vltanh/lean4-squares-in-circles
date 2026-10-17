# A mixed same-sign upper cap has a genuine whole-quadrant owner

2026-10-12 research continuation. This strengthens the **same-weak-sign**
portion of [HUMAN_MIXED_NEAR_CAP_POLARITY.md](HUMAN_MIXED_NEAR_CAP_POLARITY.md)
from *center polarization* to an **actual whole-square quadrant
separator**, with a strict rational clearance. The result holds for all
independent square frames. It is a genuine structural restriction on
the still-open S2/k4 cell C, not a complete exclusion of that cell.

## Theorem: forced strict whole-quadrant ownership

Suppose two distinct disjoint-interior unit squares P and Q
lie in a disk \(D_R\) with
\[
R^2\le9789/2500
\]
and **both entire squares** are in the positive-y cap
\[
y\ge h,\qquad h\ge7/24.
\]
Suppose their centers \(p,q\) obey
\[
|p|<1,\qquad |q|\ge1,\qquad p_xq_x\ge0.
\]
That is, P is the **inner-center** member, Q the
**outer-center** member, and their transverse center coordinates
have the same *weak* sign.

Then the outer **whole square**, not just its center, lies
strictly in one origin quadrant:

* If \(q_x>0\), every point \(z\in Q\) obeys
  \[
  \boxed{z_x>1/50,\qquad z_y\ge h\ge7/24>0.}
  \]
* If \(q_x<0\), every point \(z\in Q\) obeys
  \[
  \boxed{z_x<-1/50,\qquad z_y\ge h\ge7/24>0.}
  \]

The outer center cannot have \(q_x=0\) under the hypotheses.
In particular Q is **genuinely wholly in the open NE or NW
origin quadrant**, independently of its own frame.

## Proof from the true square half-width

The earlier arbitrary-frame mixed-cap lemma proves that
any inner/outer-center pair in a whole cap \(h\ge7/24\)
has **strict polar center-ray separation**
\[
|\arg(p)-\arg(q)|>3/4
\]
(their angles both belong to \((0,\pi)\)).
It also proves the following exhaustive weak-sign
classification:

* \(q_x=0\) is impossible.
* If \(p_xq_x\ge0\) and \(q_x\ne0\), the outer
  center ray is **farther from the positive y-axis**
  than the inner center ray in the same x half-plane.
* If \(p_x=0\), the inner ray is exactly \(+\pi/2\).
  The same polar-gap bound forces the outer
  center ray to deviate from \(+\pi/2\)
  by more than \(3/4\).

In either case, the absolute transverse coordinate of Q
obeys
\[
|q_x|=q_y\tan|\arg(q)-\pi/2|
>(h+1/2)\tan(3/4)
\ge(19/24)\tan(3/4).
\]

The elementary derivative/integration bound used in the
source note gives
\[
\tan(3/4)>
\frac34+\frac{(3/4)^3}{3}
+\frac{2(3/4)^5}{15}
=\frac{2361}{2560}.
\]
Consequently
\[
\boxed{|q_x|>\frac{19}{24}\cdot\frac{2361}{2560}
=\frac{14953}{20480}.}                          \tag{1}
\]

For **every actual unit-square frame** the maximal
horizontal supporting half-width is
\[
\frac{|\cos\theta|+|\sin\theta|}{2}
\le\frac{\sqrt2}{2}<\frac{71}{100},
\]
where \((71/100)^2>1/2\) is exact. Thus the
**minimum signed transverse coordinate of the
entire square Q** is bounded by
\[
\operatorname{sgn}(q_x)\,z_x
\ge |q_x|-\frac{\sqrt2}{2}
>\frac{14953}{20480}-\frac{71}{100}
=\frac{2061}{102400}
>\frac1{50}.
\]
The last positive rational margin is
\[
\frac{2061}{102400}-\frac1{50}
=\frac{13}{102400}>0.
\]

The whole-cap assumption already gives
\(z_y\ge h>0\) for every \(z\in Q\).
Hence Q is truly in the indicated **open
origin quadrant**, with the asserted
positive x-distance from its vertical boundary.
This proves the theorem. QED.

## Consequences for the exact S2/k4 three-cell queue

In the still-open exclusive S2/k4
[three-cell queue](HUMAN_S2_K4_THREE_CELL_QUEUE.md),
**cell C** has
\[
7/24<h_U<2/5,\quad
p_xq_x\ge0,
\]
where p is its single near-U inner center
and q its single near-U outer center.

Thus in cell C the **outer U square is a genuine
whole-quadrant occupant**: either the entire
unit lies in NE or the entire unit lies in NW,
with signed transverse clearance \(>1/50\).
The earlier frame-defect bound \(>1/2600\)
for at least one of P/Q remains necessary,
but the present conclusion needs **no**
frame-alignment hypothesis.

By the established whole-quadrant capacity
theorem
[HUMAN_ORIGIN_SECTOR_REPLICATION.md](HUMAN_ORIGIN_SECTOR_REPLICATION.md),
**no different exterior square may be wholly
contained in the same origin quadrant** at
\(R^2\le9789/2500<98/25\).
In particular, a distinct R-cap square
cannot also lie wholly in that same NE or NW
quadrant. This conclusion counts genuine
**whole-square** origin quadrants, not mere
center signs or half-cap membership.

The same local quadrant theorem applies to a
mixed inner/outer whole-cap pair in any of the
four signed cardinal directions, by rotation
and reflection.

### Logical limitation

The exact local pair in
[RATIONAL_SAME_SIGN_ROTATED_CAP_PAIR.md](RATIONAL_SAME_SIGN_ROTATED_CAP_PAIR.md)
has **two outer centers**, not one inner and one
outer, so is outside this theorem's assumptions.
It does not refute the claimed forced quadrant
ownership. Conversely, the theorem does **not**
make the entire S2/k4 cell C impossible:
a whole-quadrant outer U square can coexist with
other squares whose whole-quadrant memberships
have *not* been forced. The other S2/k4 cells
A,B, all remaining S1/S3/S4 statuses, D1/D2,
the unrestricted lower bound \(R_8\ge\widehat R\),
and Lean formalization remain OPEN.

[verify_mixed_cap_quadrant_owner.py](verify_mixed_cap_quadrant_owner.py)
audits the rational endpoint margins, not the
full continuous geometry or a Lean theorem.
