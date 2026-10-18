# A reusable five-square perpendicular-cap obstruction with an R-only outer square

Research continuation, 2026-10-12. The former *S3/k=3-specific*
closure in [HUMAN_S3_K3_FULL_EXCLUSION.md](HUMAN_S3_K3_FULL_EXCLUSION.md)
has an important **strictly local five-square core**. This note
states it independently and draws a new exact consequence for
**exclusive S1/k=3**, without using any far singleton or
outer-count assertion inside the five-square proof.

## Theorem (five actual labels, arbitrary orientations)

Let five **distinct** unit squares with pairwise disjoint
open interiors lie in a disk centered at zero with
\[
R^2\le q_+:=9789/2500.
\]
Let \(h_R,h_U\) be positive offsets satisfying
\[
h_R>17/200,\qquad h_U>17/200.
\]
Assume the following **actual whole-square** cap memberships
and center radial classes:

* Three distinct squares \(A_-,A_+,A_o\) are wholly
  contained in \(\{x\ge h_R\}\). The first two have
  **inner** centers (norm \(<1\)), and the last has
  an **outer** center (norm \(\ge1\)).
* Two further distinct squares \(B_+,B_-\) are wholly
  contained in \(\{y\ge h_U\}\), and both have
  **inner** centers (norm \(<1\)).
* Critically, the outer R-cap member \(A_o\) does
  **not** have a whole upper-cap membership:
  \[
  A_o\not\subseteq\{y\ge h_U\}.                  \tag{R-only}
  \]

Then **this five-square configuration is impossible**.

All five frames are independent. Nothing is assumed about
the central square, a physical contact graph, the presence
of any *other* packed squares, or a minimizer stress.

## Proof, exposing all dependencies

The center norm ceiling
\[
|p|<r_0:=283/200
\]
holds for every square: the true farthest-vertex formula
implies \(r^2+r+1/2\le q_+\), and the left side exceeds
\(q_+\) at \(283/200\) by \(65/40000>0\).
Distinct packed unit squares have center distance \(\ge1\)
because their open inscribed radius-\(1/2\) disks are
disjoint.

### Case 1: h_U >=1/5

The general **five-square** theorem of
[HUMAN_FIVE_SQUARE_FAN_REFINED.md](HUMAN_FIVE_SQUARE_FAN_REFINED.md)
has *exactly* the five distinct label, inner/outer,
and whole-cap hypotheses above (without even requiring
R-only), provided \(h_R>17/200,\ h_U\ge1/5\).
It proves a contradiction by four-inner ray ordering
and two mixed inner/outer angular gaps.
Hence this case is impossible.

### Case 2: 17/200<h_U<1/5

There are **four distinct inner-center rays**
from \(A_-,A_+,B_+,B_-\). The pairwise
distance-\(\ge1\) inner-ray theorem forces their
signed angular order
\[
-\pi/3<\theta_{A_-}<0<\theta_{A_+}
<\theta_{B_+}<\pi/2<\theta_{B_-}<5\pi/6,
\]
with **each consecutive gap \(>\pi/3\)**.
Both R inner centers have x coordinate
\(>h_R+1/2>117/200\), and both U inner
centers have y coordinate \(>h_U+1/2>117/200\).

Set \(\alpha=\arcsin(h_U+1/2)\).
The exact sine comparison at \(31/50\) in
[HUMAN_S3_K3_SHARPER_OUTER_RAYS.md](HUMAN_S3_K3_SHARPER_OUTER_RAYS.md)
gives \(\alpha>31/50\). The four-inner
angular order then gives
\[
\theta_{A_-}<-\alpha,\quad
0<\theta_{A_+}<\pi/3-\alpha,\quad
\pi/3<\theta_{B_+}<2\pi/3-\alpha.
\]

The same note proves the following **universal pairwise**
center-distance angular restrictions under q_+,
using only strict radial bounds and exact cosine
Taylor inequalities:

* An inner radius \(>7/10\) and an outer center
  must have angular gap \(>2\pi/9\).
* An inner radius \(>117/200\) and an outer center
  must have angular gap \(>311/500\).

The negative R-inner center satisfies
\[
|p_{A_-}|>(117/200)/\cos\alpha>7/10,
\]
and both \(A_+,B_+\) have inner center radius
\(>117/200\), so the indicated gaps apply.

Let \(\psi\) denote the outer R center ray.
Its normal projection \(x>117/200\) and
radius \(<283/200\) imply
\[
-3\pi/8<\psi<3\pi/8.
\]
The mixed radial gaps prevent \(\psi\) from
lying below \(A_-\) or above \(B_+\).
They force the exact **two-sector** alternative
derived in the preceding ray note:
\[
-\pi/9<\psi<-2041/10500
\quad\text{or}\quad
311/500<\psi<8959/10500.                       \tag{1}
\]

The entire **negative** alternative is forbidden
by the *local* radial-amplification argument in
[HUMAN_S3_K3_NEGATIVE_RAY_EXCLUDED.md](HUMAN_S3_K3_NEGATIVE_RAY_EXCLUDED.md):
if \(\psi<-19/100\), its necessary angular gap
from \(A_-\) pushes \(\theta_{A_-}<-22/25\);
the mandatory R-center x projection then forces
the inner \(A_-\) radius \(>9/10\).
The resulting stronger mixed gap \(>77/100\)
pushes \(\theta_{A_-}<-24/25\), where
\(\cos|\theta_{A_-}|<117/200\), contradicting
the same whole R-cap center projection.
This uses **only** the five centers and q_+;
the negative-ray proof's S3 notation is not
an additional geometric premise.

Consequently
\[
\boxed{311/500<\psi<8959/10500.}               \tag{2}
\]

### Final contradiction: A_o and A_+ overlap in their inscribed disks

The two inner R centers \(A_-,A_+\) have
opposite signed y coordinates. Their x projections
are both \(>117/200\), and their norms \(<1\),
so their center distance \(\ge1\) forces the
strict transverse reserve
\[
\boxed{p_{A_+}.y>49/500.}
\]
The exact integer-square proof is in section 2 of
[HUMAN_S3_K3_FULL_EXCLUSION.md](HUMAN_S3_K3_FULL_EXCLUSION.md):
\(|\Delta x|<83/200\),
\(\Delta y>\sqrt{33111}/200\),
and \(p_{A_-}.y>-\sqrt{26311}/200\).

Thus \(A_+\)'s center coordinates satisfy
\[
117/200<p_x<1,\qquad 49/500<p_y<1.            \tag{3}
\]

The outer R center \(q\) has radius
\(1\le|q|<283/200\). Its positive ray (2)
lies strictly between \(\pi/6\) and \(\pi/3\),
so \(q_x,q_y>1/2\).
The exact cosine Taylor upper bound
\(\cos(311/500)<813/1000\) gives
\[
q_x<\frac{283}{200}\frac{813}{1000}
=\frac{230079}{200000}.
\]

**This is where R-only is essential.**
Because the entire square \(A_o\) is **not**
contained in \(y\ge h_U\), its lowest true
vertex ordinate lies below \(h_U\).
Every unit square's vertical half-width is
at most \(\sqrt2/2<177/250\). Hence its
center ordinate satisfies
\[
q_y<h_U+\sqrt2/2<1/5+177/250=227/250.       \tag{4}
\]
Combining the strict coordinate bounds for the
two **different** centers \(p=p_{A_+}\) and q,
\[
|q_x-p_x|<113079/200000,\qquad
|q_y-p_y|<81/100.
\]
The full squared distance therefore obeys
\[
|q-p|^2<
(113079/200000)^2+(81/100)^2
=1-\frac{969139759}{40000000000}<1.
\]
But their distinct unit squares require
\(|q-p|\ge1\). Contradiction. This closes case 2
and proves the five-square theorem. QED.

## New S1/k=3 continuous-region exclusion

Consider any **exclusive one-side**
S1=(3+0,3+1) eight-square packing at the
n=8 ceiling with exactly **k=3** outer
exterior centers.

Orient the 3+1 opposite pair along R,L, with
three R-side members and one far L singleton.
Let the perpendicular 3+0 triple side be U,
with no opposite D member. Write \(h_{31}=h_R\)
and \(h_{30}=h_U\).

The far L singleton is outer, and both
R and U triples have at least one outer
center each, by the proven cap-center theorem.
These are distinct labels. Since **k=3**,
each triple has **exactly one outer and
two inner** centers. All R/U members are
exclusive side statuses, so the five chosen
square labels (R's three and U's **two inner**)
are distinct, and R's outer square is **R-only**:
it cannot be wholly beyond U as well.

The far L cap envelope establishes the strict
3+1 triple-side bound
\[
h_{31}>17/200.
\]

If the perpendicular 3+0 triple offset
were **strictly greater** than \(17/200\),
the five-square theorem would apply to
R's three members and U's two inner members,
yielding a contradiction. Therefore
\[
\boxed{\text{exclusive S1/k=3 requires }
0<h_{30}\le17/200.}                           \tag{5}
\]

This excludes the **entire continuous region**
\(h_{30}>17/200\) from the still-open
exclusive S1/k=3 macro-cell.
It neither excludes S1/k3 entirely nor
assumes the 3+0 triple has an opposite singleton.

Combining with the previously proved
[HUMAN_PERPENDICULAR_TRIPLE_LOW_OFFSET.md](HUMAN_PERPENDICULAR_TRIPLE_LOW_OFFSET.md):
because \(h_{31}>17/200>1/16\),
if \(h_{31}\le1/10\) then the
3+0 triple must satisfy the stronger
\[
0<h_{30}<1/16.
\]
When \(h_{31}>1/10\), the new uniform bound
\(h_{30}\le17/200\) remains.
These are necessary geometric domains,
not existence assertions.

## Precise limitations

This five-square theorem requires **three R
whole-cap labels** with two inner/one outer,
two **distinct U-inner whole-cap labels**,
both signed offsets \(>17/200\), and the
**outer R label's failure to belong wholly
to U**. It must **not** be applied to
D1/D2 or saturated Type A if an RU square
is selected twice or the R-outer actually
has both side memberships.

The earlier S3/k=3 full exclusion becomes
one special application of this local theorem
(after separate S3 counting proves the five
hypotheses). The new S1/k3 implication is
another application. In either case it
leaves other continuous configurations,
including the real S4/k7 sharp candidate,
untouched.

This is a written exact analytic deduction
from the proved inner/outer angular and
farthest-vertex lemmas. The rational
margins are audited in prior scripts.
The unrestricted n=8 sharp lower bound
\(R_8\ge\widehat R\), global equality
classification and Lean formalization
remain OPEN.
