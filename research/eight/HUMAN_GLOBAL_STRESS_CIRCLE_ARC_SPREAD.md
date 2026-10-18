# Global physical-circle-force support must spread beyond a 135-degree center-ray arc

**2026-10-13. Exact all-frame force-balance theorem independent
of the contact graph.** This extracts the general principle
behind the completed seven-outer m3 stress-cycle exclusion.
It applies also to central branching and exterior stressed
components, whenever positive physical circle multipliers
are supported in a too-short angular center-ray arc.

## Universal stress-support angular-spread theorem

Let an eight-unit-square packing attain its least
containing disk radius R, with
\[
\sqrt2+1/2<R\le\sqrt{9789/2500}<2.
\]
Choose **any normalized physical stress** satisfying
the force and nonnegative circle multiplier equations
of HUMAN_CONTACT_EQUILIBRIUM.md:
\[
F_i=2\sum_\alpha\mu_{i,\alpha}x_{i,\alpha},\quad
\mu_{i,\alpha}\ge0,\quad
\sum_{i,\alpha}\mu_{i,\alpha}=1.
\]

Let I be the set of actual square labels with **positive
total circle-vertex multiplier**
\(m_i=\sum_\alpha\mu_{i,\alpha}>0\).
Every such square has a nonzero center p_i
(the unique zero-containing C is strictly circle-free).
Then the positive-circle-multiplier square
**center rays cannot all be contained in any
circular angular arc of width at most**
\[
\boxed{\,\pi-\frac{31}{40}\,}.                   \tag{1}
\]

Equivalently, every closed angular arc containing
all their center rays must have length **strictly
greater than** \(\pi-31/40\).
This is a **strict positive physical-force support
spreading condition**, not a cap-membership assertion
about entire squares.

### Proof

Every true unit-square vertex x is at
distance exactly \(\sqrt2/2\) from its
square center p. If it lies on the
containing circle, \(|x|=R\),
the smaller angle between center ray
and circle-vertex ray is bounded by
\(\arcsin((\sqrt2/2)/R)\).
The complete exact rational calculation in
[HUMAN_SEVEN_OUTER_M3_SEMICIRCLE_EXCLUDED.md](HUMAN_SEVEN_OUTER_M3_SEMICIRCLE_EXCLUDED.md)
proves the strict bound
\[
\angle(p,x)<31/80.                              \tag{2}
\]
The proof uses \(R>191/100\),
\(\sqrt2/2<99/140\), and
\[
\sin(31/80)>
1160609/3072000>495/1337.
\]
No center-frame alignment is assumed.

Suppose the center rays of every
\(i\in I\) lay in an arc of length
at most \(\pi-31/40\). By (2),
**all actual positively weighted
circle-vertex rays** lie in the
slightly larger arc of width
**strictly less than**
\[
(\pi-31/40)+2(31/80)=\pi.
\]
Hence those true circle vertices
lie in a common open half-plane
through the disk origin.

But summing the physical force
equations over all square labels
cancels every contact force,
and gives global force balance
\[
\sum_{i,\alpha}\mu_{i,\alpha}x_{i,\alpha}=0.
\]
A nonnegative linear combination
with total coefficient 1 of
vectors **strictly in the same
open half-plane** cannot vanish:
taking the dot product against
its inward pointing normal is
strictly positive. Contradiction.
This proves (1). QED.

## New consequence for central branching B3

Suppose **k=7 exterior outer centers** and an
attained minimizer has a normalized physical stress
whose **unique nontrivial positive-contact component**
contains C and at most **three** of the seven
exterior squares, and the participating exterior
labels form a **consecutive three-label block**
in the circular order of all seven outer centers.

Then **this stress component is impossible,
regardless of its positive graph degree,
C's actual degree, square frames or contacts.**

Indeed any square outside the positive
stress component has zero total positive
contact force and hence **zero circle
multiplier** by the stationarity lemma
\(F_i=0\iff m_i=0\) in
HUMAN_CONTACT_COMPONENTS.md.
The central C has zero circle
multiplier because it lies strictly
inside the circle. Therefore every
positive circle multiplier would
belong to those at most three
consecutive outer labels.

The outer pair angular theorem
HUMAN_STABLE_OUTER_ANGLE.md states that
each successive outer-center ray gap
exceeds
\(\delta_0=\pi/4-1/500\).
The five complementary gaps force
the participating three-center
angular arc to have width
\[
<3\pi/4+1/100.
\]
But
\[
3\pi/4+1/100
<\pi-31/40
\quad\Longleftrightarrow\quad
\pi/4>157/200,
\]
which holds because \(\pi>157/50\).
This contradicts the universal
stress-support arc theorem (1).

Thus **not only the B2 m3 simple
stressed cycle, but EVERY central-
stressed component confined to three
consecutive outer square labels is
impossible at k=7**.
In particular it eliminates the
B3 subcase with three positive
C-neighbor squares forming a
consecutive triple and no additional
positively stressed outer squares.

Other central B3 configurations
with separated outer labels or
larger positive support are
**not** eliminated. The central
five-corner equality construction
with its full seven-outer
actual-contact cycle is unaffected.

## Scope

This result is an exact **global force-
balance necessary inequality**, not
a complete stress-graph classification
or the sharp \(R_8\ge\widehat R\)
lower bound. Positive circle multipliers
are essential; the center rays of
three arbitrary *unstressed* squares
may be confined to a tiny arc with
no contradiction.

The theorem can help future structural
case proofs whenever physical circle
forces appear concentrated in a
short angular sector. Its proof
uses true vertex rays and the
exact same strict rational shadow
bounds as the completed m3
global macro-case exclusion.
