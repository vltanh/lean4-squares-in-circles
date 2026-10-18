# A whole global stress-cycle subcase excluded: seven-outer C-rooted m=7 path

**Research continuation, 2026-10-12. Status: complete hand
exclusion of an entire k=7 contact/stress support branch.**
This is **not** the unrestricted eight-square sharp-radius
proof. The real equality-bearing *full seven-outer actual
contact cycle* is **explicitly preserved**.

## Theorem

Consider an attained minimum-radius packing of eight
interior-disjoint genuine unit squares, with
\[
R_8^2\le q_+:=9789/2500.
\]
Suppose:

1. All seven noncentral square centers are **outer**
   (norm at least one).
2. The outer-induced **actual contact graph**
   is a **proper** subgraph of the seven
   circular-neighbor cycle (so consists only
   of paths and isolated vertices).
3. A normalized physical stress has **exactly
   two positive contact neighbors at C**.
4. Its unique nontrivial positive-stress
   component contains **all seven exterior
   squares**.

Then **no such minimum-radius packing exists**.
Equivalently, in the seven-outer **actual-path**
branch with central positive-stress degree two,
the stressed C-rooted cycle may contain
**at most six outer squares**:
\[
\boxed{3\le m\le6.}                              \tag{1}
\]

This removes **all seven cyclic placements** of the
formerly open \(m=7\) positive-stress cycle
normal form. In this degree-two k=7 root,
the combinatorially possible support count
drops from 35 to **28 labeled supports**
(seven per m=3,4,5,6), before continuous
geometric restrictions.

## Proof: the two angular inequalities conflict

The exact global normal-form theorem
[HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md](HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md)
applies. Because the outer actual graph is
a forest and the central positive degree
is two, the entire nontrivial positive
stress component is a **single actual
C-rooted cycle**
\[
C-S_1-S_2-\cdots-S_7-C.
\]
All seven outer centers are met in
their **circular ray order**.
The six square pairs \(S_i,S_{i+1}\)
actually contact, while \(S_7,S_1\)
**cannot** contact: the two stressed
C-neighbor force normals are opposite,
with the two outer neighbors separated
by a strict supporting-line gap.

Let \(\gamma\) be the missing circular
center-ray gap from \(S_7\) to \(S_1\).
The outer-pair angular theorem in
[HUMAN_STABLE_OUTER_ANGLE.md](HUMAN_STABLE_OUTER_ANGLE.md)
proves that every one of the six
consecutive outer gaps is strictly
greater than
\(\delta_0=\pi/4-1/500\). Therefore
\[
\gamma
=2\pi-\sum_{i=1}^6\delta_i
<2\pi-6(\pi/4-1/500)
=\boxed{\pi/2+3/250}.                           \tag{2}
\]
In particular \(\gamma<\pi\), since
\(\pi/2+3/250<\pi\). The complementary
six-gap arc is longer than \(\pi\),
so **\(\gamma\) is exactly the smaller
center-ray angle** between the two
opposite-stress neighbors \(S_1,S_7\).

Now apply the **new uniform true-square
opposite-central-neighbor theorem**
[HUMAN_OPPOSITE_CENTRAL_NEIGHBOR_ANGLE.md](HUMAN_OPPOSITE_CENTRAL_NEIGHBOR_ANGLE.md).
Because the stressed contact normals
from C to \(S_1,S_7\) are opposite,
these two whole squares lie beyond
two opposite supporting lines of
the origin-containing C. That theorem
covers **every independent square
orientation and every central position**
and gives the strictly stronger
\[
\gamma>\boxed{\pi/2+1/13}.                     \tag{3}
\]
But \(1/13>3/250\), with exact
positive rational difference
\[
\frac1{13}-\frac3{250}=\frac{211}{3250}>0.
\]
Inequalities (2) and (3) contradict
one another. This rules out the full
m=7 stressed-path case. QED.

## Important logical distinctions

* The excluded branch has **seven outer
  centers, six actual successive outer
  contacts, and one missing outer contact**,
  plus **two opposite positive central
  stress contacts**. Its positive graph
  is C plus an outer path using all seven.
* The **real sharp equality construction**
  has a **full seven-outer actual contact
  cycle**. It belongs to the separate
  outer-cycle root A and does **not**
  satisfy hypothesis 2. It is therefore
  **not eliminated**.
* In the same seven-outer actual-path branch,
  central positive stress degree \(\ge3\)
  remains possible. We have not asserted
  two opposite normals there.
* C-rooted stressed paths of lengths
  m=3,4,5,6 remain. Zero-stress exterior
  spectators are real squares whose
  disk space cannot be discarded.
* For k<=6, the entire k=7 outer-ray
  ordering reduction is not available:
  noncentral inner squares must be retained.

This result is a **genuine structural macro-case
elimination**, not another cap-offset
parameter shrink. It strongly supports a
proof architecture based on the true
central contact forces and complete outer
angular order, rather than millions of
symbolic status words.

[verify_seven_outer_m7_gap.py](verify_seven_outer_m7_gap.py)
audits the final exact rational
incompatibility. The continuous
geometric content is fully proved
in the two cited hand notes, not
delegated to a numerical sampling program.

The global \(R_8\ge\widehat R\),
full equality classification and
Lean 4 proof remain OPEN.
