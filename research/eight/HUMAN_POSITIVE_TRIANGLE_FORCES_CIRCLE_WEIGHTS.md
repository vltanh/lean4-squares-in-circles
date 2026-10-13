# Positive contact triangles cannot have force-free degree-two vertices

**Structural research, 2026-10-13.** This hand theorem strengthens
the smallest central-branching stress core. It uses actual supporting
contacts and physical force balance; no cap-offset or numerical
optimization is involved.

## General three-square lemma

Let P,Q,S be distinct interior-disjoint genuine unit squares.
Suppose P--Q, Q--S and P--S are **actual square contacts**, and a
normalized physical stress gives **positive contact forces** on
both P--Q and Q--S. Suppose these are Q's **only two positively
weighted square-pair contacts** (additional actual zero-weight
contacts are permitted).

Then Q has **strictly positive total disk-circle multiplier**
\[
\boxed{m_Q=\sum_{\alpha}\mu_{Q,\alpha}>0.}      \tag{1}
\]
This holds for arbitrary independent frames, irrespective of
whether any of the three squares contains the origin.

### Proof

Suppose \(m_Q=0\). The physical force equation at Q, with
only two positive incident edges, says their strictly positive
force vectors cancel. Orient the first contact normal from P
toward Q and the second from Q toward S. Their magnitudes
are equal and their unit normals **coincide**, say n.

These are true square-support contact equalities:
\[
n\cdot(p_Q-p_P)=H_P(n)+H_Q(n),\qquad
n\cdot(p_S-p_Q)=H_Q(n)+H_S(n).
\]
Adding gives
\[
n\cdot(p_S-p_P)-H_P(n)-H_S(n)
=2H_Q(n)\ge1,
\]
because a genuine unit square has half-width
\(H_Q(n)=(|n\cdot e_Q|+|n\cdot f_Q|)/2\ge1/2\)
in every unit direction.

Thus P and S are **strictly separated closed squares**,
with projected gap at least one. This contradicts their
assumed *actual* square contact P--S.
Hence \(m_Q>0\), proving (1). QED.

## Consequence for the smallest seven-outer branching core

Under the precise hypotheses of
[HUMAN_B3_THREE_OUTER_TRIANGLE_LEAF_NORMAL_FORM.md](HUMAN_B3_THREE_OUTER_TRIANGLE_LEAF_NORMAL_FORM.md),
the unique nontrivial positive contact component is exactly
\[
C-X-Y-C\quad\text{plus a positive bridge }C-Z,
\]
where C contains the origin and X,Y,Z are three distinct
outer-center squares.

X has precisely two **positive** contact pairs,
C--X and X--Y. Its two neighbor squares C,Y also
actually contact, so the triangle lemma gives \(m_X>0\).
Similarly Y has exactly two positive contacts
C--Y and X--Y, while C and X also actually contact,
so \(m_Y>0\). The positive leaf Z has only one
positive contact C--Z and hence a nonzero resultant
contact force, which implies \(m_Z>0\) by the
physical circle-force stationarity equation.

Therefore the full physical circle-multiplier support
in this minimal B3 root is **exactly**
\[
\boxed{m_X>0,\qquad m_Y>0,\qquad m_Z>0,}        \tag{2}
\]
with every other square (including C and the four
exterior spectators) carrying zero positive circle
multiplier in the chosen stress.

In particular, **all three** positively stressed
outer squares have actual containing-circle vertices;
one cannot choose a stress supported only on Z and X,
or only on Z and Y.

The X--Y edge joins consecutive outer center rays.
The radial leaf Z lies in one of the three
non-neighboring ray positions established in the
earlier B3 normal form. Its frame/active circle
vertices are further constrained by
[HUMAN_RADIAL_STRESS_LEAF_TWO_MODES.md](HUMAN_RADIAL_STRESS_LEAF_TWO_MODES.md):
side mode (two equal-weight circle vertices) or
diagonal mode (one positive circle vertex).

These are **necessary global force/contact support
conditions**, not an exclusion of the entire B3
root or a proof of \(R_8\ge\widehat R\).
The legitimate seven-outer full-contact ring remains
a separate equality-bearing root.
