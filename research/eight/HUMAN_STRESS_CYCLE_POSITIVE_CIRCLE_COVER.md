# Physical-stress circle multipliers cover every edge of a two-force positive contact cycle

**2026-10-13. Full global force/support structural hand theorem.**
This upgrades the previous **actual circle-contact-or-C-chord**
vertex-cover bound to an **actual positive circle-multiplier
vertex-cover invariant**. It applies across *all* B2 actual
central-contact modes (P, S and K), independently of
zero-weight central chords or spectator placement.

No cap threshold, numerical circle-radius optimization,
SAT-owner enumeration, frame alignment or candidate
contact-pattern assumption is used.

## Theorem: no two adjacent force-free vertices on the positive stress cycle

Consider an attained **minimum-radius** packing of eight
pairwise interior-disjoint genuine unit squares inside a disk
of radius \(R<2\). Choose a normalized physical stress as in
[HUMAN_CONTACT_EQUILIBRIUM.md](HUMAN_CONTACT_EQUILIBRIUM.md).
Suppose its entire nontrivial positive contact component
is a **simple cycle**
\[
Q_0-Q_1-\cdots-Q_{k-1}-Q_0,\qquad k\ge4,
\]
and that every vertex of this positive-stress component
has exactly its two cycle neighbors as **positive-stress
contact pairs**. (Zero-positive-stress additional actual
contacts are explicitly allowed.)

For each cycle square let
\[
m_i:=\sum_{\alpha:\,|x_{i,\alpha}|=R}
          \mu_{i,\alpha}\ge0
\]
be the **total positive-stress circle-vertex multiplier**
of that square. Then
\[
\boxed{m_i+m_{i+1}>0
\quad\text{for every consecutive cycle edge}\quad
(Q_i,Q_{i+1}),}                                 \tag{1}
\]
with indices modulo k.

Equivalently the square labels having \(m_i>0\)
form a **vertex cover of the full positive stress cycle**.

### Proof: zero circle forces make a forbidden four-square chain

Direct each cycle pair \(Q_i,Q_{i+1}\) from
\(Q_i\) to \(Q_{i+1}\). Its positive
physical contact force has magnitude
\(\lambda_i>0\) and an actual **unit
separating side normal** \(n_i\) pointing
from \(Q_i\) toward \(Q_{i+1}\).
The physical forces on \(Q_i\) from its two
positive neighbors are, with the sign
convention in HUMAN_CONTACT_EQUILIBRIUM.md,
\[
F_i=\lambda_{i-1}n_{i-1}
     -\lambda_i n_i.                            \tag{2}
\]

Actual zero-weight contact pairs contribute
no force. The force/circle stationarity
identity is
\[
F_i=2\sum_{\alpha}\mu_{i,\alpha}x_{i,\alpha}.
\]
If \(m_i=0\), every nonnegative
\(\mu_{i,\alpha}\) is zero,
so \(F_i=0\).
Equation (2) then implies
\[
\lambda_{i-1}n_{i-1}=\lambda_i n_i.
\]
Both magnitudes are strictly positive and
the normals are **unit**, hence
\[
\boxed{\lambda_{i-1}=\lambda_i,\quad
       n_{i-1}=n_i.}                            \tag{3}
\]

Now assume two *consecutive* vertices
\(Q_i,Q_{i+1}\) both have zero
circle multiplier. Applying (3) at
both vertices gives **three consecutive
actual separating pair normals equal**:
\[
n_{i-1}=n_i=n_{i+1}=:n.
\]
The four squares
\[
Q_{i-1},Q_i,Q_{i+1},Q_{i+2}
\]
are pairwise **distinct**, since the
positive stress cycle length is
at least four.

For a unit-square frame \((e_j,f_j)\),
the centered support half-width
in the common unit normal n is
\[
H_j(n)=\tfrac12\big(|n\cdot e_j|
                      +|n\cdot f_j|\big)
\ge\tfrac12.                                   \tag{4}
\]
Each of the three **actual contact
separator equalities** has the form
\[
n\cdot(p_{j+1}-p_j)
=H_j(n)+H_{j+1}(n),                            \tag{5}
\]
for the four squares in the
displayed order.

Summing (5) and adding the two
end-support half-widths shows that
the union of the four true squares
has **total projected n-span at least**
\[
2\sum_{j=i-1}^{i+2}H_j(n)\ge4.                \tag{6}
\]
To see the identity explicitly:
the three center differences sum
to \(H_{i-1}+2H_i+2H_{i+1}+H_{i+2}\).
The first square's negative extreme
and fourth square's positive extreme
add \(H_{i-1}+H_{i+2}\), giving
\(2\sum H_j\).

But **every** square lies in the
containing disk \(D_R\), whose entire
projection onto n is \([-R,R]\),
of width \(2R<4\).
Inequality (6) is impossible.

Thus no two adjacent positive-cycle
labels can both have zero circle
multiplier, proving (1). QED.

## Consequence: central positive-degree-two B2 stressed cycles

For the established k=7, proper-outer-contact-forest,
positive C-degree-two root, the positive component
is precisely the central cycle
\[
C-S_1-\cdots-S_m-C,\qquad
3\le m\le6,
\]
by [HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md](HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md)
and the complete m=7 exclusion.

The central square **C has zero circle multipliers**,
because it contains the disk origin in its open
interior and has strict circle slack.
Apply theorem (1) to its two incident cycle edges:
\[
\boxed{m_{S_1}>0,\qquad m_{S_m}>0.}             \tag{7}
\]
This is strictly stronger than the previous
claim that S1/Sm have true disk-circle vertices,
and holds even if C has **additional zero-stress
actual contacts** (modes S and K).

Among the internal stressed labels S2..S_{m-1},
each consecutive internal cycle edge still
needs at least one positive circle multiplier
by (1). Hence the positive circle-multiplier
support on internal vertices is a vertex
cover of the (m−2)-vertex internal path.
Its minimum size is
\(\lfloor(m-2)/2\rfloor\).

Thus the required number of **distinct
stressed outer squares with genuinely
positive circle multipliers** is
\[
\boxed{2+\lfloor(m-2)/2\rfloor.}               \tag{8}
\]

| m outer cycle members | Positive circle-multiplier stressed outer labels, at least |
| --- | ---: |
| 3 | **2** |
| 4 | **3** |
| 5 | **3** |
| **6** | **4** |

These multipliers are the actual
nonnegative *physical stress*
multipliers, not merely true circle
contact indicators. In particular
the m=6/S spectator-spoke mode
forces **at least four positive
circle-multiplier stressed outer
squares**, **plus** the spectator T's
true disk-circle contact; the
spectator carries zero circle
multiplier because it lies outside
the nontrivial stress component.
Thus S has at least **five distinct
circle-contact exterior square labels**.

The m=6/K internal zero-stress-chord
mode is likewise required to have
**at least four positively circle-
stressed path squares**, irrespective
of how many extra actual C contacts
occur. Diagonal tangential bracing
does not replace these positive
circle multipliers.

## Important distinction from earlier vertex-cover theorem

[HUMAN_B2_INTERNAL_PATH_VERTEX_COVER.md](HUMAN_B2_INTERNAL_PATH_VERTEX_COVER.md)
used **minimum actual contact count**
and actual two-contact transmitter
rigidity. It forced each internal
consecutive pair to have an actual
**circle contact or C chord**.
The present theorem is **stronger
in its physical conclusion** and
requires neither actual-contact
minimality nor absence of zero-weight
C chords. It only needs a valid
normalized stress whose nontrivial
positive component is the simple
cycle in the theorem.

The proof is also simpler: two
adjacent force-free vertices would
produce **four successive full-square
support widths**, which cannot fit
into a disk of diameter <4. This is
a global chain obstruction for *actual
true squares*, not a numerical test.

A general nontrivial positive-stress
graph with degree-three vertices
need not be a simple cycle; do not
apply (1) to branching B3 or all of
root X without verifying the exact
two-positive-neighbor hypotheses.

The real equality-bearing complete
seven-outer actual-contact ring is a
separate root A and is unaffected.
The unrestricted sharp radius
\(R_8\ge\widehat R\), equality
classification and Lean 4
formalization remain OPEN.
