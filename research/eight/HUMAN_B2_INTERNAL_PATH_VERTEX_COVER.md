# A vertex-cover invariant for every centrally stressed outer path

**2026-10-12. Exact all-frame global contact-graph theorem.**
This is a genuinely structural obstruction: it couples
**true circle vertices** and **true zero-stress central
contact chords** along entire positively stressed
outer paths. It does not optimize any cap offset,
and does not assert an unproved global radius bound.

## Theorem: boundary/contact-chord vertex cover

Choose an eight-unit-square *least-radius* packing
under \(R^2\le9789/2500\), among such packings with
**the fewest actual square-square contacts**.

Suppose the seven noncentral square centers are
**outer** (norm >=1), their actual-induced
outer-contact graph is a **proper** subgraph
of their seven-ray neighbor cycle, and a
normalized physical stress has exactly two
positive C-contact neighbors. As proved in
[HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md](HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md)
and the complete
[HUMAN_SEVEN_OUTER_PATH_M7_EXCLUDED.md](HUMAN_SEVEN_OUTER_PATH_M7_EXCLUDED.md),
the unique nontrivial positive-stress graph is
\[
C-S_1-S_2-\cdots-S_m-C,\qquad 3\le m\le6,
\]
with \(S_i\) consecutive in cyclic order
of the seven outer center rays.

For each **internal stressed-path vertex**
\(S_i\), \(2\le i\le m-1\), define the
following *genuine actual geometry* predicate:
\[
\mathrm{Anchor}(i)\quad\Longleftrightarrow\quad
\begin{cases}
 S_i \text{ has at least one true vertex
 on the containing circle},\\
 \text{or}\\
 S_i\text{ makes an actual (possibly zero-stress)
 contact with C}.
\end{cases}
\]

Then for every pair of *consecutive internal*
stressed-path labels,
\[
\boxed{
\mathrm{Anchor}(i)\ \lor\
\mathrm{Anchor}(i+1),
\qquad 2\le i\le m-2.
}                                                       \tag{1}
\]
Equivalently, the anchors form a **vertex
cover** of the path of \(m-2\) internal
stressed outer squares.

Consequently
\[
\boxed{
\#\{\text{distinct anchored internal stressed squares}\}
\ge\left\lfloor\frac{m-2}{2}\right\rfloor.
}                                                       \tag{2}
\]

The precise lower bounds are:

| Stress path size m | Internal outer squares | Forced distinct internal anchors |
| --- | ---: | ---: |
| 3 | 1 | 0 (but see scaffold dichotomy below) |
| 4 | 2 | 1 |
| 5 | 3 | 1 |
| **6** | **4** | **2** |

All conclusions concern actual disk-circle
contacts and/or actual central-square
touching pairs, **not** chosen positive
stress multipliers alone.

## Proof of the universal internal-vertex cover

Fix an internal stressed-path square
\(S_i\) with \(2\le i\le m-1\).
Its two adjacent positive-stress outer
neighbors \(S_{i-1}\) and \(S_{i+1}\)
are **different actual contacting squares**.

The outer-center angular visibility
theorem
[HUMAN_OUTER_GRAPH_REDUCTION.md](HUMAN_OUTER_GRAPH_REDUCTION.md)
says that each outer-center square
can actually contact *only the two
circularly neighboring outer ray labels*.
Because the positive stressed path's
labels are consecutive in that same
ray order, these two path neighbors
exhaust all possible **outer** actual
contacts of S_i.

Since k=7, **every noncentral square is
outer**. Hence the **only possible
additional square-square actual contact**
of an internal S_i is with the unique
central inner square C.

Thus, if \(\mathrm{Anchor}(i)\) is false,
S_i has **exactly two actual square
neighbors**, the two positive path
neighbors, and it is **strictly
inside the containing circle**.

By the exact contact-minimal true-square
transmitter theorem in section 8 of
[HUMAN_CYCLE_ANALYSIS.md](HUMAN_CYCLE_ANALYSIS.md),
this circle-free actual-degree-two square
must have *opposite side-aligned contacts*.
It is a genuine interior transmitter.

If two **consecutive** internal labels
S_i and S_{i+1} both lacked anchors,
they would be adjacent genuine
**circle-free actual-degree-two
transmitters**, forbidden below disk
radius two by the adjacent-interior-
transmitter corollary in the same section.
This proves (1).

The minimum cardinality of a vertex cover
of a path on \(m-2\) vertices is
\(\lfloor(m-2)/2\rfloor\): the
\(\lfloor(m-2)/2\rfloor\) pairwise
disjoint internal edges
\((S_2,S_3),(S_4,S_5),\ldots\)
each demand a different anchored endpoint.
Alternating internal vertices exhibit a
cover of that size. This proves (2). QED.

## Strong global consequences for m=6

The **k=7, C-positive-degree-two, m=6**
root has exactly four internal stressed
outer squares \(S_2,S_3,S_4,S_5\).
The cover theorem forces **at least two
different internal labels** either to touch
the disk circle or to have an actual
central C contact chord.

This combines with the independently
proved three-mode actual-contact split
[HUMAN_M6_THREE_ACTUAL_CONTACT_MODES.md](HUMAN_M6_THREE_ACTUAL_CONTACT_MODES.md):

* **P (C actual degree exactly 2):**
  no internal C chords exist. Therefore
  **at least two of S2..S5 truly touch
  the circle**. In addition at least
  **one of the two stressed outer path
  endpoints S1,S6 touches the circle**,
  by the spectator-endpoint theorem.
  Hence
  \[
  \boxed{\text{mode P has at least
  THREE distinct true circle-contact
  outer squares on its stressed path}.}
  \]
* **S (C actual neighbors only S1,S6,T):**
  again there are no internal C chords.
  Therefore at least **two** internal
  path members S2..S5 touch the circle.
  The spectator T also has a true
  circle vertex by the exact actual-leaf/
  two-contact transmitter argument.
  Thus
  \[
  \boxed{\text{mode S has at least
  THREE distinct true circle-contact
  exterior squares, two of them
  internal to the stressed path}.}
  \]
  If T is an actual leaf, it must be
  a radial, C-parallel square attached
  on a central side **perpendicular**
  to the stressed C force normal,
  by HUMAN_LEAF_EXCLUSIVE_CENTRAL_SIDE.md.
* **K (an internal C contact chord):**
  the vertex-cover statement remains.
  In particular **a single internal
  zero-weight C chord cannot be the
  only anchor**; there must be at least
  one *other* anchored internal label
  (a true circle-contact square or
  an additional C chord).
  If the central stressed normal is a
  square diagonal, the stronger
  two-sided tangential-bracing theorem
  forces the separate true zero-stress
  contact-normal restrictions as well.

These conclusions are **whole packing
constraints**: any numerical model that
forgets the internal boundary vertices or
the true central contact chords misses
entire required geometric hypotheses.
No P/S/K case is yet proved impossible
as a whole.

## An m=3 four-square parallel scaffold dichotomy

There is one additional sharp
specialization of the same structural
principle. Suppose **m=3** and, besides
the B2/k7 hypotheses, C has **exactly
two actual neighbors** (the stressed
endpoints S1,S3).

Then C is a circle-free actual-degree-two
transmitter. The sole internal path
square S2 also has exactly two actual
outer neighbors (S1,S3); it has no C
contact because C's actual degree is
two.

* If S2 has a true disk-circle contact,
  it is a **boundary-anchored middle square**.
* Otherwise S2 is a **second circle-free
  actual-degree-two transmitter** sharing
  the *same neighbor pair* S1,S3 as C.
  Section 9 of HUMAN_CYCLE_ANALYSIS.md
  proves that **two such shared
  transmitters force all four square
  frames C,S1,S2,S3 to be parallel**,
  with the two transmitters placed in
  a genuine common-normal width-one
  strip between the same outer neighbors.

Therefore
\[
\boxed{\text{m=3, C actual degree 2}
\Longrightarrow
\text{(circle-contact S2)}
\ \lor\
\text{(exact FOUR-SQUARE
parallel scaffold C,S1,S2,S3).}}
\]

This recognizes an actual **candidate-like
parallel four-square motif** from
global minimality, instead of
assuming it in a diagram or frame ansatz.
It does not say the other four exterior
squares fit around that scaffold
at radius \(<\widehat R\).

## Exact finite-combinatorial audit

[verify_B2_internal_path_vertex_cover.py](verify_B2_internal_path_vertex_cover.py)
enumerates subsets of internal path labels
for m=3,4,5,6 and checks the exact minimum
vertex covers. The continuous geometry
behind (1) is the **analytic actual-contact
transmitter theorem**, not the graph script.

This is not yet the unconditional sharp
radius bound \(R_8\ge\widehat R\),
global equality classification, or a
Lean 4 proof. The real seven-outer
full-contact-cycle candidate remains
a different untouched root A.


## Stronger complete-graph corollary in the pure C-two-contact representative

The prior vertex-cover argument holds
whether C has two or more **actual**
contacts. When C has **exactly its
two positive-stress actual contacts**,
a stronger global theorem now applies:
[HUMAN_B2_PURE_CENTRAL_CONTACT_ISOLATES_SPECTATORS.md](HUMAN_B2_PURE_CENTRAL_CONTACT_ISOLATES_SPECTATORS.md)
proves **all spectator square
contact edges are impossible**,
because any proper nonempty
complementary outer path would
contain a true **noncentral
one-contact leaf**, violating
minimum-contact rigidity.

Thus in that pure root the entire
actual contact graph is the C-rooted
positive stressed cycle **plus
actually isolated outer spectators**;
there are no C-internal chords.
The two stressed outer endpoints
must **both** have true circle vertices,
and the current minimum distinct
circle-contact stressed outer label
counts are
\[
m=3:2,\qquad m=4:3,\qquad
m=5:3,\qquad m=6:4.
\]

All isolated spectators can, by an
arbitrarily small radial inward
translation, be selected to be
**strictly circle-free** while
retaining their outer-center
classification and preserving
the globally least radius;
see
[HUMAN_ISOLATED_OUTER_CIRCLE_FREE_NORMALIZATION.md](HUMAN_ISOLATED_OUTER_CIRCLE_FREE_NORMALIZATION.md).
They remain actual full unit
squares whose occupancy and SAT
constraints must be kept in
every sharp lower-bound argument.

This is a **complete structural
contact-graph subcase exclusion**,
not the still-missing sharp radius
inequality \(R_8\ge\widehat R\).


## The m=3 circle-free four-parallel scaffold alternative is now completely impossible

**This supersedes the earlier m=3 'circle contact
or parallel scaffold' still-open dichotomy.**

[HUMAN_B2_M3_PARALLEL_SCAFFOLD_EXCLUDED.md](HUMAN_B2_M3_PARALLEL_SCAFFOLD_EXCLUDED.md)
proves that, under the *pure* C-actual-degree-two
B2/k7/m3 hypotheses, a **circle-free internal
S2 square** is **impossible**.

Indeed the existing two-shared-transmitter
theorem would then force the four genuine
frames C,S1,S2,S3 all parallel, with
S1,S3 on opposite common-normal sides of
C and S2. The positive-circle-multiplier
vertex-cover theorem forces **both**
outer endpoints S1,S3 to have genuinely
positive physical circle-vertex weights.
Their actual two positive contact forces
are each exactly horizontal in that
common frame, so their resultant
physical circle forces must be
horizontal. For an axis-parallel
outer endpoint with signed nonzero
normal-center coordinate, this
is possible with positive
multipliers only if its **transverse
center coordinate equals zero**.
Both outer endpoint centers are
therefore on the same horizontal
diameter.

Since C has genuine opposite
unit-width side contacts, their
normal center coordinates are
\(c-1,c+1\), where |c|<1/2.
Positive circle vertices of both
axis-parallel endpoints then force
\[
R^2=(c-3/2)^2+1/4
    =(c+3/2)^2+1/4,
\]
giving c=0 and \(R^2=5/2\).
But eight unit squares have total
area 8, so \(R^2\ge8/\pi>
28/11>5/2\), contradiction.

Thus the **only** still-unexcluded
pure m3 geometry has its *sole
internal stressed outer square*
S2 also **true circle-contacting**.
Both endpoints already have
positive circle multipliers.
Hence **all three stressed outer
squares must touch the containing
circle**, not merely the
two endpoints.

This is a genuine **global,
complete conditional subcase
exclusion**, not an inferred
impossibility of all m3
stressed paths or of the
sharp equality-bearing outer ring.
