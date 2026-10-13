# All zero-stress spectators are actually isolated when C has only its two stressed contacts

**2026-10-12. A complete global actual-contact graph rigidity theorem.**
This **eliminates every extra spectator contact edge** in
the k=7, centrally two-stressed, actual-central-degree-two
outer-path root. It is stronger than the previous
boundary-or-spectator case split and does not optimize
any real cap/radius constant.

## Theorem: actual-contact graph equals the positive cycle plus isolates

Let an attained least-radius packing of eight genuine unit squares
in \(D_R\), \(R^2\le9789/2500\), be chosen among all such
minimizers with **the fewest actual square-square contacting pairs**.
Let C contain the disk origin in its open interior.

Assume:

1. All seven noncentral center norms are \(\ge1\)
   (the **k=7 outer-center branch**);
2. Their induced **actual-contact graph is a proper
   subgraph of the cyclic seven-center ray-neighbor graph**;
3. A normalized physical stress has exactly two distinct
   positive C-contact neighbor labels \(S_1,S_m\)
   and its unique nontrivial positive-stress component
   is the single C-rooted cycle
   \[
   C-S_1-S_2-\cdots-S_m-C,\qquad 3\le m\le6,
   \]
   where S1,...,Sm are consecutive outer center-ray
   labels in circular order;
4. C has **exactly two actual square-contact neighbors**,
   namely the two positive-stress endpoints S1 and Sm.

Then the **complete actual square-contact graph**
of the entire eight-square configuration consists of
**exactly one nontrivial component**, precisely the
positive C-rooted m-outer cycle above, plus
\[
\boxed{7-m\text{ completely isolated exterior
square labels}.}                               \tag{1}
\]
Every exterior spectator not among S1,...,Sm has **actual
square-contact degree zero**, not merely zero positive
stress. There are **no** extra zero-stress actual contacts
between spectators, between spectators and stressed outer
squares, or between spectators and C.

Consequently:

* Both **stressed path endpoints S1 and Sm have
  true disk-circle vertices** (not just "at least
  one" endpoint).
* Since there are no internal central C contact
  chords, the existing stressed-path internal
  vertex-cover theorem forces at least
  \[
  \left\lfloor\frac{m-2}{2}\right\rfloor
  \]
  distinct **internal stressed outer squares** to have
  true disk-circle vertices.
* Thus the stressed outer path has at least
  \[
  \boxed{2+\left\lfloor\frac{m-2}{2}\right\rfloor}
  \]
  different circle-contact labels:
  \[
  \begin{array}{c|cccc}
  m&3&4&5&6\\
  \hline
  \text{minimum true circle-contact path labels}
    &2&3&3&4 .
  \end{array}                                    \tag{2}
  \]
* In the m=3 case, if its sole internal square S2
  is circle-free, it and C are two distinct
  actual-degree-two interior transmitters with the same
  outer neighbors S1,S3, so the exact shared-transmitter
  theorem forces the genuine
  **four-square parallel scaffold** \(C,S_1,S_2,S_3\).

The known exact seven-outer **full actual-contact
ring equality configuration** is excluded from the
hypotheses by condition 2, and therefore
**remains valid**. The theorem does not claim
the remaining 28 stressed graph supports are
geometrically realizable or globally impossible.

## 1. The only possible extra outer contacts lie on one complementary spectator path

By the outer-center visibility theorem
[HUMAN_OUTER_GRAPH_REDUCTION.md](HUMAN_OUTER_GRAPH_REDUCTION.md),
every actual square-square contact joining
two outer centers must join **consecutive
center rays** in their circular ordering.

The m outer labels S1,...,Sm of the positive
stressed path are consecutive in that
circular ordering. The positive stress
already forces each of the m−1 path
edges \(S_i-S_{i+1}\) to be a
**genuine actual square contact**.

Write \(T_1,\ldots,T_{7-m}\)
for the remaining outer spectator labels,
in the complementary circular order
\[
S_m,T_1,\ldots,T_{7-m},S_1.
\]
Thus **every possible further actual
outer-outer edge** belongs to one
complementary path
\[
S_m-T_1-\cdots-T_{7-m}-S_1.                     \tag{3}
\]
There are \(8-m\) optional edges
along this complementary path.

Because the actual outer graph is
**not** the full seven-center cycle,
at least one of those optional
complementary path edges is absent.
No spectator has an actual C contact,
since by assumption C has only its
two stressed endpoint neighbors.

## 2. A nonempty proper spectator path would create a forbidden noncentral leaf

Assume for contradiction that **at least one**
edge of the complementary path (3)
is actually present. Since not
**all** its edges are present, the
present optional edges form one or
more **nonempty path segments**,
each a maximal contiguous run of
present edges separated by missing edges.

Every such maximal proper run has
**at least one endpoint that is a
spectator T_j**, not S_m or S_1:
otherwise the run would span the
entire complementary path from
S_m to S_1, meaning all optional
edges were present, which would
make the outer actual graph the
forbidden full seven-cycle.

Choose such a spectator endpoint T_j
of one maximal present-edge run.
Within the outer-induced actual graph,
T_j has **exactly one actual
outer neighbor**: its other cyclic
outer-neighbor edge is absent by
maximality. It has no nonconsecutive
outer contact by angular visibility,
and it has **no actual C contact**
by assumption 4. Because k=7,
there are no other noncentral inner
square labels it could touch.

Therefore T_j has **exactly one
actual square-square contact**, with
another **noncentral exterior square**.

But the general actual-leaf theorem
in [HUMAN_STRESS_GRAPH.md](HUMAN_STRESS_GRAPH.md),
section 1, proves that **every actual
one-contact square in a contact-minimal
least-radius packing must have the
central origin-containing square C as
its sole contacting neighbor**.
This contradiction eliminates **every**
nonempty selection of spectator outer
edges.

Consequently the entire complementary
outer path (3) has **zero actual
edges**. Each spectator has no
outer contact and, by assumption 4,
no central C contact either. Therefore
each spectator is **actually isolated**.

No further actual contacts can occur
among stressed path vertices: outer
angular visibility already restricts
each to its two circular outer
neighbors, and C has only its
two stressed endpoint contacts.
Thus the entire actual contact graph
is **exactly** the positive C-rooted
cycle plus isolated spectators. QED for (1).

## 3. Both stressed endpoints must circle-touch

The central square C lies strictly
inside the disk because zero is in its
open interior and its diameter is
\(\sqrt2<R\). Since C has precisely
two actual contacts in a
contact-minimal minimizer, section 8 of
[HUMAN_CYCLE_ANALYSIS.md](HUMAN_CYCLE_ANALYSIS.md)
makes it an aligned
**circle-free actual-degree-two
transmitter**, with two opposite
contact side normals.

By section 2, neither path endpoint
S1 nor Sm touches any spectator.
Each has precisely its positive
outer-path neighbor S2 (or S_{m-1})
and its central contact C.
Hence S1 and Sm both have
**actual contact degree exactly two**.

If either endpoint were strictly
circle-free, it would itself be an
actual-degree-two interior transmitter
by the same section 8. But it
would then be **adjacent to the
circle-free transmitter C**,
contradicting the exact corollary
that two interior transmitters
cannot be adjacent when R<2.

Therefore **both** S1 and Sm
touch the containing circle at
actual square vertices. QED.

## 4. Actual internal circle witnesses and the m3 parallel scaffold

Every internal stressed-path outer
label S_i, \(2\le i\le m-1\),
has exactly its two positive outer
path contacts and no C contact.
By
[HUMAN_B2_INTERNAL_PATH_VERTEX_COVER.md](HUMAN_B2_INTERNAL_PATH_VERTEX_COVER.md),
the set of internal square labels that
have true disk-circle vertices is
a **vertex cover** of the
internal path. It must contain at least
\(\lfloor(m-2)/2\rfloor\) labels.
Adding the two distinct circle-contact
endpoints gives the counts in (2).

For m=3, the sole internal S2
has exactly two actual contacts to
the two outer endpoints S1 and S3.
If S2 is circle-free, it and C
are two different circle-free
actual-degree-two transmitters
sharing the *same* actual neighbor
pair S1,S3. By section 9 of
HUMAN_CYCLE_ANALYSIS.md all four
genuine square frames must be
parallel in a shared width-one
strip between S1 and S3.
If S2 is circle-contacting, it
supplies a different boundary
anchor and no parallel scaffold
is asserted. QED.

## 5. Exact finite combinatorial case collapse

The previous all-possible *outer
actual-contact supergraph* enumeration
in
[HUMAN_B2_ENDPOINT_BOUNDARY_OR_SPECTATOR.md](HUMAN_B2_ENDPOINT_BOUNDARY_OR_SPECTATOR.md)
found, for seven cyclic placements
of each positive stressed path,
\[
7(2^{8-m}-1)
\]
proper outer graph supertemplates.
Across m=3,4,5,6 these number
\(217+105+49+21=392\).

**The present theorem rules out
all extra actual spectator edges
in the C-actual-degree-two root.**
Thus for each m the *only
remaining actual outer graph* is
the **bare stressed outer path**
itself, with seven cyclic
placements, leaving exactly
\[
\boxed{7\cdot4=28}
\]
combinatorially possible **complete
actual contact graph supports**,
before any continuous packing or
sharp radius inequalities are checked.

This is a reduction of **364
previously admitted graph-only
supertemplates** within the exact
hypotheses. It is **not** a
reduction of the unrelated
3,995,040 symbolic central-side
status words, and it does not prove
that any of these 28 graph supports
is geometrically feasible.

The independent pure graph audit
[verify_B2_isolated_spectators.py](verify_B2_isolated_spectators.py)
enumerates the optional edge runs
and confirms every nonempty proper
optional selection produces an
actual-degree-one spectator.
The mathematical exclusion of such
a leaf is the *previously proved
true-square actual-leaf theorem*,
not a computer simulation. QED.

## Global proof significance and open cases

For **k=7/B2 central actual degree two**,
we now have a strong *all-square
contact normal form*:

* One true central side-aligned
  stressed cycle C-S1-...-Sm-C,
  with m=3,4,5,6 and all its m+1
  actual contacts carrying positive stress;
* \(7-m\) **completely isolated
  actual-contact spectators** (still
  genuine space-occupying unit
  squares with true disk vertices);
* both stressed path endpoints
  touching the circle, and further
  internal circle-contact counts (2).

The next meaningful proof must show
this entire structure forces
\(R\ge\widehat R\), or forces
a candidate-like five-corner
support inequality with the
spectators included. It is **not
valid** to drop isolated spectators
from the disk occupancy problem.

If C has three or more **actual**
contacts but only two **positive**
stress contacts, zero-weight central
spokes can prevent the leaf
argument. Those cases are exactly
the S and K modes for m6 and
must remain under separate study.
The real full seven-outer contact
ring equality packing belongs to
root A and is unaffected.

The unrestricted sharp optimality
inequality \(R_8\ge\widehat R\),
full equality classification and
Lean formalization remain OPEN.
