# An exterior stressed cycle must contain a near-center interior contact transmitter or branch

**2026-10-12 research continuation. Exact conditional structural theorem,
not an unrestricted sharp-radius proof.**

This resolves the correct *inner witness* and *actual contact degree*
subdivision of global stress-root X in
[HUMAN_GLOBAL_STRESS_ROOTS.md](HUMAN_GLOBAL_STRESS_ROOTS.md).
Its purpose is to force a real contact configuration, rather
than extrapolate a cap inequality or silently treat a
positive-stress degree-two vertex as an actual-contact
degree-two transmitter.

## Theorem: near-center stressed exterior witness

Let a radius-minimizing eight-unit-square packing
with \(R^2\le9789/2500\) be chosen **among radius
minimizers to have the fewest actual touching pairs**.
Write C for its unique open origin-containing square.

Choose a normalized physical contact/circle stress
from HUMAN_CONTACT_EQUILIBRIUM.md, and assume its
unique nontrivial positive-stress component **does not
contain C**. Also exclude the branch of a full
seven-outer actual-contact cycle.

Then there is at least one **noncentral exterior
square T** with all the following properties:

1. T belongs to a *directed nonzero-moment
   positive-stress cycle* of **5, 6 or 7**
   distinct exterior square labels.
2. Its center p_T lies in the strict annulus
   \[
   \boxed{\frac12<|p_T|<1.}                     \tag{1}
   \]
3. Its **entire actual closed unit square**
   lies strictly inside the disk,
   with a positive vertex-to-circle margin.
   In particular T has no circle contact
   and every active circle multiplier is zero.
4. T has **at least two distinct positive-moment
   incident contact pairs**. Consequently its
   *actual* contact degree is at least two.
5. If T has **exactly two actual contacting
   neighbors**, they act on its two opposite
   frame sides, and **T has a side normal
   parallel to their unique opposite contact normals**.
   Its two neighbors are a Euclidean distance
   **exactly one** apart. If T has at least three
   actual neighbors, retain the **branching**
   exterior-cycle case; no parallel or
   transmitter conclusion is asserted.

These statements are for actual square geometry
and hold for independent orientations.

## Proof

The four-root theorem
HUMAN_GLOBAL_STRESS_ROOTS.md proves the
existence of a directed nonzero-moment
**exterior** positive-stress cycle with
5..7 vertices, including at least one
square T whose center has norm <1.
All those cycle labels are exterior, so
T is **not** C. This gives the upper
radius bound \(|p_T|<1\).

Because C contains zero in its *open*
interior and the packed square interiors
are disjoint, every other **closed**
square must omit zero. The closed
inscribed radius-1/2 disk about p_T
lies inside T. If \(|p_T|\le1/2\),
this inscribed closed disk would contain
zero, contradicting that T is exterior
while C contains zero in its open interior.
Therefore \(|p_T|>1/2\), proving (1).

Every point z of a unit square with center p_T
satisfies \(|z|\le|p_T|+\sqrt2/2\).
Thus
\[
|z|<1+\sqrt2/2
<\sqrt2+1/2<R_8,
\]
where the final strict packing-radius
lower bound is the established
analytic inequality indexed by
HUMAN_CONTACT_COMPONENTS.md.
This proves that **T is strictly
circle-free** (all four vertices, all
edges and the whole square are inside).
In particular its circle multipliers
vanish and its contact forces balance
with zero resultant.

A simple directed positive-moment cycle
uses one incoming and one outgoing
*distinct* contact edge at every vertex.
Thus T has at least two incident
**positive-stress contact pairs** and
actual degree at least two.

Now use the **actual** minimum-contact
representative, not merely a chosen
stress. Section 8 of
[HUMAN_CYCLE_ANALYSIS.md](HUMAN_CYCLE_ANALYSIS.md)
proves: a strictly circle-free square
with exactly two *actual* contacting
neighbors in that representative has
unique opposite separating normals and
its own side normal parallel to them.
Section 9 proves that its two neighbor
squares are at **exact Euclidean distance
one** (not merely projected one apart).
Therefore if deg_actual(T)=2, the
stated aligned transmitter conclusion
holds. If deg_actual(T)>=3,
that theorem does **not** apply and
the branching possibility must be
retained. This proves all claims. QED.

## Why the degree distinction matters

An inner exterior square may have precisely
two **positive** contact edges yet one or
more additional *zero-weight actual contacts*.
Such a square has actual degree >=3,
and one cannot invoke the minimum-contact
two-neighbor alignment theorem merely from
the degree of a selected physical stress.
The exact root-X proof must therefore
retain two separate geometric continuations:

* **X2: transmitter present.** A near-origin
  exterior actual-degree-two square with
  center radius in (1/2,1), opposite
  aligned frame sides, and two exterior
  neighbor squares at exact distance one.
  Its existence is *conditional* on some
  cycle inner witness having actual degree2.
* **X3: interior branching.** Every
  exterior inner-center square on the
  positive-moment cycle has actual
  degree>=3. The extra zero-weight
  contacts and genuine three-force
  balances must be kept and analyzed.

Neither branch is eliminated by the
current arguments; they represent
different possible routes to the
sharp five-corner support inequalities.

This is not a global \(R_8\ge\widehat R\)
proof, nor a contact-degree classification
of all minimizers. The actual seven-outer
candidate equality ring remains intact,
and no unproved degree-two assignment
has been made.
