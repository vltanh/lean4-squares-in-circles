# A nonparallel radial stress bridge forces real zero-weight spectator bracing

**Structural research, 2026-10-13.** This theorem distinguishes
a square with exactly one **positive-stress** contact from a
square with exactly one **actual** contact. It is a full
actual-contact necessity in the minimal k=7 central-branching
triangle-plus-leaf core, not a radius-interval result.

## Theorem

Choose an attained least-radius packing of eight true unit
squares with the **fewest actual square-square contacts**.
Assume the exact smallest k=7 B3 positive stress component
\[
C-X-Y-C\quad\text{plus the radial bridge }C-Z
\]
as in [HUMAN_B3_THREE_OUTER_TRIANGLE_LEAF_NORMAL_FORM.md](HUMAN_B3_THREE_OUTER_TRIANGLE_LEAF_NORMAL_FORM.md).
The outer actual-contact graph is a *proper* subgraph of
the seven-ray neighbor cycle. The positive outer X,Y are
consecutive, while Z is one of the three nonadjacent
outer ray positions. Four outer labels are spectators of
the positive stress.

Let Z's bridge use one of the three genuine interface types
from [HUMAN_RADIAL_BRIDGE_THREE_SAT_INTERFACES.md](HUMAN_RADIAL_BRIDGE_THREE_SAT_INTERFACES.md):

* SS: C side / Z side, with C and Z parallel;
* CS: C radial corner / Z side;
* SD: C side / Z diagonal.

Then:

1. If Z has **only one actual square neighbor**, namely C,
   it necessarily uses the genuine **SS** interface.
   It is a radial C-parallel actual leaf with two true
   positively weighted circle vertices.
2. In either **CS** or **SD** mode, Z must have an
   **additional actual square-square contact** with at least
   one of its **two circularly adjacent outer spectator
   labels**. Such a contact has **zero positive stress**:
   \[
   \boxed{
   \text{CS or SD}\Longrightarrow
   Z\sim T\text{ actually, for some spectator }T,
   \quad \lambda_{ZT}=0.
   }                                                 \tag{1}
   \]
3. If Z touches **exactly one** such outer spectator T,
   then **T cannot have only Z as its actual neighbor**.
   To avoid a forbidden noncentral actual leaf, T
   must additionally contact C or its other cyclic
   outer neighbor. In particular, the zero-weight
   Z--T edge requires a continuation of the **real
   actual-contact scaffold**.

No conclusion is asserted that the full CS or SD modes
are impossible after adding these true bracing contacts.

## Proof

**1. A single actual contact invokes the complete leaf theorem.**
In the chosen minimum-actual-contact radius minimizer,
the exact theorem
[HUMAN_STRESS_GRAPH.md](HUMAN_STRESS_GRAPH.md)
and [HUMAN_ACTUAL_BRIDGES.md](HUMAN_ACTUAL_BRIDGES.md)
states that every unit square having exactly **one actual
square contact** has C as its unique neighbor and is a
**radial actual leaf with frame parallel to C**, touching
the circle in the two vertices of its outer side.
Its actual contact uses a true **common side normal**.

Therefore if Z has no actual square contacts besides
its positive stress C--Z edge, that theorem forces
C/Z interface **SS** in the independently proved
three-interface classification. Thus CS and SD are
impossible with Z of actual degree one.

**2. Only spectator outer labels could brace Z.**
If Z is CS or SD it must consequently have some
actual contact with a square other than C.
All seven exterior centers are outer, and the
outer-center visibility theorem
[HUMAN_OUTER_GRAPH_REDUCTION.md](HUMAN_OUTER_GRAPH_REDUCTION.md)
proves an outer-center unit can actually touch only its
two circular-ray neighbor outer labels.

Because the exact minimal B3 graph classification
places Z at a ray index **nonadjacent to both X
and Y**, those two neighboring outer labels are
**spectators of the chosen positive stress**.
Any extra actual Z contact is therefore with at
least one such spectator T. As Z has exactly one
positively stressed neighbor C, every such Z--T
actual contact has **zero** chosen stress weight.
This proves (1).

**3. An auxiliary spectator cannot itself be a noncentral leaf.**
Suppose Z touches exactly one additional outer
spectator T and T has no other square contact
besides Z. Then T is an actual contact-graph
leaf with sole **noncentral** neighbor Z.
The same minimum-contact actual-leaf theorem
says its unique neighbor would have to be
C, contradiction. Consequently T must contact
some other square in addition to Z.

By outer angular visibility, T's only other
possible outer neighbor is its other circular
neighbor; or T may actually touch the central C.
There are no noncentral inner-center squares in
the k=7 branch. Thus one of these two additional
actual contacts must occur, proving claim 3. QED.

## Precise B3 computer-to-hand case queue

The positive radial Z bridge is no longer a generic
single edge with arbitrary Z frame. It has the
following exhaustive actual-contact modes:

| Positive bridge interface | If Z actually touches only C | If extra actual contact is needed |
| --- | --- | --- |
| **SS** (parallel side-to-side) | Allowed by this theorem; an actual central leaf | Not required, but possible; model zero-weight extra contacts |
| **CS** (C radial corner, Z side) | **Impossible** | Must have a true zero-weight contact with neighboring spectator |
| **SD** (C side, Z inward diagonal corner) | **Impossible** | Must have a true zero-weight contact with neighboring spectator |

A bracing spectator cannot be an uncontinued outer-only
actual leaf, so the CS/SD actual contact graph must contain
a larger **zero-positive-weight path or central chord**.

The side-mode SS actual leaf monopolizes its high
whole cap, by the previously proved high-cap theorem;
its positive circle vertices occur in an equal-weight pair.
The diagonal SD mode has a single positive circle vertex
and must be externally braced.

This is an actual-contact structural reduction, not a
proof of \(R_8\ge\widehat R\) or elimination of all k=7/B3
small branching cores. The full seven-outer actual-contact
ring equality construction is outside the hypotheses.
