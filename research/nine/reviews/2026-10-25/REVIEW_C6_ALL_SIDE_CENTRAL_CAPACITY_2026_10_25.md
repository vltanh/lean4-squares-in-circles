# Independent review: the complete all-side C6 central capacity is one

Date: October 25, 2026. Reviewer: root, independently of `c6_joint`.

**Verdict: PASS.** `SIX_CYCLE_ALL_SIDE_CENTRAL_CAPACITY_ONE.md`
proves that the entire central free union has unit-square capacity at
most one whenever its original all-side alternating C6 has distinct
applications on one side of each loaded square and all three force
turns are strictly obtuse. The complete remaining all-unique one-share
and two-share families satisfy those premises. No new coefficient
certificate or checklist identifier is introduced.

## 1. The premises come from the actual six-body certificate

I read `SIX_CYCLE_UNIQUE_STRICT_TURN_AND_SHARED_NORMAL_FORM.md`
and `SIX_CYCLE_SHARED_SUPPORT_FUNCTIONAL.md`. The former proves all
three turns belong to `(pi/2,3pi/4]`, with distinct original means on
one physical inner side; the latter gives the exact channel displacement
`p_(i+1)^- - p_i^+ = n_i`. The statements retain the original side
means, including endpoints of genuine shared intervals. The new proof
does not replace a shared mean by a vertex or assume its side chord is
strictly shorter than one.

The incoming mean minimizes the previous normal and the outgoing mean
maximizes the next normal. Taking their difference proves both support
dot-products in Section 2. At a turn `theta` strictly between `pi/2`
and `pi`, their intersection gives the actual chord direction
`theta-pi/2 <= eta <= pi/2`. Consequently the two consecutive direction
changes remain strictly between zero and pi even at either support
equality. This is the relevant endpoint check.

## 2. Convexity and the full central region

The six positive edge lengths alternate between one and the original
`ell_i in (0,1]`. Their directions increase strictly through exactly
one turn. For each fixed edge, the other edges' perpendicular increments
are first positive or zero and then negative or zero; the first is
strictly positive and the last strictly negative. Closure therefore
puts every nonincident vertex strictly on the same side of that edge.
This proves the stated strict convexity without assuming simplicity
from a generic drawing. Its perimeter is exactly `3+sum ell_i <= 6`.

I separately read the complete `CONTACT_RING_HOLE_AREA.md`,
`PHYSICAL_BODY_GRAPH_UNCROSSING.md` and
`SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md` inputs. They supply an arbitrarily
close compatible physical cycle and define the central free union by
its inside winding label. They cover all central components, not just
one face of a limiting contact picture.

An open point of an extra square has positive distance from the closed
core. The physical routing can be chosen closer than that distance.
Homotoping each body path to its actual chord inside the occupied body
(with its arbitrarily small routing neighborhood first collapsed)
preserves winding about that point. The limiting contact curve is the
strictly convex hexagon just proved, so every such point is inside it.
Applying this to compact inner portions and taking closure includes each
whole central extra at coincident junctions and shared endpoints. Extra
zero-stress contacts can subdivide free space but cannot evade this
inclusion. No actual square, force or mean is moved.

## 3. The perimeter obstruction and its equality case

I independently derived the width formula for two centered symmetric
squares, at center displacement `d`:

    width(conv(K union L),n)
       = h_K(n)+h_L(n)+max(|d dot n|,|h_K(n)-h_L(n)|).

Integrating over a half-turn gives
`Per(conv(K union L)) >= 4+2|d|`. A separating line for disjoint
open unit squares gives `|d|>=1`, since both support half-widths are
at least `1/2`. Hence their hull perimeter is at least six, for all
relative orientations.

If this perimeter is six, the same inequalities force `|d|=1`,
alignment of `d` with a separating normal, and both half-widths equal
to `1/2`. Both squares then have that normal as a side axis and share
a full side; their hull is exactly a `2 by 1` rectangle. No equality
claim for a merely sampled orientation is used.

Convex perimeter is strictly monotone for a proper inclusion of compact
convex sets with nonempty interior: a strict support-function difference
persists on an open angular interval, and its width integral is positive.
Thus if two extras were central, their hull inside the hexagon would
force equality of both perimeters and equality of both sets. A rectangle
cannot equal a hexagon with six strict vertices. This completes the
contradiction even when all three original chords have length one.

## 4. Exact consequence and retained open work

The whole all-unique all-side one-share and two-share families now have
at most one central extra and hence at least two extras in their actual
exterior channel regions. The existing `UNIQUE_SHARED` gate remains
open: this theorem alone does not exclude two exterior extras, require
them to occupy different pockets, or exclude one central plus two
exterior extras. No new gate is created to count this necessary bound.

The geometric theorem is independent of a unique-corner force-value
identity. It may be applied to other masks only after their actual
strict-turn and same-side port premises are proved. In particular it
does not close the full exactly-one-radial family by scope substitution.

The original nine squares, all individual circle-weight endpoints,
physical masks and all three arbitrary completion squares remain.
The unrestricted sharp bound and equality classification stay open.
No Lean compilation, CI or workflow dispatch was used.
