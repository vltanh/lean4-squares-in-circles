# Independent review of the actual-and-cone four-plus-three assembly

6 November 2026. This is a second-agent mathematical review, not a human
referee report. It checks the exact caller and coverage of
[ACTUAL_FOUR_131.md](ACTUAL_FOUR_131.md), especially its Section 9.
It reads the stated earlier theorems and the local guards invoked by the
new chapter. It is not a fresh independent verification of every scalar
argument in the full inherited dependency graph. No Lean or certificate
replay is used or asserted.

## 1. The reviewed theorem

Let nine original unit squares, each with its own frame, have pairwise
disjoint open interiors and lie in a centered disk of radius strictly
less than \(\sqrt{1105}/16\). Suppose four specified originals form a
horizontal projection chain and their three consecutive center
differences also satisfy the horizontal cone comparisons. Suppose three
distinct outsiders form a horizontal center-cone three-chain.

These predicates are incompatible. The two designated short links need
not have disjoint horizontal projections. In the notation of the proof
draft, this excludes exactly all four strict predicates `000/**` without
an additional selected-link assumption. The statement does not exclude
an arbitrary actual four-chain when the additional cone hypotheses are
absent, and does not assert that the unrestricted extraction makes the
three main links actual.

## 2. Normalization and the complete count table

Put \(l=29/60\). The original columns are \(x\le-l\),
\(-l<x<l\), and \(x\ge l\). The strict-radius
[side-capacity theorem](sources/UNRESTRICTED_ACTUAL_FOUR_CHAIN_SIDE_CAPACITY_HAND_PROOF.md)
places at most two outsiders in each side column. There are five
outsiders, so the following six rows exhaust their counts, up to
horizontal reflection.

| Left, central, right | Exact available contradiction |
|---|---|
| \((2,1,2)\) | [Full-side theorem](ACTUAL_FOUR_FULL_SIDES.md), requiring the actual-and-cone main chain but no selected outsider triple |
| \((2,2,1)\) | [Complete (2,2,1) theorem](ACTUAL_FOUR_221.md), with the designated outsider cone triple |
| \((2,3,0)\) | [One-sided theorem](ACTUAL_FOUR_230.md), Section 5, in the normalized closed-disk domain with inward span greater than two |
| \((1,3,1)\) | [New chapter](ACTUAL_FOUR_131.md), Sections 1--9 |
| \((1,4,0)\) | [Four-central theorem](ACTUAL_FOUR_140.md), in the normalized closed-disk domain with inward span greater than two |
| \((0,5,0)\) | The two cone links give total horizontal center span at least \(\sqrt2\), while the central strip has width \(2l=29/30<\sqrt2\) |

For a direct enumeration, arrange the two side counts so that the left
count is the larger. If it is two, the right count is two, one, or zero;
if it is one, the right count is one or zero; if it is zero, both are
zero. The central count is then fixed by the sum five.

Every strict counterexample permits a common center expansion by a
sufficiently small factor \(t>1\), with all physical frames fixed.
The finitely many strict corner margins preserve containment strictly
inside the target disk. The finitely many original central-column
margins preserve their column membership, while existing side membership
persists automatically. Every original separating projection has a
strictly positive support sum, so multiplication of its center gap by
\(t\) makes it strict. Thus the expanded closed squares are disjoint.
Actual links and homogeneous center-cone inequalities persist, and the
main inward span becomes strictly greater than two.

This normalization satisfies the closed-disk callers of the (2,3,0)
and (1,4,0) theorems without assuming invariance under expansion all the
way to the boundary. The (2,1,2) and (2,2,1) theorems can be applied
directly in their original strict-radius callers. Consequently the use
of differently stated normalization conventions does not leave a gap
in the six-row union.

## 3. The new (1,3,1) caller and its local dependencies

In this count there is one side original on each side and three central
outsiders. Each selected cone link has horizontal gap at least
\(1/\sqrt2\), by the two contained insets. Thus the selected middle
is central, with \(|x_P|<23/60\), and a selected endpoint must be
a side original. The original main-cone bound and physical clearances
put every central outsider above both inner mains or below both.
A common vertical reflection puts the selected middle above both;
the selected cone inequalities then put every selected endpoint above
its corresponding main. These steps require neither short link to be
actual.

The three possible counts of upper central outsiders are one, two, and
three. Opposite orders of the two side originals are excluded in
Section 2.3 using the local one-sided main-height bound and low central
cone-endpoint exclusion from Appendices C and D of
[ACTUAL_FOUR_221.md](ACTUAL_FOUR_221.md). Their exact guards are supplied:
the retained lower side original gives the main bound \(-17/50\),
and the selected central endpoint gives the horizontal bands and cone
comparison. The proof then invokes only Sections 1--4 of
[ACTUAL_FOUR_230.md](ACTUAL_FOUR_230.md), not its (2,3,0) occupancy
caller.

The remaining branches match the following complete cover.

| Upper central count | Surviving side conditions | Contradiction |
|---:|---|---|
| 1 | Both side originals above their mains; both high or one low | Sections 3--4 |
| 2 | Opposite side orders | Section 2.3 |
| 2 | Both sides above and at least \(3/5\) high | Section 6 |
| 2 | Both sides above, exactly one below \(3/5\) | Sections 7--8 |
| 3 | Opposite side orders | Section 2.3 |
| 3 | Both sides above, both high or one low | Section 5 |

Both sides below are impossible because a selected side endpoint is
above its own main. Two low upper sides are impossible by the selected
triple's horizontal span. These eliminations account for the alternatives
that do not appear as surviving rows.

The low-side and same-side central-floor input is the local theorem in
Appendix B of [ACTUAL_FOUR_CONE_TRIPLES.md](ACTUAL_FOUR_CONE_TRIPLES.md);
it is used with its stated central/main order and side-height guards.
The new one-upper case uses Appendix B of ACTUAL_FOUR_221 only after
proving the required whole floor and lower side height. The two-upper,
very-low-helper case uses Appendix E of that chapter only after proving
all four groups of guards: the helper's inset edge and top, the positive
central original's height and low floor, the right main inset top, and
the original high right shoulder. These are local inputs, so their uses
do not presuppose (2,2,1) occupancy in the (1,3,1) caller.

## 4. New geometric steps and boundaries

The new chapter retains both lower central originals in Section 3.
The rectangle diameter estimate when a main is at most \(-1/2\)
uses its own-half clearance for negative central centers and the generic
clearance for every central center; hence the conclusion applies to
both mains after reflection. The selected middle's good whole floor is
obtained from the reflected adjacent-inset barrier and the central-strip
pair cap, using those same two originals.

In Section 7 the distance bound with the moderate helper is convex in
the helper height after expansion, so its four endpoint comparisons
cover the full height rectangle. The lower bound on the central
horizontal coordinate then bounds the possible loss in its actual
upward separating axis by \(1/72\). Its raised contained inset,
rather than a replacement unit square, supplies the obstruction in
Section 8.

Section 8 retains both physical chiralities. Taking absolute components
of a unit-owned separating normal produces only a necessary inequality;
the corner lower bound uses the actual square's unchanged halfwidth and
vertex-offset magnitudes. The coordinate cases and the closed ranges
\([0,4/15]\), \([4/15,3/4]\), and \([3/4,1]\) cover every
normal. In the last near-vertical range, the stated positive derivative
makes the corner minimum occur at the left horizontal endpoint, and the
printed polynomial bound is uniform over that entire normal interval.

The side boundary \(x=\pm l\) belongs to the side columns. Height
\(3/5\) belongs to the high alternative; whole floor \(1/10\)
is retained in the bad-floor contradictions and the cap; the helper
height \(119/310\) belongs to the moderate range. The source clearances
include \(x=0\), and all reflections act on the centers and the original
frames together. None of these boundaries creates an omitted row.

## 5. Result of the review

The assembly and local caller coverage support the stated strict-radius
actual-and-cone four-plus-three theorem. No additional actual condition
on the short chain is needed. The proof has a complete occupancy cover;
the previous top-level description ending at the (2,2,1) result was stale.

The remaining unrestricted implication is still substantive: every cone
four-plus-three witness in a hypothetical strict counterexample must
have a weak main link. This review supplies no contradiction for that
remaining predicate, no archived closure count, and no global equality
classification.
