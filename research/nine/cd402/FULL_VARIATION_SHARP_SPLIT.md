# Use the full sharp variation guard, not only its small rectangular subset

**Status: complete reduction of five saved frontier predicates; no new
whole-original closure.** This changes neither the Cd402 original nor the
231-cell register. It supplies a sharper terminal and a finite, explicit
complement for the existing table. Numerical visualizations suggested the
choice, but are not premises of the reduction.

## Original-square hypotheses and imported sharp theorem

Retain the unchanged normalized original-nine Cd402 predicate: actual
AB, BC, EF, FG; strictly weak CD; the five marked center-cone comparisons;
all original frames, corners and physical pairs; A's canonical tilt
nonnegative and D's nonpositive; x_H <= x_I; strict radius q < 1105/256.
The accepted extra-strip theorem gives x_A < x_H <= x_I < x_D.

The previously accepted full-angle opposite-endpoint four-row theorem,
with the literal original row A,H,I,D and actual original E,F,G, applies
whenever

    V = |y_H-y_A| + |y_I-y_H| + |y_D-y_I| <= 23/100.

It then forces q >= 1105/256. The complete theorem and its exact scope
are imported from the archived whole-original eight-height assemblies,
not inferred from a pose or from a partial search:

- `A2_00100_C887_WHOLE_ORIGINAL_EIGHT_HEIGHT_CHECKPOINT.md`,
  section "Whole-original theorem attachment";
- `A2_00100_CB882_WHOLE_ORIGINAL_EIGHT_HEIGHT_CHECKPOINT.md`,
  section "Why the eight closed domains cover every possible survivor".

Both are pinned at archive commit
`6a9a45e0ad997c8e143b0f22a0de88370d9d7adb`. Their full-angle scalar
source has 80 domains and 1,405 leaves. This continuation reuses that
accepted theorem; it does not claim a fresh replay of its scalar archive.
The original names B and C remain physical and are not replaced by H,I.

The stated hypotheses hold in Cd402 as well: their proof uses the same
original mask, endpoint signs and extra strip, not the special C887 or
Cb882 escape inequality. Thus every Cd402 strict counterexample has

    V > 23/100.                                           (1)

## Why the old rectangular guard was smaller

The saved central leaf 505 used three bounds of magnitude at most 1/16.
They imply V <= 3/16 < 23/100. But failing one of those three bounds does
not imply V > 23/100. For example (a,b,c)=(0,1/16,0) fails a strict
rectangular test while still having V=1/16.

The reduction below applies the whole accepted sharp theorem and retains
its entire complement. It does not simply delete the old outer leaves.

## The exact four-way complements on each of the five saved leaves

Put a=y_H-y_A, b=y_I-y_H, c=y_D-y_I. Each listed leaf already supplies
one known sign. For every independent s,t in {-1,+1}, retain the indicated
closed halfspace:

| Existing saved leaf | Inherited sign | Four closed remaining domains |
|---|---|---|
| 495 | a <= -1/16 | -a + s*b + t*c >= 23/100 |
| 498 | a >= 1/16 |  a + s*b + t*c >= 23/100 |
| 499 | b <= -1/16 | -b + s*a + t*c >= 23/100 |
| 502 | b >= 1/16 |  b + s*a + t*c >= 23/100 |
| 506 | c <= -1/16 | -c + s*a + t*b >= 23/100 |

Every domain retains the complete original leaf ancestry, including the
other preceding height bounds and all physical alternatives. For instance,
leaf 506 retains |a|<=1/16 and |b|<=1/16; neither is silently removed from
its caller. Its inherited condition y_I-y_D>=1/16 is exactly c<=-1/16.

The maximum of the four displayed signed forms is V, using the inherited
sign in that row. Equation (1) therefore puts every surviving original
configuration in at least one of the four closed domains. All equality
faces are retained. Conversely no exclusion of any complement is claimed
until that complete conditional domain has its own proof. This is a finite
proof split inside the same five leaves, not twenty new original cells or
a change to the fixed external progress denominator.

## Current boundary

The exact boundary control in `visualize_boundary.py` has a=b=c=0 and is
correctly handled by the sharp terminal, not by a positive-margin LP
contradiction. The numerical near-boundary plots also suggested this
larger guard; their numerical minima prove nothing about the complements.
The other eight saved frontier leaves are unchanged. A complete Cd402
proof must still discharge every remaining complementary domain and
preserve all already established sibling exclusions. No Lean or CI was run.
