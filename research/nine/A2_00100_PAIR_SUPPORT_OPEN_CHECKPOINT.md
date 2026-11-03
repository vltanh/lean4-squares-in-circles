# Pair-support continuation: original mask still OPEN

November 3, 2026. This is a source-bound research continuation after the
[nine-cell proof checkpoint](A2_00100_ORDERED_DISTANCE_AND_FRAME_CONTINUATION.md).
It closes **zero additional original cells and zero whole masks**.
The accepted register remains **168 CLOSED / 63 OPEN**, and the mask
ledger remains **8 CLOSED / 24 OPEN**. All original paths, strict bits,
physical pairs, roadmap IDs and equality obligations are retained.

The new physical inequalities are proved and their used arithmetic is
independently replayed. They improve an unfinished original parent's
internal proof, but do not supply the missing complete parent exclusion.
No Lean, Lake or CI was run; no human or proof-kernel audit is claimed.

## 1. A distance bound that uses both original frames

For two original unit squares, write their canonical side frames as
`(alpha_i,beta_i),(-beta_i,alpha_i)` and similarly for j. Set

    c = alpha_i*alpha_j + beta_i*beta_j,
    s = alpha_i*beta_j - beta_i*alpha_j.

The canonical frame gives `alpha>=|beta|`, hence `c>=0`. Every possible
signed original separating axis has support sum `(1+c+|s|)/2`. Physical
nonoverlap therefore implies

    ||center_j-center_i|| >= (1+c+|s|)/2.

There is no choice of a separating owner in this implication. Folding
both betas to their actual absolute values gives a second valid lower
threshold. This also couples the absolute-beta variables that an
uncoupled linear relaxation can otherwise misuse.

The [complete hand proof](OWNER_FREE_RELATIVE_SUPPORT_HAND_PROOF.md)
checks all axis owners, both signs, zero betas and orientation endpoints.
It derives exact affine rows from nonnegative rectangle products and
the original identity relating a square's frame to its slope. All nine
physical originals remain present.

One static pass checked the 61 remaining original parents other than the
two shallow A/B roots, which had their own static tests. **None of the
63 whole original parents closed by these rows alone.** The preserved
numerical proposals and source hashes document that negative result;
solver feasibility is not a physical packing certificate.

## 2. Proved pair differences before stronger secants

The same row system can prove bounds on `x_j-x_i` and `y_j-y_i` by exact
nonnegative rational combinations. A round uses the preceding matrix;
its deductions are installed simultaneously only after every exact sum
passes. No proposed LP bound becomes a premise on its own.

Two rounds give 168 new pair-difference deductions for the entire shallow
A parent and 171 for the entire shallow B parent. The independent
reviewer reconstructs all 339 deductions, their 33 and 30 inherited
coordinate deductions, and every final difference interval. A second
implementation separately recomputes the 339 sums from 644 printed
used rows. Both whole parents remain OPEN.

An existing ordered octagon diagonal child supplies further exact bounds.
Its primary diagonal and four predecessor complements force each signed
rotated coordinate into `[5/13,12/13]`. The recorded rational rotation
then gives original-coordinate difference intervals. Exact triangle
identities among the nine original centers propagate them, with every
new bound citing earlier antecedents. The
[hand lemma](ORDERED_OCTAGON_PAIR_DIFFERENCE_HAND_LEMMA.md) proves the
complete implication, including closed faces and negative-cycle terminals.

These intervals sharpen the same physical squared-distance rows. They
add no branch and do not change an old path's midpoint, sign or meaning.

## 3. A guarded chord of the distance disk

There is a stronger linear consequence when proved signed coordinate
caps `u<=a`, `v<=b` satisfy `a^2+b^2<r^2`, while physical separation
requires `u^2+v^2>=r^2`. Choose exact nonnegative rational lower roots

    p^2 <= r^2-a^2,   q^2 <= r^2-b^2,

with `b+p>0` and `a+q>0`. Then every physical point satisfies

    (b+p)*u + (a+q)*v <= a*b-p*q.

To check it, a strict violation gives nonnegative
`mu=(a-u)/(a+q)`, `nu=(b-v)/(b+p)` and positive
`lambda=1-mu-nu`. The point is their convex combination of
`(a,b)`, `(-q,b)` and `(a,-p)`. Those vertices have squared norm strictly
below, at most, and at most `r^2`, respectively. Convexity with
`lambda>0` contradicts the physical lower distance. Every guard and
vertex comparison is exact.

The [chord hand lemma](CLIPPED_CENTER_DISK_CHORD_HAND_LEMMA.md) and its
independent checker retain the same original pair and the previously
proved difference intervals. This row closes one further existing A
descendant; the two whole A/B roots remain OPEN.

## 4. Complete accounting inside the one OPEN A original

All results here refer to the unchanged original
`positive-2d5aba857f2f7602`. The final complete partial cover contains
840 paths and the same 395 internal split nodes. The later filters add
no branches.

| Context | Independently proved terminal paths |
|---|---:|
| Retained original-distance V3 tree | 629 |
| Original-frame V4 filter | 163 |
| Relative-orientation support filter | 24 |
| Inherited and path-specific difference filter | 2 |
| Guarded clipped-disk chord | 1 |
| **Proved terminals** | **819** |
| **Explicit pending paths** | **21** |

Every one of the 819 terminal paths has an independent exact replay.
The previous V4 sample boundary is removed: all 163 V4 leaves, including
the 98 previously unreviewed ones, were checked. All 629 retained V3
leaves were also replayed independently. The separate saved deep-leaf
example is redundant and is not counted again.

The composition checker matches every source index and exact path across
successive filters and verifies the complete finite child union. It
keeps all 21 pending paths explicit. Thus the original parent remains
**one OPEN original cell**, not 21 new external obligations. Its terminal
count is not a substitute for closure of the parent.

The saved survivor proposals continue to violate physical center-distance
or shared-frame conditions. For example, before the final chord layer,
one saved EH difference had squared norm about 0.00237, while its valid
box secant allowed an upper value about 2.366. This is a diagnostic of
the relaxation's missing strength. It is neither a feasible packing nor
a contradiction covering the entire original path.

## 5. Other preserved OPEN work

The separate fifteen-parent octagon checkpoint has a complete independent
partial replay of 457 bound deductions and 4,036 retained terminal leaves,
with 1,028 explicit pending paths. It closes zero original parents.

Two targeted continuations remain OPEN as well. Their final v3 records
have 503 proved leaves with 20 pending paths for
`negative-2f9ffd3df06e7c5f`, and 511 proved leaves with 43 pending paths
for `negative-573078fc944ce553`. All 1,014 retained leaves and both partial
unions passed fresh independent root replay. These are descendants of
the same two originals, not additional original cells or a reduction of
the external denominator. Earlier smaller-frontier records remain as
alternative checkpoints of the same domains.

The three negative573 static probes using the new path-difference rows
also remain OPEN. Their exact interval derivations are checked, but no
terminal contradiction was obtained. Further unchanged tree extension
is not represented as a completed proof.

## 6. Why a reduction to fewer originals is insufficient

The earlier selected-seven control already realizes every remaining
mask below Q. The new [eight-original hand control](EIGHT_ORIGINAL_ALL_WEAK_EXTRACTION_OBSTRUCTION.md)
shows a stronger limitation for a proposed global witness reduction:
eight aligned physical units fit strictly below Q, yet in every frame
every center-cone four-chain has all three main links weak. They cannot
be relabeled or rotated into `001/00` or the already closed outer-actual
family. Its squared-radius slack is the exact positive number
`917/2304`.

This control is not a nine-square counterexample. It proves that any
stronger-chain extraction bypassing the other masks must use the ninth
original essentially. The current `001/00` low-gap, vertical-order and
bottom-exclusion conclusions cannot simply be imported into the other
fixed mask predicates.

## 7. Evidence and remaining task

The [open continuation manifest](computer_assisted/a2_00100_open_continuation_manifest.json)
binds the research archives and separates each partial proof's scope
from the accepted whole-cell proofs. The new
[pair-support manifest](computer_assisted/a2_00100_pair_support_open_manifest.json)
identifies the complete sources, exact tables, portable replay entry
point, and the final partial-cover review. Discovery sources are retained
with their numerical conclusions labeled as such.

The exact remaining original families are still A=17, B=30, C=10 and D=6.
All 63 predicates in the [fixed register](gates/A2_00100_FIXED_FRONTIER.json)
need complete exclusions, or a proved theorem covering their union.
Only then can the accepted low-gap result and complete large-gap cover
close `001/00`, followed by its exact reversal `100/00`. The other 22
open masks still require complete original-nine arguments. None of this
continuation changes the historical positional-root ledger, the 15
roadmap IDs, or the unrestricted equality-classification obligation.
