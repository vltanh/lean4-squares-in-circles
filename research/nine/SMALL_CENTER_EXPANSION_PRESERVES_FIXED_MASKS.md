# Small common center expansion preserves the fixed mask and outsider columns

November 2, 2026. Complete hand normalization lemma, independently
reviewed. No Lean or CI. This lemma changes no quantified domain,
fixed-mask definition, or positional-root count.

## 1. Statement

Suppose nine original physical unit squares form a strict counterexample:
every one of their 36 original corners has squared norm strictly below
`Q=1105/256`, and all original pairs have disjoint open interiors. Retain
the fixed orthonormal witness frame, original labels, five selected cone
links, and all five actual/weak bit predicates.

There exists a common center multiplier `lambda>1`, arbitrarily close
to one, with all the following properties:

- Every expanded original corner still has squared norm strictly below Q.
- The nine expanded closed squares are pairwise disjoint.
- Every selected cone comparison and every actual/weak bit is preserved.
- Every outsider retains its left/central/right column relative to
  `l=29/60`, and every relative center-height order is preserved.
- If the main four-chain is actual, its expanded adjusted endpoint span
  is strictly greater than two.

Every original frame is retained. Only the centers are multiplied by
the same positive scalar about the existing circle center.

## 2. Choose one multiplier satisfying all finite constraints

Write each original corner as `ci+vij`, where ci is its center and vij
is its fixed frame-dependent corner offset. Its expanded squared norm
`|lambda*ci+vij|^2` is continuous in lambda. Since all 36 original
values are strictly below Q, a single interval `1<=lambda<1+epsilon`
keeps every corner strictly below Q.

For each weak selected link, let d be its positive horizontal center
gap and H the sum of the two original physical horizontal halfwidths.
Its exact bit says `d<H`. Require additionally `lambda<H/d`, a strict
upper bound larger than one. For each originally central outsider with
nonzero horizontal coordinate x, require `lambda<l/|x|`; this too is
a strict upper bound larger than one. There are finitely many such
requirements. Choose any lambda strictly between one and their minimum,
also satisfying the corner-containment interval. A zero horizontal
coordinate needs no extra restriction.

## 3. Original pairs and selected chains

For each original pair choose one genuine separating unit normal n.
The unchanged original support sum sigma is positive; indeed each unit
contains its centered radius-one-half disk, so `sigma>=1`. Orient n
so the original separation says

`n dot (cj-ci) >= sigma`.

After the common expansion,

`n dot (lambda*cj-lambda*ci) >= lambda*sigma > sigma`.

Thus the same original owner axis strictly separates the two expanded
closed squares. This argument applies separately to all 36 original
pairs and does not require a common separator choice or contact graph.

Each selected cone inequality `|yj-yi|<=xj-xi` is preserved because
both coordinate differences are multiplied by lambda. An actual bit
`d>=H` remains actual, and even becomes strict. Every weak bit remains
weak by the multiplier bound in Section 2. No bit is silently changed
during normalization.

## 4. Columns, height orders, and adjusted endpoint span

An original right-side coordinate `x>=l` remains on that side under
positive expansion; likewise an original left-side coordinate `x<=-l`
remains left. The finite central-coordinate restrictions preserve all
strict central inequalities. All relative center-height orders are
preserved because their differences are multiplied by the same positive
lambda. These observations include the side boundaries `x=+/-l` and
the central coordinate x=0.

For an actual four-chain, summing its three original projection gaps
gives

`D0=x3-x0-h0-h3 >= 2h1+2h2 >= 2`.

Its expanded adjusted span is

`Dlambda=lambda*D0+(lambda-1)(h0+h3)>D0>=2`.

All frames and therefore all halfwidths are unchanged.

## 5. Why the side-marker and occupancy callers apply

The marker capture theorem in Sections 1--5 of
`UNRESTRICTED_ACTUAL_FOUR_CHAIN_SIDE_CAPACITY_HAND_PROOF.md` assumes
only containment in the closed Q-disk and the original physical
nonoverlap predicates. Its marker-order argument additionally uses
closed-square disjointness. The small expansion supplies all these
hypotheses. Neither argument needs an attained corner at squared norm Q.
Thus marker capacity, the full-side marker order, and the established
actual-four coordinate bounds all apply to this expanded configuration.

The completed occupancy callers use exactly closed-Q containment,
strict separation of closed original squares, retained actual/cone
comparisons, their stated column counts and height orders, and the
adjusted span `D>2`. The earlier description of expansion all the way
to a Q-contact can therefore be replaced by this small expansion in
the fixed-mask assembly. No subsequent inequality in those callers
uses attainment of the outer circle.

This permits the full `000/11` proof to classify the expanded outsiders
without losing either weak selected short link or an original column.
It also applies to the other fixed masks as a normalization statement;
it supplies none of their missing terminal contradictions.

## 6. Scope boundary

This is a strict-radius lemma. At closed Q the necessary corner
continuity margin may be zero, and no such expansion is asserted.
It does not preserve a particular historical hexagonal positional root
and does not discharge or reclassify any of the 7,915 stable root IDs.
The original fixed-mask cover and all physical hypotheses are unchanged.
