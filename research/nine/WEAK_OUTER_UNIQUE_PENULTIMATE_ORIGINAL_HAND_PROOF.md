# A weak right endpoint has a unique penultimate original

November 3, 2026. Complete hand consequence of already accepted whole-domain
results. This theorem targets the unchanged `001/00` frontier. It does not
by itself close a whole mask or change a fixed-cell status. No Lean, Lake,
or CI.

## 1. Caller and dependencies

Let nine independently oriented physical unit squares lie in a disk of
squared radius `q<Q=1105/256`, with their interiors pairwise disjoint. Retain
the exact original `001/00` witness: main chain A,B,C,D; short chain E,F,G;
all five center-cone comparisons; actual AB, BC, EF, FG; and strictly weak
CD. Every unused original and all of its physical constraints remain.

Normalize the common vertical coordinate so that `y_D-y_C>0`. The accepted
complete low-gap theorem then gives `y_D-y_C>2/3`.

We use only these completed inputs, with their unchanged scopes:

1. `WEAK_OUTER_LOW_GAP_HAND_TABLE_ASSEMBLY.md`: every original `001/00`
   witness satisfies `|y_D-y_C|>2/3`, for all physical tilt signs.
2. `WEAK_OUTER_LARGE_GAP_SHORT_ENDPOINT_ORDER_HAND_TABLE.md`, Section 1:
   after normalizing `y_D-y_C>=7/30`, its original right short endpoint
   satisfies `y_G>y_D`. This holds at closed Q, uses all tilt signs, and
   imposes no condition on the two omitted originals.
3. `GLOBAL_OUTER_LINK_EXTRACTION_DG_INSET_AND_SLANT_HAND_REDUCTION.md`,
   Sections 2-3, together with the completed C-slant table reviewed in
   `GLOBAL_OUTER_LINK_EXTRACTION_C_SLANT_INDEPENDENT_REVIEW.md`: on the
   normalized gap `y_D-y_C>=2/3`, one has `x_C>29/60` and no other original
   X can have both `x_X>=0` and `y_X<=y_C`. We call this the **bottom
   exclusion**. Its proof concerns every other physical original, not just
   either of the two omitted labels. The same source gives `x_C<4/5`.
4. `A2_COVERAGE_AND_CLOSURE_CONTRACT.md`, Sections 3 and 5: an actual
   `000/00` four-plus-three witness is impossible for `q<Q` by the completed
   physical cap theorem. This input is only used with its strict-radius
   conclusion.
5. The original physical inset and center-radius facts: each square has
   coordinate halfwidth `h` in `[1/2,1/sqrt(2)]`, contains the concentric
   aligned square of halfwidth `g=1/(4h)>=1/(2sqrt(2))`, and every center
   has norm less than `rho=91/60`. For a physical center-cone pair i,j,
   `x_j-x_i>=g_i+g_j`.

These sources precede this argument and do not use the new uniqueness
claim. Their finite tables are reused as established theorems; no unchanged
large table is represented as freshly replayed here.

## 2. General uniqueness theorem

**Theorem.** Suppose the same nine originals admit another four-chain

    A' <_x B' <_x X <_x D

of distinct original centers, disjoint from the same E,F,G, where each of
its three links i,j satisfies `x_j-x_i>=|y_j-y_i|`, and with the first
two links A'B' and B'X actually separated by their full horizontal
projections. Then **X=C**.

The original names A' and B' can be any of the other originals consistent
with those distinctness conditions. They need not be A and B. No new
physical square, orientation, contact, or cone comparison is invented.

**Proof.** If XD is actual, these four originals and the unchanged actual
short chain E,F,G form the full `000/00` witness. The strict-radius sharp
cap theorem excludes it. Hence XD is strictly weak.

Consequently A',B',X,D;E,F,G form an exact original-nine `001/00` witness:
the first two and both short links are actual, the last main link is
strictly weak, and all five center cones are among the stated hypotheses.
The other two originals remain physical members of the same packing.
The complete low-gap theorem, applied to this witness, gives

    |y_D-y_X|>2/3.                                      (1)

The original witness and the G-order theorem give `y_G>y_D`. If X were
above D, reflect the entire configuration in the horizontal coordinate
axis, so `y'=-y`. The new witness now has

    y'_D-y'_X=y_X-y_D>2/3.

Every original physical square and every pair remains; the center cones,
horizontal halfwidths and exact actual/weak bits are preserved. The
G-order theorem for this reflected new witness would give
`y'_G>y'_D`, namely `y_G<y_D`. This contradicts the order from the original
witness. Therefore the only possibility in (1) is

    y_D-y_X>2/3.                                       (2)

The same horizontal localization and bottom exclusion now apply to the
new witness in the original coordinate frame. In particular `x_X>29/60`,
and no original distinct from X with nonnegative horizontal coordinate
may lie at or below X.

Suppose X differs from C. Since `x_X>0`, the original bottom exclusion
at C gives `y_X>y_C`. Since `x_C>0`, the new bottom exclusion at X gives
`y_C>y_X`. These inequalities contradict one another. Thus X=C.

Every possible XD status and transverse sign was covered, including the
projection equality XD: equality is assigned to the actual bit and was
excluded in the first paragraph. No positive separation margin from that
boundary is assumed. QED.

**Scope.** The theorem is a strict-radius result because its XD-actual
branch invokes the strict `000/00` terminal. No closed-Q exclusion or
new equality classification is asserted. The reflected G-order input has
no D-tilt or omitted-original restriction, so the common reflection is
legitimate on its entire caller.

## 3. Linear consequences for the named hard parent

Take an original X distinct from C, with A,B,X,D a center-cone four-chain
and disjoint from E,F,G. The original AB bit is actual. If BX were actual,
Section 2 would force X=C. Therefore

    x_X-x_B < h_B+h_X.                                 (3)

This is a strict necessary inequality on the complete stated caller. It
requires no height placement or ordering of the other extra original.
For example it applies to X=H throughout the immutable original cell
`positive-2c719a20ef7510de`: the `alternate_four_escape(1,7)` child 7
retains all six A,B,H,D cone inequalities. The following escape for I
changes none of those premises. In particular (3) applies before the
four-way H/I proxy split, and hence on all its descendants.

More generally an `alternate_four_escape(1,X)` child numbered 6 or 7
retains the same six cone rows; AB is already actual in the root caller.
Either child therefore permits (3). Any application outside that syntax
must establish the actual cone premises explicitly.

## 4. C and X must separate vertically by their original insets

Retain the caller of Section 3. Actual BC and (3) imply

    x_X-x_C < h_X-h_C
              <= 1/sqrt(2)-1/2
              < 1/sqrt(2) <= g_C+g_X.                  (4)

The original universal center bound and actual AB give
`x_B> -rho+1=-31/60`. The BX cone and physical inset separation give

    x_X>=x_B+g_B+g_X > -31/60+1/sqrt(2)>0.              (5)

For the other direction, use `x_C<4/5` and the same BX inset inequality:

    x_C-x_X < 79/60-g_B-g_X < g_C+g_X.                 (6)

The last strict comparison holds because

    g_B+g_C+2g_X >= sqrt(2) > 79/60.

Together (4) and (6) prove strict overlap of the two original aligned
insets' horizontal interiors. Those inset interiors are contained in the
pairwise disjoint original interiors, so their vertical intervals must
separate. By (5), the original bottom exclusion at C rules out
`y_X<=y_C`; hence the sign of that vertical separation is fixed:

    y_X-y_C >= g_C+g_X.                                (7)

For the HI-up child, (7) with X=H combines with its original H/I proxy
inequality to give the additional, redundant telescoped consequence

    y_I-y_C >= g_C+2g_H+g_I.

Equation (7) itself does not require that HI-up child.

## 5. Exact scalar checks and checker rows

The only new numerical comparisons in Section 4 are

    1/2-(31/60)^2 = 839/3600 >0,
    2-(79/60)^2   = 959/3600 >0.

All quantities being compared are positive. These verify the two radical
comparisons by squaring. The displayed inset inequalities are universal
identities from `g=1/(4h)`, not sampled angle estimates.

In the frozen v14 variable convention, `AL(i)=alpha_i`, `AB(i)=|beta_i|`,
`GI(i)=g_i`, and `2h_i=AL(i)+AB(i)`. For X=H (label 7), the following
closed necessary rows follow from (3) and (7):

    x_H-x_B -(AL(B)+AB(B)+AL(H)+AB(H))/2 <= 0,
    y_C-y_H +GI(C)+GI(H) <= 0.

The first row comes from a strict original inequality; relaxing it to
`<=` is sufficient for positive-reserve row-sum certificates. A checker
that uses its strictness at zero reserve must separately verify that
terminal rule. Neither row may be applied when the A,B,H,D cone guard
has not been derived.

A complete fixed original-cell proof must still provide its full split
cover and exact contradiction at every retained terminal. This reusable
geometric consequence earns no original-cell or mask closure without
that complete parent proof. No new mandatory roadmap gate is introduced.
