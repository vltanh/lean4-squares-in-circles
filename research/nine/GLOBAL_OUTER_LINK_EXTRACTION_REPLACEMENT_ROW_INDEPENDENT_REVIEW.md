# Independent review of the near-horizontal replacement-row terminal

November 3, 2026. Complete independent mathematical review of
`WEAK_OUTER_NUMERIC_NEAR_HORIZONTAL_REPLACEMENT_ROW_HAND_TERMINAL.md`.
The new exact scalar checker was also replayed successfully. No Lean,
Lake, or CI was used.

**Accepted scope.** In the unchanged original strict `001/00` caller at
closed `Q=1105/256`, normalized with `y_D-y_C>=2/3`, no unchanged extra X
can satisfy

    x_B<=x_X<=x_D,
    |y_X-y_B|<=1/8,   |y_D-y_X|<=1/8.

The two new physical row links may both be weak and every original
orientation is retained. The same original-extra statement reverses
with the witness. This excludes a complete neighborhood and its equality
face; it does not close the complement or a whole mask.

## 1. Every physical pair and owner is covered

For a pair with positive horizontal gap d and vertical gap at most 1/8,
the contained radius-1/2 disks give `d>=sqrt(63)/8>1/8`. A physical owned
separator has components equal, up to signs and order, to its owner's
folded `alpha,beta`. A steep-axis upper bound
`beta*d+alpha/8` is no larger than `alpha*d+beta/8`; square support is
invariant under a quarter turn, so this comparison retains the same
actual support sum. It does not assert that the shallow axis itself
separates the pair.

The lower support estimate

    R>=1+alpha*|h_O-h_P|

has both required width orders. If the owner is wider, the complete
free-frame support inequality proves it. If the other square is wider,
its smaller coordinate j is no larger than the owner's j, and its
actual rightmost vertex gives the estimate. The identity
`alpha*h_owner-beta*j_owner=1/2` has the correct sign and constant.
Thus the physical horizontal-gap inequality holds for both owners,
both chiralities, and both of their possible separating axes.

## 2. The scalar payment covers the whole two-dimensional domain

The normalized toll is the maximum of two separately valid endpoint
tolls, not their sum. Their coefficients agree with the inherited
universal and sharp-small-angle cap theorems after division by 46.

For endpoint slope `t<=1/8`, q is decreasing on `[0,t]`, h is increasing,
and q+h is strictly increasing on `[0,1]`. The latter follows from the
displayed derivative identity and `A'>=1/(2sqrt(2))>1/8`. These facts
reduce both possible orders of the owner slope s and endpoint slope t
to `q(t)+T(t)/2`. Multiplication by the positive `64sqrt(1+t^2)` and
the elementary square-root upper bound give
`t+(23/2)t^2-4t^3`, positive for `0<t<=1/8`. At t=0, strict increase of
q+h gives equality only at s=0.

For `t>=1/8`, the global lower bound on q and the two endpoint toll
comparisons cover all of `[1/8,1]`. Concavity in the physical angle is
used only on the stated sharp-toll interval `[atan(1/8),atan(1/3)]`;
the universal branch covers the remainder. All comparisons are strict.
The exact replay verified squared reserves 188, 6,270,736, 773,606,
and 10,586. Consequently the complete payment inequality has equality
only when both its owner and endpoint slopes vanish.

## 3. Two links, width variation, and equality

The total width variation

    V=|h_B-h_X|+|h_X-h_D|+h_B-h_D

equals twice the sum of the two positive successive width decreases.
It is at least `2*(max(h_B,h_X,h_D)-h_D)`, and hence pays the sum of
the two chosen owners' positive excesses over h_D. Adding the two
scalar payments therefore proves the complete two-link inequality.

If equality holds, both scalar payments vanish. D and the two selected
owners are aligned, and the remaining width-variation term forces all
three widths to be 1/2 even if the same middle original owns both
separators. Thus B,X,D are all aligned. Their vertical differences are
less than one, so physical nonoverlap gives horizontal gaps at least
one, and equality in their sum makes both gaps exactly one. No equality
of the three heights is assumed.

The closed horizontal-order endpoints cause no missing case. If
`x_X=x_B` or `x_X=x_D`, the corresponding vertical difference is at
most 1/8, contradicting unit center distance. Every physically possible
point in the stated closed row region therefore has strict horizontal
order, as needed by the pair estimate.

## 4. The original strict bit closes the equality face

Actual AB and EFG make the weighted chain lower bound equal to the sum
of the two accepted endpoint-cap upper bounds. Equality is therefore
necessary throughout; a subcritical radius is impossible by the strict
ordinary cap. The aligned row conclusion makes its toll zero, so the
ordinary physical-cap equality theorem applies without any new equality
classification. G>D selects

    D=(3/2,-1/16),  G=(1,15/16),
    x_B=-1/2,      x_X=1/2.

Aligned X,G have horizontal gap 1/2. Their physical separation and the
row height bound force `y_X<=y_D`; the original transverse lower bound
also gives `y_X>y_C`. Actual BC implies `x_C>=h_C>=1/2`, and the original
CD cone gives `x_C<=5/6`. With `p=x_C-1/2`, the unchanged C,X centers
satisfy

    0<=p<=1/3,
    1<=|c_C-c_X|^2<=p^2+(1-p)^2.

The last upper bound is strictly less than one for p>0, so p=0.
Actual BC then forces h_C=1/2. The original CD horizontal gap is now
one, equal to h_C+h_D, contradicting precisely the retained strict
weak bit. This establishes a closed-Q exclusion, including the boundary
configuration that obstructs a uniform-reserve proof of the closed
weak-comparison relaxation.

## 5. Dependencies and finite-cover use

The proof uses the inherited ordinary cap and equality theorem, the
inherited universal and sharp endpoint tolls, original physical-pair
separation, original actual AB/BC/EF/FG comparisons, and completed
G-order. It does not use the C-slant theorem, the C-bottom exclusion,
the new actual C/G comparison, or the proposed F-order theorem. Its
dependency order is therefore acyclic.

The six closed escape alternatives in the manuscript cover the exact
complement of the excluded row region, including shared boundaries.
A finite proof may use them exhaustively, or apply the accepted
analytic terminal to a fully enclosed row cell. This review accepts
neither an unproved placement routing into that region nor an invented
strict Farkas reserve at an actual closed-weak equality point.

## 6. Positive-D total-variation extension: independently accepted

The later manuscript
`WEAK_OUTER_NUMERIC_POSITIVE_D_TOTAL_VARIATION_ROW_HAND_TERMINAL.md`
correctly proves the broader positive-D condition

    |y_X-y_B|+|y_D-y_X|<=1/2.

This statement retains every B and X chirality. Its signed D toll is
the normalized `sigma=alpha_D-1+(23/32)beta_D`, and the new two-link
transfer is valid over the complete original angle domain.

Each individual vertical gap is at most 1/2. The original unit center
distance gives a horizontal gap at least `sqrt(3)/2`, so the physical
owned support estimate and its steep-axis comparison apply. Taking
the largest of the two selected owner slopes makes the total vertical
loss at most half that slope, while the sum of the two nonnegative
secant surpluses retains at least the larger one. The same width
variation V pays twice the positive owner-width excess over D.

The resulting two-variable scalar bound is

    q(s)+2*(h(s)-h(t))_+ +sigma(t)>=0,
    q(s)=sqrt(1+s^2)-1-s/2.

The derivative of q+2h is strictly positive, and q has its unique
minimum at `1/sqrt(3)`. Splitting at s=t therefore gives precisely
`q(min(t,1/sqrt(3)))`. For the lower t interval, the displayed exact
decomposition into `(r-1)^2/r` and
`t*(23/(32r)-1/2)` is nonnegative, with strictness for t>0 because
`23^2-2*16^2=17`. For the remaining interval, sigma is unimodal and
its minimum is at an endpoint. The lower endpoint is already covered;
the t=1 endpoint has strict rational reserve greater than `27/448`.
The fresh exact arithmetic replay passed all three radical comparisons.

Equality in this complete scalar reduction requires the endpoint and
both selected owners to align. As before, zero remaining width
variation then forces B,X,D all to align even when one middle original
owns both separators. Both physical horizontal gaps equal one.

For its original caller, the signed-cap prerequisite is supplied by
both previously established facts `y_G>y_D` and

    -1459/1728 < x_G-x_D < 11/60.

Their horizontal absolute gap is strictly below one. Thus a unit
owned D/G normal with nonpositive vertical component would have center
projection less than the support sum, which is at least one. An
upward owned separator is therefore available for the unchanged pair;
height order alone is not being used as a replacement premise.

The weighted cap equality and the original C/X argument reviewed in
Section 4 apply with the larger per-link bound 1/2: it still gives
`y_X<y_G` and `y_X>y_C` since the original transverse lower bound is
2/3. The closed horizontal-order endpoints are again impossible by
unit center distance. Consequently the full closed total-variation
region is excluded for nonnegative D tilt, including its equality
face, even at closed Q.

This extension does not use the C-slant table, the F-order table, or
either new boundary contraction certificate. It does not assert the
corresponding negative-D extension or a whole-mask closure.
