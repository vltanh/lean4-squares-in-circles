# Independent review of the weak-outer signed low-gap arguments

November 2, 2026. Mathematical review of the delivered source arguments.
No Lean, Lake, or CI. This review accepts the stated conditional theorems;
it does not close either full fixed mask.

## Sources reviewed

- `WEAK_OUTER_SIGNED_SMALL_GAP_TRANSFER.md`.
- `WEAK_OUTER_NUMERIC_NEGATIVE_TILT_LOW_GAP_HAND_EXCLUSION.md`.
- The independent signed-cap derivation in
  `SIGNED_NEGATIVE_MAIN_UPWARD_SEPARATOR_CAP_INDEPENDENT_PROOF.md`.
- `WEAK_OUTER_LOW_GAP_HAND_TABLE_ASSEMBLY.md`, including the complete
  three-row union and its explicit dependency order.
- `WEAK_OUTER_POSITIVE_TILT_TWO_THIRDS_HAND_TRANSFER.md`.
- `WEAK_OUTER_NUMERIC_NEGATIVE_TILT_TWO_THIRDS_HAND_EXCLUSION.md`.

## Signed transfer and its physical caller: accepted

The C,D transfer includes both physical owners, both signs of the normal,
all steep upward normals, and the aligned-D boundary. The free-C support
minimum is valid on the entire normal range. A downward normal with slope
at least one is excluded by d<sqrt(2), while an upward normal is retained
for every slope. The positive-D support formula is correct on both sides
of beta/alpha; its downward-chirality lower bound is used only on t<1,
where it is valid.

The reduction to t=0, beta/alpha, and 1 follows from concavity up to one
and strict increase thereafter. The half-angle polynomial is exactly
64z^3-43z^2+3. Its derivative has the asserted sign, and its endpoint
reserve follows from 2*203^2-287^2=49. The final slope-one value reduces
to 119/(32sqrt(2))-21/8, with squared reserve 49. Strictness at beta=0
uses the exact weak bit to exclude a horizontal physical separator.

The unconditional bound |x_D-x_G|<1 is correctly derived from the original
left endpoint cap and the two actual chains. In particular, the cap
implies a(x_C-h_C)+b(x_G-h_G)>=b/2, and the identity in h_D gives
x_D-x_G<1459/1728. The other direction follows from x_D>4/3.
If y_G>y_D, a usable separator with nonpositive vertical component would
have projection less than one; this contradicts the sum of its physical
supports. Thus the upward-separator premise of the stronger signed cap
is derived, rather than inferred merely from center height order.

The final cap sum is legitimate: the four endpoint squares are distinct,
the original positive D chirality becomes negative after the stated
horizontal coordinate reflection, and the actual outer spans produce
a strict lower bound exceeding 2a+b=2T. The manuscript explicitly retains
y_G>y_D until a separate complete argument supplies it.

## Nonpositive-D-tilt low-gap theorem: accepted

The bound d+h_C+h_D<2011/960 follows from the two actual main links,
the left center-radius estimate, and the true right-square support.
For every usable owned separator, its owner's exact support and the other
square's free-frame support lower bound give the stated J(phi).
The derivative

    J'(phi)=(sin(phi)^3+cos(phi)^3-5/8)/cos(phi)^2

is positive over the entire quadrant. The exact comparison at tan(phi)=1/3
therefore proves |n_y|/n_x<1/3 for every usable physical normal, with
neither owner nor sign omitted.

For upward normals, the negative-D support is exactly ch+sk on this
derived slope range. The concavity chord A(t)>=1+9t/20 is valid. Both
k ranges are covered, and the uniform bound
k+(6/23)beta>=6/(23sqrt(2))>7/40 supplies strict reserve in the small-k
range. The beta=0 case is strict because the weak bit forces t>0.

For downward normals, the local vertical reflection preserves the original
physical pair, changes D to positive chirality, and changes its transverse
displacement to -v<=0. Replacing that displacement by zero weakens the
inequality. The endpoint values 1,1/alpha,sqrt(2)+k cover the resulting
whole interval, including the aligned face.

The universal four-beta right cap and ordinary left cap then exclude this
entire nonpositive-D-tilt, v<=5/8 subdomain even at closed Q. No G,D height
premise or constraint on the two unselected originals was inserted.

## Complete low-gap assembly: accepted

The assembled theorem correctly combines the inherited [0,7/30] result,
the nonpositive-D argument, and the positive-D argument with the independent
G-order theorem on [7/30,5/8]. The common vertical reflection preserves
every original square and every exact marked bit. The two closed folded
chirality ranges cover all original D orientations, including the aligned
and diagonal boundary representations. Both shared transverse endpoints
are retained, and the positive-D cap sum is strict because the original
weak bit makes its transfer strict even at beta=0.

The dependencies are acyclic. The signed cap is proved from physical
support and the inherited cap, the positive transfer is proved without
G-order, and the horizontal endpoint localization uses only the ordinary
left cap and actual-chain consequences. The G-order forest uses that
localization and the original C,D,G physical constraints; it does not use
the assembled low-gap conclusion or the stronger signed cap. Only then
does the assembly invoke G-order to supply the signed cap's upward-normal
premise. Its four endpoint witnesses remain distinct originals.

The printed finite-evidence totals agree with both complete exact replay
reports: 62,297 nodes, 34,752 leaves, 26,145 angle splits, 1,400 separator
splits, depth 18, empty frontier, and positive reserve exceeding
608951/10^12. The certificate hash agrees in the two reports and in the
five rejected damaged-certificate controls. This review checked those
records; it does not claim a third arithmetic replay of that unchanged
forest.

The assembled conclusion |y_D-y_C|>5/8 is therefore accepted even at
closed Q, as is its exact simultaneous reversal for 100/00. It is a
complete continuous subdomain exclusion. The larger-gap original-nine
complement remains open, so no whole-mask or positional-root count changes.

## Complete two-thirds extension: accepted

The two later manuscripts extend the same original physical caller to
the full closed transverse interval `0<=v<=2/3`. This supersedes the
5/8 cutoff above, without changing any square, frame, comparison, or bit.

For positive D tilt, the original span bound and the increasing J_V
function give `t<1/3` for every usable owned normal, with squared reserve
765110. Both vertical signs remain covered: on this derived range the
downward D support is at least the upward support used in the transfer.
The exact identity for A'' shows that A' has global minimum
`1/(2sqrt(2))` at t=1, so F_+ is increasing for V=2/3. Concavity of F_-
on `[0,1/3]` leaves only zero and `min(t_D,1/3)`.

If `t_D<=1/3`, the kink surplus factors as beta/alpha times
`(23/32)alpha+z(1-alpha)-2/3`; alpha>=3/sqrt(10) makes it strictly
positive with squared reserve 1889. If `t_D>=1/3`, the endpoint surplus
is the stated positive cosine-sine combination plus a constant, so its
minimum is at an angular endpoint. Both displayed endpoint comparisons
are positive. Beta=0 is handled separately: the exact weak bit excludes
t=0, and the increasing F_+ gives strictness for every remaining normal.

For nonpositive D tilt, the stronger normal cutoff `t<13/40` follows
from the same J function, with squared reserve 1121887. On that entire
range the upward support is exactly `ch+sk`. The endpoint contribution
`(13/80)alpha-(139/1840)beta` decreases with beta and has minimum
sqrt(2)/23. The two rational radical comparisons then give the strict
F(13/40) surplus `6869/15788580`. Concavity, together with the weak bit's
exclusion of a horizontal separator, proves strict transfer even when
beta=0. The downward reflection has favorable transverse displacement;
weakening it to zero gives the complete endpoint list
`1,1/alpha,sqrt(2)+k`. Positive beta supplies strict toll, and the
aligned case is strictly increasing away from t=0.

The cap caller is unchanged. The positive branch uses the already
complete G-order theorem only on `[7/30,2/3]`; the inherited small-gap
result handles `[0,7/30]`. The nonpositive branch needs no G-height
premise. These two extensions do not use the C-bottom theorem, the
slanted halfplane, or the new D/G inset clearance. The dependency order
therefore remains acyclic.

Together they exclude the full original `001/00` domain with
`|y_D-y_C|<=2/3`, even at closed Q, and simultaneously reversed `100/00`.
This is a complete continuous subdomain exclusion; the full masks remain
open on the larger-gap complement.

## Exact current scope

The individual positive-D caller carries its stated vertical-order premise;
the complete assembly supplies that premise using the accepted G-order
forest. With the two-thirds extension, these arguments do not settle the
v>2/3 complement, prove a whole fixed-mask closure, classify
equality, or modify the 32-mask or positional-root accounting. The separate
signed-cap proof checks all orientation endpoints, including the aligned
M-owned normal n=(1,0), which is not in the two unaligned owner arcs.
