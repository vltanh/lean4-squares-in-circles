# Three boundary returns force a high middle unit and a full unit section

**Date:** October 30, 2026 UTC.
**Status:** complete proposed force-free structural and section lemmas,
awaiting independent full review. No completion or whole-cycle closure
is claimed by these lemmas alone.

Put `Q=1105/256`, `M=91/60`, and `z=5/4`.
All units below are actual closed squares with pairwise disjoint open
interiors in the same unchanged centered disk.

## 1. Every unit above height 3/8 has a section of length at least one

**Theorem 1 (whole-section width).** Let an actual unit S be contained
in `D_Q` and wholly above the line `y=3/8`. Its full horizontal
section at `y=z` is nondegenerate, has length at least one, and has
length strictly greater than one unless S is axis aligned.

The boundary convention is closed: `S subset {y>=3/8}` suffices.
No circle contact, force, graph, second unit, or separating direction
is required.

Choose a signed side description with absolute tilt coefficients
`a>=b>=0`, `a^2+b^2=1`. Write its center height as y, and put

    h=(a+b)/2, w=a+b, delta=z-y.

The top height is at least `3/8+w>=11/8>z`. The bottom height
is at most `sqrt(Q)-w<=sqrt(Q)-1<9/8<z`. Thus the section lies
strictly between the horizontal supporting lines.

The floor and circle top bound give

    delta<=7/8-h,
    delta>h-7/8,
    |delta|<=7/8-h.                                  (1)

The first inequality may be equality at the closed floor, and no
strict claim at that endpoint is needed. If b=0, the full section
has length exactly one. If b>0, solving the original four side
inequalities, in either sign of tilt, gives the exact width

    W=min(1/a,(h-|delta|)/(a*b)).                      (2)

For example, in the central band `|delta|<=(a-b)/2` the two
opposite-side intersections have separation `1/a`; outside it the
two adjacent-side intersections have separation `(h-|delta|)/(ab)`.
The two expressions agree at the band boundary, so (2) includes all
sections.

We have `1/a>1`. Also

    h-|delta|>=w-7/8,
    w-ab=w-(w^2-1)/2>=sqrt(2)-1/2>7/8.               (3)

The middle function decreases for `1<=w<=sqrt(2)`, and the last
comparison follows from `sqrt(2)>11/8`. Hence the second expression
in (2) also exceeds one. This proves the entire theorem.

## 2. Three physical boundary returns on one side of a long pair

Suppose `2<=R<=sqrt(Q)` and A,B are actual physical-boundary units
with a signed support gap at least two in the x direction. Let
at least three other physical-boundary units lie wholly in `y>0`.
No graph or stress premise is imposed in this section.

**Theorem 2 (middle-return localization).** There are at most three
such above-side boundary units. When there are three, call them
`T_1,T_2,T_3` in increasing center-angle order. Then the entire
actual middle unit T_2 lies in

    y>83/160>1/2.                                    (4)

Its section at `y=5/4` has length at least one, strictly greater
than one for a nonzero tilt. Moreover the closed disk of radius
`1/40` centered at `P=(0,5/4)` lies in its open interior.

The force-free long-gap bounds give endpoint center directions within
five degrees of the signed x axes. They also give `|c_i|<M` for
every actual unit center. The endpoint angular estimate is proved
in Section 2 of the frozen return-side source using only the actual
support gap and coupled endpoint-height budget; no embedded-cycle
order is needed for that estimate.

Every two physical-boundary units have center-angle separation
strictly greater than forty degrees throughout this radius window.
This follows from the closed centered forty-degree inner arc lying
in each actual open square, as proved in `CENTERED_INNER_ARC.md`.
It is a physical boundary statement, independent of selected loads.

Every above-side center has angle in `(0,180 degrees)`. Its separation
from A,B therefore puts its angle in `(35,145 degrees)`. Four such
angles would span more than 120 degrees between the first and fourth,
inside an interval of width 110 degrees, which is impossible. Thus
there are at most three. With three, the middle angle theta satisfies

    75 degrees<theta<105 degrees.                    (5)

The middle center radius r obeys

    r>=R-1/sqrt(2)>31/24,
    r<M.                                             (6)

Here `R>=2` and `1/sqrt(2)<17/24` supply the strict lower bound.
Since `sin(75 degrees)>19/20`, its center height exceeds
`(31/24)(19/20)=589/480`. The vertical halfwidth of any actual
unit is at most `1/sqrt(2)<17/24`. Subtraction gives

    min_(p in T_2) p_y>589/480-17/24=83/160,

proving (4). Theorem 1 applies immediately to this actual unit.

## 3. A fixed disk inside the actual middle unit

The slightly stronger elementary bound

    sin(75 degrees)>24/25

is useful. One exact check is
`sin(75 degrees)^2=(2+sqrt(3))/4>37/40>(24/25)^2`,
using `sqrt(3)>17/10`.

For P=(0,5/4), equations (5),(6) give

    |c_(T_2)-P|^2
      =r^2+25/16-(5/2)r*sin(theta)
      <r^2+25/16-(12/5)r.                             (7)

The last quadratic is convex in r. Its endpoint values on the
enlarged closed interval `[31/24,91/60]` are

    377/2880, 401/1800.

Therefore

    |c_(T_2)-P|^2<401/1800<(19/40)^2,
    (19/40)^2-401/1800=41/14400>0.                    (8)

The actual unit contains its open incircle of radius one half.
Every point in the closed radius-1/40 disk about P is strictly less
than `19/40+1/40=1/2` from the middle center. This proves the
stated fixed-disk inclusion in the open original unit.

The simpler fact `P in int(T_2)` also follows directly from its
centered inner arc, because (5) puts its center angle within fifteen
degrees of the upward direction. Equation (8) gives a quantitative
two-dimensional margin rather than just the single point.

## 4. Literal long-channel use and the still-needed completion implication

A genuine four-body long channel with two unloaded full-degree-two
internal bodies supplies a support gap at least two. Its original
force and angular equations give a line containing two occupied points
four units apart; hence `R>=2`. Its endpoints are physically boundary
whenever the proved positive-long-endpoint theorem is invoked.
Thus a packing with three other actual boundary squares wholly on
the same above side meets every hypothesis of Theorem 2.

All nine physical units remain in a nine-body application. The theorem
does not require the three above-side units to be a selected path or
to carry positive circle coefficients. It does not infer that the two
outer returns have set distance at least one. A unit-length section
of the middle square does give a unit section gap between those outer
returns **if** their actual sections exist and the middle section is
proved to lie between them; that ordering is a separate geometric
obligation. Neither graph order nor center order is silently substituted
for the order of sections on the horizontal line.

These lemmas therefore provide a high actual middle unit, a fixed
occupied disk, and a full unit section for the remaining all-completion
analysis. They are not by themselves a seven- or nine-body exclusion.

## 5. Frozen inputs and verification boundary

- `CENTERED_INNER_ARC.md`, SHA256
  `fac240eca4ad3254ba4aafd8c915f9771f7eeb3acea57bd2ee3ddd4eab0ba2e5`:
  entire centered open-square arc and physical forty-degree separation.
- `LONG_RUN_RETURN_MARKS_WHOLE_SIDE_CLEARANCE_AND_SHORT_NORMAL_CONE_2026_10_30.md`,
  SHA256 `c10361ea546b8e5681b4ac38c09b1b2e9b14fa0a2621c541f689857c73acbd1e`:
  Section 2 actual long-gap endpoint bounds only; its plane-cycle order
  theorem is not invoked here.
- `TWO_ENDPOINT_EXPANDED_SQUARE_COVER_AND_LONG_CHANNEL_TRIANGLE_EXCLUSION_2026_10_30.md`,
  SHA256 `78dfc5ed83b1538b2484007fc6d60d047c078b7f124944c0aef4dce6593558f6`:
  the underlying force-free center and coupled-height estimates.

All section formulas, angular intervals, inequalities and disk margins
are continuous and exact. No numerical pose search, original certificate
change, discarded unit, ledger mutation, Lean compilation, CI execution
or remote publication is used.
