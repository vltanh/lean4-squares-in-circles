# Root review: the refined long/diagonal angular budget

Date: October 30, 2026 UTC.

**Verdict: PASS for the complete source and every stated family join.**

| Source | SHA256 |
| --- | --- |
| SHARP_LONG_AND_DIAGONAL_RUN_ANGLE_BUDGET_2026_10_30.md | `614382093c6c976e7767855c5234419fe3a3c477bafc8c4465e46d86446e56fc` |
| TWO_ENDPOINT_EXPANDED_SQUARE_COVER_AND_LONG_CHANNEL_TRIANGLE_EXCLUSION_2026_10_30.md | `78dfc5ed83b1538b2484007fc6d60d047c078b7f124944c0aef4dce6593558f6` |
| UNIFORM_MARKED_CYCLE_ANGULAR_BUDGET_AND_NINE_BODY_CYCLE_EXCLUSION_2026_10_30.md | `b5d9f55141ca2ab2c4f4195de68a714340fa2de607b8b9e81bb484578e4b16be` |

I read the entire new source. Both complete direct inputs already have
full root and separate independent reviews at the exact frozen versions
above.

## 1. The long-gap angle exceeds 175 degrees

The coupled endpoint estimate is used literally: the absolute horizontal
center coordinates exceed 89/60 and the sum of absolute transverse
coordinates is at most 1/8. The deficit from antipodality is at most
the sum of the two absolute endpoint deviations. Bounding their
arctangents by their arguments gives a strict upper bound 15/178.
The source also handles both transverse coordinates zero, where the
same strict upper bound remains valid.

Its exact comparison with five degrees is correct: sin(pi/12)<pi/12,
sqrt(6)>22/9 and sqrt(2)<10/7 give pi>64/21. Hence

    pi/36>16/189>15/178,
    16/189-15/178=13/33642>0.

This proves the minor angle exceeds 175 degrees for both transverse
sign patterns. The geometric lemma requires neither boundary endpoints
nor force or torque balance; an actual gap-two pair suffices.

## 2. A diagonal-width support gap exceeds 105 degrees

Reserve sqrt(2), plus the endpoint halfwidths, gives center distance
at least 1+sqrt(2). If the minor angle were at most 105 degrees, its
cosine would be greater than -13/50. I checked the positive-squaring
comparisons sqrt(6)<49/20 and sqrt(2)>141/100, whose difference is
less than 26/25. The center bound then gives squared distance below

    (63/25)(91/60)^2=57967/10000
      =29/5-33/10000<3+2sqrt(2).

The last inequality follows from sqrt(2)>7/5 and contradicts the
support-derived distance. The endpoints are nonzero because this
required distance exceeds the universal center radius.

## 3. The complete cycle sum gives the claimed integer theorem

The unchanged marked-cycle hypotheses supply actual center order and
the full-turn angular sum. Direct runs, other singleton runs, diagonal
singleton runs and long runs have strict angular lower bounds of forty,
eighty, one hundred five and one hundred seventy-five degrees. With
m=k_0+2k_s+2d+3ell this gives

    40m+25d+55ell<360,
    8m+5d+11ell<=71.

The second inequality uses integrality. Each actual directed gap is
at least its minor endpoint angle, including when it is the major arc.
No force polygon or new origin-containment assertion is introduced.

For m=7, ell=1 and d>=1, the integer left side is at least 72.
Therefore every seven-body marked cycle with a long run has no diagonal
singleton run. Both four-mark cyclic orbits (2,1,0,0) and (2,0,1,0)
lose their entire diagonal-short domains at once. The side-short record
has d=0 and remains allowed. For m=8 the base theorem gives ell=0,
and the refinement gives d<=1 across all counts and placements of marks,
including the remaining four-load alternating family.

## 4. Moment balance is used only for the discrete width interpretation

The geometric theorem counts an actual width-sqrt(2) run. Its physical
caller correctly adds the actual moment equation before classifying
an unloaded true-degree-two singleton. Opposite forces cancel, their
actual mean difference is parallel to the normal, and the support
equation fixes that difference to the actual width times the normal.
One zero own-axis normal component gives side width one and equal
transverse means. Two nonzero components give opposite exposed vertices,
hence equal absolute components and width sqrt(2).

The full-degree condition includes every positive contact of the body.
No endpoint force is removed; actual shared-side endpoint means and
physical circle masks are retained. A merely translational caller is
not assigned this classification without an independently established
width. The drawing, full degrees and moment equations must refer to
one retained certificate in the physical caller.

## 5. Verification and limits

All rational identities and positive radical comparisons were checked
exactly. The complete long-height and annular-order inputs are already
fully reviewed. This source does not close the side-short seven-body
families, every eight-body cycle, chorded parents, equality classification
or unrestricted optimality. No Lean build, CI, numerical pose search,
mesh, original ledger mutation or certificate substitution was used.
