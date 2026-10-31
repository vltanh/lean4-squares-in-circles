# Independent audit: orientation of the moment at an actual boundary contact

Date: October 28, 2026. Reviewer: triangle_bridges, separately from
author hexagon and the root reviewer.

**Decision: ACCEPT the complete force-free local theorem, without
correction.** It holds at the entire declared radius window, for
arbitrary actual degrees, support owners and common-side means.
This is a sign theorem and is not a whole original-family exclusion.

## 1. Exact complete source and imported scopes

I read and independently rederived all of
`BOUNDARY_CONTACT_ORIGIN_MOMENT_ORIENTATION.md`, SHA-256

`851417d7fcd12ccb93a6f7f09ba7d7b2bf9bccc61c82fee3457b5ee4cee47e9a`.

I also reread the complete physical center-annulus, pair-gap and
touching-pair angular arguments in Sections 1--3 of
`CIRCLE_CONTACT_ANGULAR_ORDER.md`,
`2625b3a2b730525a6397bc90232e78c5e1aac8091381c1f5e5fc8a71ef1da449`,
and the full one-square corner/resultant calculation in Section 1 of
`FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md`,
`6c38d162e1f2c435cf65a8b4a58a7001fe9489c65b3510159fee2687b9753708`.
Both current full-file pins match. The latter section is a physical
one-square fact; its later four-body force-sum and path premises are
not used here.

The physical pair has center minor gap strictly between pi/5 and
2pi/5. The lower bound needs only the two actual center radii in
(5/4,61/40) and center distance at least one; the upper bound uses
actual contact and center distance at most sqrt(2). I checked the
rectangle maxima and the strict upper-gap comparison in the original
proof. No positive circle multiplier is needed for these physical
statements.

For a circle corner z=(a,b), a>=b>=1/2, its own center is
(a-1/2,b-1/2). The exact angular tangent
(a-b)/(2R^2-a-b) decreases with a+b at fixed radius, and its maximum
is 1/[2 sqrt(R^2-1/4)]. This is below tan(pi/12) throughout the
window. Thus every actual circle corner, and every nonzero
nonnegative resultant on those corners, is within pi/12 of the
center direction. This includes a physical two-corner mask with
one individual weight zero. I verified that the resultant cannot
vanish, because its nonzero weights lie in one cone of aperture
less than pi.

## 2. Actual support and the nonzero application moment

Translate the coordinate chart to the original O and rotate it so
the unchanged directed A-to-B normal is East. Write the unchanged
application p=(h,y). Then all of A has x<=h and all of B has x>=h.
Each actual square has projection width at least one, so containment
gives 1-R<=h<=R-1, including a side-interior or endpoint application.

If y=0 and h>=0, any circle corner z of A satisfies z_x<=h. Its
distance from the actual point p in A is therefore at least

    |z-p|^2 >= R^2-h^2 >= 2R-1 > 2,

contrary to the unit diameter. For h<=0 the circle corner of B
gives the identical bound with the correct reversed product sign.
The common endpoint h=0 is included. Thus y cannot be zero, and
det(p,East)=-y is already nonzero by geometry alone.

For y>0,h>=0, a circle corner of A with nonpositive vertical
coordinate gives the stronger lower bound 2R-1+y^2>2. Thus every
circle corner of A is strictly above O. No choice of a positive
corner weight or a special physical mask is made in this step.

## 3. Complete directed-angle derivation without an assumed lift

Choose an actual A circle-corner angle theta_A in (0,pi), and a B
circle-corner angle theta_B in [-pi/2,pi/2], the latter allowed by
z_B.x>=h>=0. Their support ordering gives

    cos(theta_A)<=h/R<=cos(|theta_B|),

so theta_A>=|theta_B|. The difference L=theta_A-theta_B is strictly
positive. Equality would identify a common point on the original
circle. At such a corner each inward orthonormal unit side direction
w has z dot w<=-1/2 by containment of the adjacent corner. Hence
-z has strictly positive coordinates in both inward axes, and a
short inward radial segment lies in the open square. Two squares
sharing that circle point would therefore have overlapping open
interiors. This proves the required strictness for every corner
and support endpoint.

The actual contact-to-corner distance gives z_A.x>=h-sqrt(2).
Since R>=79/40>sqrt(8/3), theta_A<5pi/6, and thus L<4pi/3. On the
other hand the angular triangle inequality, using the actual center
gap and both corner deviations, puts the minor corner gap below
17pi/30. If L>=pi, that same minor gap is 2pi-L>2pi/3, a strict
contradiction. Therefore

    0<L<pi and L<17pi/30.

This step resolves the possible wrap around the angular cut. It does
not assume that support ordering alone fixes the minor traversal.

Lift the two center directions within pi/12 of the two selected
corner lifts. Their difference lies in (-pi/6,11pi/15), strictly
inside (-pi,pi). If it were nonpositive, its absolute value would
be below pi/6, contradicting the actual center separation pi/5.
Thus the center difference is positive and below pi. Consequently
the actual A-to-B center determinant and the unchanged contact
moment are both strictly negative for the whole y>0,h>=0 row.

For y>0,h<0, reflection in the vertical axis followed by exchanging
A and B returns the directed normal to East. The application height
is unchanged, and the two reversals preserve the center determinant.
For y<0, reflection in the horizontal axis reverses both determinants
and reduces to the positive-height row. These are coordinate changes
only, not changes of the physical configuration or selected normal.
Together with the excluded y=0 case they cover every original
support line, all common-side means, and every cone endpoint.

## 4. All nonnegative physical circle resultants

Orient the minor center traversal from A to B. Its absolute angle
is strictly between pi/5 and 2pi/5. Perturbing each direction by
less than pi/12, as permitted for any actual nonzero nonnegative
circle resultant, leaves the directed resultant difference with
the same orientation and absolute angle strictly between

    pi/30 and 17pi/30.

It is therefore nonzero and has absolute value below pi. Its
determinant has the same sign as the center determinant and hence
as det(p-O,n). This includes every allowed individual zero weight
on a physical two-corner unit. It does not impose equilibrium or
replace the full resultant by a corner chosen for convenience.

## 5. Exact verification and conclusion

I independently recomputed the four strict numerical reserves used
in the new proof with Fraction arithmetic:

| Comparison | Exact positive difference |
| --- | --- |
| 79/40 versus 3/2 | 19/40 |
| (79/40)^2 versus 8/3 | 5923/4800 |
| 2/3 versus 17/30, in units of pi | 1/10 |
| 1/5 versus 1/6, in units of pi | 1/30 |

The one-square denominator and angular identities and the complete
orientation/reflection argument were independently derived, not
inferred from those scalar checks or from the root acceptance.
The root's separate complete record is
`REVIEW_BOUNDARY_CONTACT_ORIGIN_MOMENT_ROOT_2026_10_28.md`,
`7ab142d656c50ca9bcf6fe7d6696ef99d6116804e4350758fde98fd2273a0bee`.

Both claimed determinants are nonzero with the same sign at the
entire stated physical scope. The result supplies no proper
concurrence, inside-body point, force balance, fixed mean or
higher-degree reduction. The remaining seven units, when present,
are unchanged. No sampled pose, new normal selection, remote write,
shared metadata edit, Lean compilation, CI or workflow was used.
