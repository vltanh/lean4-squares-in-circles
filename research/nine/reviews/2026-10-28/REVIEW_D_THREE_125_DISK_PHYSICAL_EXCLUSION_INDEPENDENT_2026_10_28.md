# Independent review: the fixed 3/125 disk at a genuine D root

Date: October 28, 2026. Reviewer: diamond, independent of author two_blocks.

**Verdict: PASS unchanged, at its full stated physical scope.** I read and
independently reconstructed the complete source
`D_LEAF_ROOT_AT_MOST_ONE_OTHER_UNIT_IN_THREE_125_DISK.md`, SHA256
`34385a647c1889564b3423ecfff03a7a75747275e45f68346c3f8a9f06abfaaf`.
The complete actual-domain proof is valid on
`79/40<=R<=sqrt(1105)/16`, including both endpoints, and permits arbitrary
true degrees, loads, forces, additional physical contacts and completing
units. It gives no fine or coarse gate closure by itself.

The exact accepted conclusion is that at most one original closed unit
other than the genuine D root G meets the closed disk of radius `3/125`.
If such a unit K exists, every unit other than G and K has distance
strictly greater than `3/125`, hence strictly greater than
`sqrt(2)*epsilon`, where `epsilon=max(sqrt(R^2-1/4)-2,0)`.

## 1. Original geometry and the exhaustive shallow reduction

The only operative external input is the genuine D chart from
`RADIAL_BRIDGE_AND_LEAF_REDUCTION.md`, SHA256
`faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676`.
Its actual root and leaf are retained. No force equation at a near unit
is imported, and no radius-two lower bound is used.

I checked the complete radius margins directly. The comparisons
`sqrt(2)<57/40`, `R<52/25`, and `sqrt(2)>140/99` have positive
squared reserves `49/1600`, `1599/160000`, and `2/9801`.
Thus `11/20<r<1648/2475<2/3`, with final upper reserve `2/2475`,
and `s=1-r>1/3`. These strict margins remain valid at both original
radius endpoints.

Every point of another closed unit avoids `int(G)`, because its actual
interior is dense in that full-dimensional closed square. A point in the
closed `3/125` disk therefore forces one root vertical margin at most
`3/125`: both horizontal margins are larger, and if both vertical margins
were larger the whole disk would lie in `int(G)`. The two possible shallow
vertical sides cannot occur together because their margins sum to one.
One reflection therefore gives the single exhaustive chart
`0<a<=3/125`. The whole closed lower semicircle of radius `1/3` is
in fact strictly inside G in this chart. The real leaf cannot be one of
the two hypothetical near units because its minimum first coordinate is
`r>3/125`.

## 2. Actual arcs inside the two arbitrary near units

For each actual point x_i in the small disk, choose each own axis toward
the square center and order them positively. At least half a unit remains
in both chosen directions, including when x_i is on an actual side or
vertex. Thus the displayed actual half-unit rectangle is a subset of
the original square; this is a coordinate choice, not a translated unit.

With `beta=arcsin(3/40)` and `rho=1/3`, every point on the source's
closed arc has both own coordinates relative to x_i strictly between
zero and one half. The lower reserve is exactly
`rho*sin(beta)-3/125=1/1000`, and the upper reserve is
`1/2-rho-3/125=107/750`. Accordingly the entire closed arc belongs
to the actual open interior of its square. The two arcs are disjoint
and lie in the open upper semicircle, since the closed lower semicircle
is occupied by the root interior.

Lifting their nonwrapping angles from east to west gives
`-beta<phi_R<3*beta`,
`pi/2-3*beta<phi_L<pi/2+beta`, and
`abs(phi_R+pi/2-phi_L)<2*beta`; the source uses harmless weak versions.
These follow from the two upper-semicircle endpoint constraints and the
strict separation of the two closed intervals, not from an assumed
orientation of the squares.

I independently checked `cos(2*beta)=791/800`,
`sin(2*beta)<3/20`, and `sin(3*beta)=3573/16000<9/40`.
Since `beta<pi/6`, the cosine of `3*beta` is positive. Its lower
bound `cos(3*beta)>97/100` follows with squared reserve `339/40000`.
The resulting full-interval sine and cosine bounds are valid at all
allowed angular endpoints.

## 3. Both actual separator owners are retained

For two squares with disjoint open interiors, the separating-axis
theorem gives a weak separator parallel to an own side axis of at least
one square. One may justify it directly from the edge normals of their
convex difference polygon, so tangential contact is included.

The two near-vertical axis alternatives `v_R,u_L` cannot separate the
squares. Each actual half-unit north segment starts at a projection at
most `3/125` and ends above `1/4`; the latter reserve is
`791/1600-3/125-1/4=1763/8000`. The full projection intervals of
both squares therefore contain `[1/8,1/4]` in their interiors.

The remaining separator direction, after its sign is fixed rightward,
is exactly `u_R` or `-v_L`. The actual east segment of K_R has a
strictly positive projected point and the actual west segment of K_L
has a strictly negative one. The opposite ordering of their separated
projection intervals is thus impossible. Consequently
`min(K_R) r_0.x>=max(K_L) r_0.x>=-3/125`, as stated.

In K_R's actual own frame the coefficients of r_0 satisfy
`A>=791/800` and `abs(B)<3/20`. The source evaluates the separator
at a genuine point of the full left face, keeping the actual near
point's north coordinate. This gives
`l_r>-(920/791)*(3/125)=-552/19775` and hence
`l_r+1>19223/19775`. The strict inequality and its direction survive
division by A because A is positive and bounded below. No common
orientation or preferred separator owner has been assumed.

The actual near point and half-unit north segment also give
`l_r,l_n<=3/125` and `l_n+1>=1/2-3/125`, exactly the additional
interval information needed for the final witness.

## 4. The unchanged leaf and near square contain the same interior point

The source's witness is the actual point `q=(r+1/4,6/25)`. Its strict
diamond reserve is `1/100`, so q is in the open interior of the original
D leaf for every radius and root slider in the stated domain.

The own-coordinate estimates for K_R are correct on the complete angular
interval. The first coordinate lies strictly between `361/500` and
`364/375`; the second lies strictly between `531/20000` and
`357/800`. Comparing these to the actual intervals from Section 3 gives
the four positive reserves

| Required comparison | Exact positive reserve |
| --- | --- |
| First coordinate lower bound minus `3/125` | `349/500` |
| Right-face lower bound minus first coordinate upper bound | `421/296625` |
| Second coordinate lower bound minus `3/125` | `51/20000` |
| North-face lower bound minus second coordinate upper bound | `119/4000` |

Thus q is strictly inside both of K_R's actual full own-coordinate
intervals. It is in `int(K_R)` and `int(L)`, and K_R and L are distinct.
This contradicts physical interior disjointness. The argument covers
small-disk boundary points, square boundary points, weak contacts,
arbitrary original orientations and both possible separator owners.

## 5. Quantitative consequence and audit scope

Because every remaining unit is compact and has empty intersection with
the closed `3/125` disk, its distance is strictly larger than `3/125`.
The comparison with the far-body threshold is also strict:
`sqrt(2)<36/25` has squared reserve `46/625`, while
`(36/25)*(1/60)=3/125` and `epsilon<1/60`. This is a distance
conclusion, stronger than merely avoiding the closed epsilon disk.

I separately recomputed every rational reserve in the author's exact
record, SHA256
`c145410ac52eb9779c4bd1b4cc52b4b3a57fdfd43221504423dd445ce8a9e17b`.
All agree. These exact calculations corroborate the full independent
geometric reconstruction above; they are not a substitute for its angular,
feature, separator and actual-witness arguments.

The earlier near-origin source is method history only. The new larger
disk, constants and witness are proved in full in the reviewed manuscript.
The only operative external proof is the original genuine D chart at the
pin above. The accepted source bytes require no change.

This review grants zero fine and zero coarse credit. It does not assert a
new completion exclusion without a caller proving its necessary near-unit
premise. No force, true degree, physical unit, original normal, actual mean,
mask, ledger, Lean source or remote object was changed. No Lean build, CI,
numeric pose search or sampled angular verification was performed.
