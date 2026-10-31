# Independent review: the all-orientation stair theorem and original S-leaf join

Date: October 26, 2026.

Reviewer: C6 completion agent, independent of the source author.

**Verdict: PASS.** I read the complete
`UNIT_STAIR_POCKET_EXCLUSION.md` and
`S_LEAF_C5_AXIS_CHANNEL_COUPLED_POCKETS.md`, and checked the direct
physical chart, half-plane and winding prerequisites in
`S_LEAF_C5_TILTED_DIRECT_AND_CHANNEL_HALFPLANES.md` and
`S_LEAF_C5_RADIAL_BC_POCKET_CAPACITY.md`.

## 1. Generic geometric theorem

The first-quadrant support lemma is valid for every actual square
orientation. Its centered support is the displayed absolute-value
formula. Splitting only at its actual sign transition gives two
concave trigonometric functions whose endpoint values are exactly
\(\alpha+\beta\) and \(1+\alpha\beta\). The comparison at the
middle endpoint follows from \((1-\alpha)(1-\beta)\ge0\).
Thus the right and above separation cases follow as stated.

I checked the complete separating-axis cover for disjoint open
square interiors. Weak separation by a side normal of one of the
two squares follows from the supporting inequalities of their
Minkowski difference, including all boundary contacts. The root
square's left and below separations contradict positive width and
the stated strip/quadrant containments. The southwest normal of
the extra is impossible because its full width along that own
axis is one. The northwest and southeast cases imply actual above
or right separation respectively; the identity
\(1/2+(s-c)(c+s)/2=s^2\) has the correct sign.

For both northeast orientation ranges I rederived the square support
and every algebraic lower bound. In the shallow case the coefficient
of the center height is nonnegative, and the resulting expression
is linear in \(\beta/\alpha\); both endpoint bounds hold over
the complete interval. The identity in (13) is exact. In the steep
case, the two signs of \(\beta-\alpha s/c\) correctly select the
lower or upper horizontal center bound. Both simplifications in
(15),(17) and the final differences in (16),(18) are correct.
The common coefficient-zero case is retained by both arguments.
Pure coordinate axes were already covered and are not divided by
zero in the remaining cases.

This exhausts every square orientation and every separating side
axis. All separation and containment inequalities may be weak. The
strict exclusion follows solely from \(\ell<L\) and
\(\alpha>0\), so no generic-contact hypothesis is hidden in the
geometric theorem.

## 2. Original S-leaf physical chart and mean interval

I checked the side-axis premise against the accepted tilted-root
normal cover: it is exactly the original \(n=f_1\) branch,
with its whole actual mean \(0\le Y<db\). The support equation
is \(da=1-\delta\), and translating the unchanged actual
application produces precisely
\[
 A'=[-1,0]\times[-Y,1-Y].
\]
All five contact vertices in (10) are correct. In particular the
direct root application retains its original full Z interval, and
the U reserve is exactly one. The quantity
\(L_0-\ell=1/2-db>7/30\) holds for the full mean interval,
using \(db<4/15\). Thus \(0<\ell<L_0\le1\) does not require
choosing a convenient endpoint mean.

For an occupied actual BC pocket, the accepted crosscut theorem
places the whole extra beyond its actual positive-height line.
The farthest-corner identity applied to that whole square gives
\(R^2\ge(H+1)^2+1/4\), hence H<=d. I rederived the squared
inequality and the monotone bound
\(\alpha\ge4d/(4d^2+1)>3660/4621>3/4>\beta\).
Its positive rational reserve is \(777/18484\), as stated.
No particular frame for the exterior extra is assumed.

## 3. Whole central-region localization

The earlier BC-pocket source proves that the entire actual central
region is on the inward side of the BC return line, with the real
genuine leaf included. It derives this using the positive full
connection coefficients and q_A on its true leaf ray; it does not
assume q_A lies inside A or treat A as a fictitious circle load.
After the stated translation its exact inward inequality is (16).

The actual center/contact loop can be homotoped to the contact
polygon inside the original closed occupied bodies. A central
extra's open interior retains winding one, so lies in that
polygon's convex hull. Every listed vertex lies in the closed
strip \([-1,1]\times[0,\infty)\); closure gives the same
whole-square containment for the extra. This supplies every
premise of the generic stair theorem, including disjoint open
interiors from the actual translated root square.

The compact-interior winding argument applies at genuine shared
endpoints and other original degeneracies. Additional physical
zero-selected-force contacts may subdivide a region but cannot
invalidate either closed half-plane containment. Therefore an
occupied BC pocket excludes every whole central extra, exactly
as the claimed product-of-allocation-counts statement says.

## 4. Accepted scope

The coupled exclusion covers the complete original tilted
S-leaf side-axis A-to-C branch, all genuine root means and Z
values, both physical B masks, both C individual circle-weight
endpoints, all true degrees, sliders and additional squares.
It does not convert strict root-corner channels into side axes.
It removes all central-plus-BC allocations in that branch, but
does not claim a whole S-leaf completion or any new original
gate closure. The two leaf-side exterior regions retain their
remaining obligations.

No angle grid, numerical pose, computational certificate, Lean
compilation or CI is part of either proof.
