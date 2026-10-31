# Adoption: a uniform oblique bridge theorem and complete Type I/II roof features

Date: October 29, 2026 UTC. Parent commit:
`02d0c4e21adb03ab35cbdd2327e1b489a9d7a3b0`.

**Accepted at the complete stated feature scopes.** Three new mathematical
sources have full separate independent reviews. Root independently
reviewed both Type II sources and their complete capacity reports. Root
and roofs are Type I contributors; its complete independent review is by
root_triangles. The combined root report states these roles explicitly.

## 1. A radius-free result for whole actual units

At every minimum support Q of a real unit square S in unit direction n,
and for every unit d with n.d>=0,

    min_S d >= d.Q-|det(n,d)|.

The proof includes strict vertices, owned sides, every original side
mean and both endpoints. Consequently no actual unit can connect two
units B,C when their original supports satisfy

    d.(Q_B-Q_C)>sqrt(2)+|det(n_B,d)|+|det(n_C,d)|,
    n_B.d>=0, n_C.d<=0.

This general result needs no stress, radius, exterior degree, load,
circle mask or selection assumption. It compares the whole physical
units, not only their centers or marked points.

## 2. Complete Type I two-shared-roof closure in the unloaded row

If both original Type I roof interfaces AV,DV are physically shared,
their actual frames are V-parallel. The complete two-shift cover has
both shifts nonpositive and at least one zero. At point-only AD, the
full hub forces give strict NW/SE exterior supports separated by
(-2,2). The new oblique theorem excludes every actual bridge N, in
either original load column.

For positive-shared AD, all three full V/A/D moments force the actual
DC mean q=1-2*tau, tau=rho/(nu+rho). The support difference is exactly
(-2*(1-tau),2). The already accepted radius-free unloaded-bridge theorem
then excludes the entire feature in L135, including all original roof
and hub means and the reflected placement. The loaded positive-shared
AD alternative in L1345 remains open.

Source: ACTUAL_OBLIQUE_SUPPORT_BRIDGE_AND_TYPE_I_BOTH_SHARED_ROOFS_COMPLETE_UNLOADED_EXCLUSION_2026_10_29.md.

## 3. Type II shared West is impossible; the genuine remainder is explicit

The full V2 moment gives S>=C, retaining w=1,S=C. In every physically
shared West-roof configuration, actual support geometry leaves just
three AD owners. Two have direct whole-side support contradictions.
The third gives the complete D3 moment nu*t=rho*(C-S), impossible
because t,nu are positive. This excludes the entire shared-West
feature for both original N loads, with no N equation required.

The surviving West contact is a genuine V-only singleton, 0<w<1,S>C.
Its complete nonfree AD cover has four own axes. Full original support
and torque arguments remove every shared AD interface, all A-owned
-e cases, the wrong signs in both D-owner rows, and both strict vertex
returns in the D-perpendicular row. Every surviving side mean is
derived and retained explicitly.

For the D-roof-direction upper return, its actual D-frame support
difference has vertical component 1+H-K>2 and horizontal component
less than -(H+K)<0. The same generic unloaded-bridge theorem removes
that WHOLE row in L135, without any angle or ratio subdivision.

Sources: UNIQUE_CIRCLE_TYPE_II_SHARED_WEST_ROOF_ALL_HUB_OWNERS_COMPLETE_EXCLUSION_2026_10_29.md
and UNIQUE_CIRCLE_TYPE_II_SINGLETON_WEST_COMPLETE_HUB_OWNER_AND_EXTERNAL_RETURN_DOMAIN_2026_10_29.md.

## 4. Exact original residual and review boundary

| Feature | Original L135 | Original L1345 |
| --- | --- | --- |
| Complete Type III, all original owners | Previously closed | Previously closed |
| Type I: both roofs shared, point-only AD | Closed here | Closed here |
| Type I: both roofs shared, positive-shared AD | Closed here | Remains |
| Type I: at least one genuine singleton roof | Remains | Remains |
| Type II: shared West roof | Closed here | Closed here |
| Type II: D-roof owner, upper exterior return | Closed here | Remains |
| Other genuine Type II rows in the complete table | Remain | Remain |
| Physical-two roof residuals | Remain | Remain |

All nine physical units remain. A,D retain their unloaded true3 stars;
V,B,C retain loaded true2; N remains unloaded true2 in L135 and loaded
true2 in L1345. Every positive edge, original normal, actual support
owner, full mean, physical corner and individual zero circle weight
remains. The new generic oblique theorem and Type I point-only exit are
selection-free. The Type II owner entries and unloaded bridge use the
same explicitly conditional prior selection and diagonal avoidance.
Their missing global compatibility proof is not supplied here.

The complete proof/review pins and reversible metadata changes are in
TYPE_I_OBLIQUE_BRIDGE_AND_TYPE_II_COMPLETE_DOMAINS_CHECKPOINT_2026_10_29.json.
All seven distinct direct input pins match. Counts are unchanged:
**2373/2513 original fine checked, 140 open; 36/58 coarse closed,
22 open**. No whole D02 flag changes. The unrestricted sharp theorem,
equality, global prerequisite audit and Lean integration remain open.
Hand proofs only; no Lean/Lake build, CI/workflow dispatch, numerical
pose search, angle mesh, new packing certificate or merge was used.
