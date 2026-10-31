# Independent focused review of the occupied radial-side pocket height and angle bounds

Date: October 30, 2026 UTC. Reviewer: branch_budget.

**Result: ACCEPT the complete occupied-height argument and every angular
consequence in Section 7.3 of the exact target below.** I did not contribute
this lemma or its earlier strict-height observation. This is the separate
noncontributor check requested because root and joint_pockets contributed
that observation. It supplements, and does not replace, the separate full
review of the target's other theorems.

## Exact texts read in full

| Text | SHA-256 |
| --- | --- |
| SIMPLE_CYCLE_POCKET_CONTACT_LOCALIZATION_AND_SIDE_POCKET_MIDPOINT_DILATION_2026_10_30.md | 6843aa6a6735bc90395cac8baf7d60105a60aa625d05c811cc867bf4c5ef2b2c |
| RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md, target [R] | 2d78bc2892c11e58007881ff84d57cc6606dce201bb46d412ef216c12577191e |
| END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, target [H] | 20a845eff8bee3e9c533162df0b32ea96f9dd104a3cfec41efb3b0cf92d6e9cf |

I read all 500 lines of the target and both complete direct inputs. I
independently reconstructed the argument below, including its equality
case. The original full-component and occupied-cap premises of the target
are retained. Acceptance here does not independently recertify its other
inputs, its physical-contact localization theorem, or its dilation theorem.

## 1. The original chart and its strict application condition

The full physical support cover in [R], Section 1, applies to the actual
radial loaded endpoint and genuine side transmitter. It leaves, after a
whole reflection, precisely

    p_A=d e+f/2, g=-c e+s f, N=s e+c f,
    c,s>0, c^2+s^2=1,
    ell=-dc+s/2, h=ds+c/2,
    U=[ell,ell+1]g+[b-1/2,b+1/2]N.

Its singleton endpoint argument gives the strict retained relation
`|b-h|<1/2`: the actual application is in the relative interior of U's
side. It is not a newly chosen side mean. The entire side-channel cap
places each occupied-pocket unit E in `N.x>=h`, and [R] gives `h>1/2`.
Neither endpoint's physical corner mask nor any individual zero weight
is removed in this call.

## 2. The full support bound and its sole equality case

[H], Section 1, is a statement about an arbitrary contained unit; its
end-triangle hypotheses belong to later sections and are not required
for this support bound. For completeness, the original center c_E obeys

    |c_E|^2+|c_E|+1/2<=R^2,
    |c_E|<=d+1/2.

The actual halfwidth in N is at least 1/2. Hence the cap containment
implies `h<=N.c_E-1/2<=d`. If `h=d`, both inequalities are equalities.
The center is `(d+1/2)N`, the N halfwidth is exactly 1/2, and the actual
unit is the unique radial cap

    E=[d,d+1]N+[-1/2,1/2]g.

There is no assumption that E was initially a boundary body. Its entire
position and circle contact follow from this equality.

The orthonormal coordinates of the original p_A satisfy
`ell^2+h^2=d^2+1/4`. Thus equality gives `ell^2=1/4`.
Because `d,c>0` and `s<1`, one has `ell=-dc+s/2<1/2`, so
`ell=-1/2`. The longitudinal U and E intervals are both exactly
`[-1/2,1/2]`. The strict original mean gives

    b-1/2<d<b+1/2.

Consequently the open rectangle with longitudinal coordinate in
`(-1/2,1/2)` and transverse coordinate in
`(d,min(d+1,b+1/2))` is nonempty and belongs to both actual interiors.
This is a positive-area overlap, including every possible endpoint
equality elsewhere in the original chart. Therefore `h<d` is strict.

## 3. Every angular branch is covered

Set `phi=atan(1/(2d))` and `c=cos(theta), s=sin(theta)` with
`0<theta<pi/2`. The project range has `d>1/2`, so `0<phi<pi/4`.
Writing `k=sqrt(d^2+1/4)`, the exact identities are

    h=k sin(theta+phi), d=k cos(phi),
    ell=-k cos(theta+phi).

On the whole complementary interval
`pi/2-2phi<=theta<pi/2`, the argument theta+phi lies in
`[pi/2-phi,pi/2+phi)`, where sine is at least cos(phi).
This includes both its increasing and decreasing branches. It contradicts
`h<d`; therefore

    0<theta<pi/2-2phi,
    c>sin(2phi), s<cos(2phi).

Now `phi<theta+phi<pi/2-phi`, and cosine is strictly decreasing on
this whole interval. Since `k cos(phi)=d` and `k sin(phi)=1/2`,

    -d<ell<-1/2,
    1/2-d<ell+1/2<0.

These are exactly all inequalities in target (7.5), with no lost second
trigonometric branch and no limiting angle silently included.

The last consequence (7.6) also follows at its stated conditional scope:
`b>h-1/2>0`; if `b>1/2`, the actual U rectangle lies beyond transverse
height `b-1/2`, so the separately established original bound
`dist(O,U)<delta` implies `b<1/2+delta`. If `b<=1/2`, the same strict
upper bound is immediate. The printed `delta<29/128` gives
`b<93/128`.

## Scope of this acceptance

All checked conclusions concern the unchanged original units, normals,
applications and full physical masks. No motion is needed for the strict
height or the angle bounds. No scalar parameter, contact mean or circle
coefficient is reselected. The argument is a necessary geometric
restriction on an occupied radial-incident side pocket; it does not
exclude the remaining U/T/loaded-return system or close an original
parent. No mathematical correction to the pinned source is requested.

Only full manuscript reads and symbolic identities were used. No pose
search, angle grid, new certificate, Lean/Lake, CI, metadata or remote edit
was performed.
