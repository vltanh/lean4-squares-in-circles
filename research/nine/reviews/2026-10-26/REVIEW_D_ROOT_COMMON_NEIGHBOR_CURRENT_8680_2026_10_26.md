# Fresh current-head audit: a D root and any near-origin unit

Date: October 26, 2026. Reviewer: `rooted_current`, separately from
the author and earlier review. Baseline:
`8680a4b9204c0d6fb82a8d052ece5bb52aa9b6c8`.

**Verdict: PASS** for the complete
D_ROOT_NEAR_ORIGIN_COMMON_BOUNDARY_NEIGHBOR_EXCLUSION.md and its
two original mixed hub/tip diamond callers. I read and reconstructed
the full geometric proof, including every supporting-normal case.
The current remote genuine-leaf, centered-arc, root-localization and
support-span inputs are byte-identical to the retained exact inputs.

Frozen main source SHA256:
`c193b23275a411e9771f9c5a332d7ede3ec6b4c6002ada9745b3ba0c3898a131`.

## 1. The theorem is physical and degree-free

The actual D leaf fixes H=[-s,r]x[-A,beta] with O in its open
interior. A different actual unit B meets D_epsilon, where
epsilon=max(d-1,0). For d<=1 this disk is the singleton O, so B
would contain O and overlap H; only d>1 remains. A separating
axis from H to B has positive support at most delta=d-1. It is an
auxiliary geometric separator, not a replacement force normal.

Its radial contribution gives |n_x|<1/20; after vertical reflection
its vertical component exceeds19/20 and the original H top height
satisfies0<beta<1/57. Every point of B is above -25/228. All these
bounds hold for any actual positive degrees and even if HB is not
a physical contact. The actual D leaf is kept as an obstacle and
as a physical boundary-center direction.

## 2. Every boundary neighbor is below H's top side

A physical boundary center has norm>4/3. A hypothetical northwest
or negative-axis center has nearest-point distance to H incompatible
with r^2-s^2=2r-1>1/4>beta^2. A northeast center has sine of its
angle from the actual D leaf below3/5, whereas their strict physical
center separation exceeds2pi/9, whose sine exceeds3/5. Thus every
other boundary-neighbor center lies below the horizontal axis.

If such a unit contained any point on the entire top H side,
including both endpoints, its center would either have norm squared
below965/576<16/9 or lie too close in angle to the actual leaf.
This excludes all upward supporting normals at once, independent
of the physical owner or circle weights at either contact.

## 3. All three remaining axis normals are excluded

At the downward axis the whole boundary neighbor K is below
-56/57, while B is above -25/228. At the right axis its center
has first coordinate>9/8 and negative second coordinate. Separation
from the actual leaf gives C_y<-(3/4)C_x<-27/32. Even K's highest
point is then below -13/96<-25/228, so it cannot touch B.

At the left axis the B contact forces the actual top of K above
-1/12. Writing its own side components u>=w>=0, u^2+w^2=1,
all four physical vertices have squared radius bounded by the
larger of the displayed F1,F2 expressions. Their difference is
2(s-1/12)w>=0. One eigenvalue bound and one Cauchy--Schwarz bound
give F1<4-79/2880<4. This is a single continuous orientation bound,
including aligned K; physical circle contact requires radius R>2.

## 4. Strict corner normals retain the full actual slider

The support-span lemma follows directly from the own-coordinate
square: when the entering support normal m has m.n<0, at least one
own-axis n component is negative, and the positive span is strictly
below one. Its side-interior version retains the entire actual mean.
This excludes n_x=0 and opposite horizontal signs of n,m, since
the actual H-to-B support gap from the lower corner is at least one.

For equal horizontal signs the complete K chart is
Q+[-tau,1-tau]U+[0,1]V, with U=(sin(theta),cos(theta)) and
V=(cos(theta),-sin(theta)). At a vertex, an upward inward axis must
point right; if both inward axes pointed down their whole n-span
would be too short. A side-interior Q has exactly this chart with
the actual arbitrary tau. Thus no support owner is omitted.

The true n-span required to reach B gives theta<=2asin(|n_x|),
sin(theta)<1/10, cos(theta)>99/100 and tau<21/400. On the lower
left H corner, every point of K then has squared radius below
560621/160000<4, impossible for a circle-touching unit. On the
lower right corner, the fixed actual point Z=(r+1/4,-1/8) is strictly
inside both the unchanged D leaf and K. The source verifies its two
actual own coordinates against the full tau interval with strict
margins. No mean or contact point was selected to obtain that overlap.

The up, down, left, right and two strict lower-corner alternatives
exhaust every possible H/K supporting normal. The proof therefore
excludes any common physical boundary neighbor of H and B, without
a force equation or degree restriction at K or B and without using
the quarter-disk completion theorem.

## 5. Exact original scope and accounting

At the current baseline the whole original diamond hub/tip mixed
labels are both unchecked:

- `M6.B4L2.DIAMOND.HUB_TIP.LKC.DH_SB`
- `M6.B4L2.DIAMOND.HUB_TIP.LKC.SH_DB`

In either assignment the genuine S root is the near-origin unit,
and original positively loaded K is a physical common neighbor of
both roots. K retains its true degree three, the other loaded page
tip C retains degree two, H retains degree four and B degree three.
No force is omitted. The theorem covers every reflected placement,
physical mask, zero individual weight, original mean and the same
three arbitrary completion units. Exactly these two additional full
families have a new complete exit. The SS family and the whole
hub/tip parent remain open from this result alone.

The geometric theorem also applies to identical actual features in
larger components, but does not invent fine labels or imply a whole
coarse closure. Mixed opposite-C4 and two-hub-diamond consequences
overlap the separate common-neighbor package and must not be counted
again. No computational certificate, sampled pose, force deletion,
normal change, Lean compilation, CI or remote mutation was used.
