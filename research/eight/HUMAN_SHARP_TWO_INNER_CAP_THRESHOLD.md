# Sharp inner-center angular capacity for two squares in a cap

Research continuation, 2026-10-12. This is an unconditional
orientation-independent **center-norm** lemma, applicable to the
remaining S2/S3/S4 outer-count and central-offset branches.
It improves the previously used \(h\ge2/5\) sufficient threshold
in HUMAN_SINGLE_SIDE_OUTER_K_PRUNING.md to the exact smaller
threshold \((\sqrt3-1)/2\).

## Theorem

Let two *distinct*, pairwise interior-disjoint unit squares \(S,T\)
be wholly contained in a common outward half-plane
\[
n\cdot x\ge h,\qquad |n|=1,\quad h\ge0,
\]
where the origin is the center of the disk used to define "inner."
Suppose **both** square centers \(p_S,p_T\) have norm strictly less
than one. Then necessarily
\[
\boxed{h<(\sqrt3-1)/2}.                         \tag{1}
\]
Thus for every \(h\ge(\sqrt3-1)/2\), at least
one of two squares in that cap has an **outer center**
(norm \(\ge1\)), for arbitrary unrelated square frames,
regardless of the containing disk radius.

Moreover, whenever two inner centers lie in any nonnegative
whole-square cap, their transverse center coordinates relative
to \(n\) have **strictly opposite signs**, and at least one has
\[
|n_\perp\cdot p|>(h+1/2)/\sqrt3.                \tag{2}
\]
The side-offset threshold (1) is **sharp even for two actual
axis-parallel unit squares** at disk radii smaller than the n=8
search ceiling, as the explicit construction below shows.

## Proof

For any unit square, its half-width in an arbitrary unit normal
\(n\) equals \((|n\cdot e|+|n\cdot f|)/2\ge1/2\).
Whole-square cap containment therefore forces
\[
n\cdot p_S\ge h+1/2=:a,\qquad
n\cdot p_T\ge a.                                \tag{3}
\]
Both center radii \(r_S,r_T\) are \(<1\), hence if
\(\theta_S,\theta_T\) denote their signed center-ray angles from
\(n\), then
\[
\cos\theta_i = (n\cdot p_i)/r_i
\ge a/r_i>a.
\]
In particular, \(a<1\) and
\[
|\theta_S|,|\theta_T|<\arccos a\le\pi/3
\quad (h\ge0).                                    \tag{4}
\]

**Angular exclusion for two inner centers.**
Disjoint unit squares have disjoint inscribed
open radius-\(1/2\) disks, so
\(|p_S-p_T|\ge1\). But if their smaller
angular gap \(\delta\le\pi/3\), with center
radii \(0<r\le s<1\), the cosine law gives
\[
|p_S-p_T|^2=r^2+s^2-2rs\cos\delta
\le r^2+s^2-rs
=s^2-r(s-r)\le s^2<1,
\]
a contradiction. Therefore
\[
|\theta_S-\theta_T|>\pi/3                     \tag{5}
\]
(the ordinary difference equals the smaller separation by (4)).

If the signed angles had the same weak sign, their
difference would be less than \(\pi/3\) by (4),
contradicting (5). Thus they have strictly opposite
signs, proving the first transverse-sign conclusion.

Combining (4) and (5) yields
\[
\pi/3<|\theta_S-\theta_T|<2\arccos a.
\]
Consequently \(\arccos a>\pi/6\), so
\(a<\cos(\pi/6)=\sqrt3/2\).
Since \(a=h+1/2\), this gives exactly (1),
including strictness at the boundary.

Finally, opposite angular signs and (5) imply at
least one absolute angle \(>\pi/6\). For that
center,
\[
|n_\perp\cdot p|=(n\cdot p)|\tan\theta|
>(h+1/2)/\sqrt3,
\]
proving (2). QED.

## Sharpness for actual whole squares (not just center disks)

For every \(\varepsilon\in(0,(\sqrt3-1)/2)\), put
\[
x_\varepsilon=\sqrt3/2-\varepsilon,\qquad
h_\varepsilon=x_\varepsilon-1/2.
\]
Take the two **axis-aligned** unit squares
\[
S_\pm=[x_\varepsilon-1/2,x_\varepsilon+1/2]
\times [\pm1/2-1/2,\pm1/2+1/2].
\]
They occupy adjacent vertical strips \([0,1]\) and \([-1,0]\),
so their open interiors are disjoint. Both are wholly beyond
\(x=h_\varepsilon>0\), and their centers
\((x_\varepsilon,\pm1/2)\) satisfy
\[
|p_\pm|^2=x_\varepsilon^2+1/4<1.
\]
Their farthest vertex squared norm is
\[
(x_\varepsilon+1/2)^2+1
<(1+\sqrt3/2)+1=2+\sqrt3/2<9789/2500.
\]
Thus they fit the **actual n=8 search ceiling** in the same disk,
and as \(\varepsilon\downarrow0\), their cap offset tends to
\(H_*=(\sqrt3-1)/2\) from below. Therefore (1) cannot
be made strictly smaller even under the extra disk bound for a
**standalone two-square cap theorem**. This does not assert
that the two squares extend to a full eight-square packing.

## Consequences for the exact n=8 side-status queue

Put
\[
H_*=(\sqrt3-1)/2\approx0.3660254,\qquad
T_*=\tfrac12-H_*=1-\sqrt3/2\approx0.1339746.
\]
These are *exact analytic thresholds*. As a simpler rational
corollary, a cap at \(h\ge3/8\) cannot hold two inner centers,
because \(3/8>H_*\).

**Exclusive all-single-side S2=(3+0,2+2).**
Let \(t\) be the signed central-center coordinate on the
2+2 axis. The farther two-square side has offset
\(h_\mathrm{far}=1/2+|t|\ge1/2\), so **both**
its center labels are outer. If
\[
|t|\le T_*,
\]
the nearer two-square side has
\(h_\mathrm{near}=1/2-|t|\ge H_*\), and hence
contributes a **third distinct** outer-center label.
The perpendicular triple has at least one further
outer center, by the known triple-inner-cap exclusion.
Thus
\[
\boxed{\text{S2 and } |t|\le T_*\implies k\ge4}. \tag{6}
\]
In particular S2/k=3 requires \(|t|>T_*\),
strengthening the former \(|t|>1/10\) necessary
condition. This does **not** remove all S2/k=3
cases, since the 2+2 axis still allows
\(|t|<5/24\).

**Exclusive S3=(3+1,2+1).**
Let \(h\) be the offset of the *two-member* cap
of the 2+1 axis. The perpendicular triple and
its opposite singleton supply two distinct outer
centers. If \(h\ge H_*\), the 2+1 axis supplies
two **additional distinct** outer centers:
for \(h\ge1/2\) both two-member cap centers are
outer; for \(H_*\le h<1/2\) the two-member cap
has at least one outer and its opposite singleton
has offset \(1-h>1/2\) and is outer. Hence
\[
\boxed{\text{S3 and }h\ge H_*\implies k\ge4}.    \tag{7}
\]
The S3/k=3 branch therefore requires \(h<H_*\)
(in addition to the triple offset \(<13/100\)
from the improved triple-cap two-outer theorem).

**Exclusive S4=(2+1,2+2), including equality.**
For the offset \(h\) of the two-member side on the
2+1 axis, \(h\ge H_*\) yields two distinct outer
centers from that axis. The 2+2 axis has two
far-side outer centers; therefore
\[
\boxed{\text{S4 and }h\ge H_*\implies k\ge4}.
\]
If also the 2+2 signed central coordinate obeys
\(|t|\le T_*\), its nearer cap supplies a
third outer center from that axis, hence
\[
\boxed{\text{S4 and }h\ge H_*,\ |t|\le T_*
\implies k\ge5}.                                \tag{8}
\]
These strengthen the previous \(h\ge2/5\)
and \(|t|\le1/14\) continuous k restrictions.
No whole S4 branch is discarded; the
five-corner equality construction remains valid.

## Limitations

The proof uses **center norm** and an actual whole-square
cap. It does not say that a center of norm \(\ge1\)
forces circle contact, or that centers lying merely on
the positive side of the cap normal count as whole
square members. The classification's symbolic
3,995,040 status word count does not change.

This does not imply the unrestricted sharp
lower bound \(R_8\ge\widehat R\).
