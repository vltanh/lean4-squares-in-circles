# Four explicit transverse center anchors in the S2 near-inner branch

Research continuation, 2026-10-12. This is a quantitative,
arbitrary-square-frame **continuous placement theorem** for the still
unresolved exclusive S2/k=4 near-inner subcase. It strengthens
the earlier qualitative opposite-sign polarization of inner and
outer two-square cap pairs, without inferring whole-quadrant
square membership from center signs.

## Statement

Let eight independently oriented, pairwise interior-disjoint
unit squares fit in \(D_R\), with
\(R^2\le9789/2500\). Let C be their unique
origin-containing square, and suppose the seven exterior
squares have exclusive single-side statuses
\[
R:3,\quad L:0,\quad U:2,\quad D:2,
\]
where U is the **nearer** of the two opposite 2+2 whole caps.
Let the two U centers both be **inner** (norm <1). Write
\[
h_U=1/2+b,\qquad 7/24<h_U<(\sqrt3-1)/2,
\quad h_D=1-h_U>5/8.
\]
Order the U labels by transverse center x coordinate
\(x_{U_-}<x_{U_+}\), and the two D labels analogously.

Then the four center x coordinates satisfy the independent
**strict rational bounds**
\[
\boxed{x_{U_-}<-9/25<0<9/25<x_{U_+},}       \tag{1}
\]
\[
\boxed{x_{D_-}<-29/100<0<29/100<x_{D_+}.}   \tag{2}
\]

These inequalities hold for **every allowed independent
square orientation**, and do not assume the squares touch.
The previous notes additionally prove, under the same
S2 near-inner hypotheses,
\[
k=4,\qquad 0<h_R<1/20,
\]
with the two R outer center rays on opposite sides of +x.

## 1. The two U inner centers are each transverse by >9/25

We first prove an elementary two-inner-center cap fact.
Let two disjoint-interior unit squares have centers
\(p_1=(x_1,y_1)\), \(p_2=(x_2,y_2)\) of norm
strictly less than one and lie wholly beyond
\(y\ge h\) with \(h\ge7/24\).
The whole-square center projection gives
\[
y_i\ge h+1/2\ge19/24=:a,\qquad y_i<1.
\]
The sharp inner-center angle lemma
[HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md](HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md)
forces the two transverse signs to be strictly opposite.

Because a pair of disjoint unit squares has
center distance at least one (inscribed
radius-1/2 disks), and
\[
|y_1-y_2|<1-a,\qquad |x_i|<\sqrt{1-a^2},
\]
we obtain
\[
|x_1-x_2|>\sqrt{1-(1-a)^2}
=\sqrt{2a-a^2}.
\]
The lower bound on the right increases with a
and the upper bound on |x_i| decreases with a,
throughout \(0<a<1\). Consequently for either
of the opposite-sign x coordinates,
\[
|x_i|>
\sqrt{1-(5/24)^2}-\sqrt{1-(19/24)^2}
=\frac{\sqrt{551}-\sqrt{215}}{24}.         \tag{3}
\]

The following exact rational square comparisons suffice:
\[
\sqrt{551}>1173/50,\qquad
\sqrt{215}<44/3,
\]
because \(551\cdot2500-1173^2=1571>0\) and
\((44/3)^2-215=1/9>0\).
Therefore
\[
\frac{\sqrt{551}-\sqrt{215}}{24}
>\frac{1319}{3600}>\frac9{25},
\]
the final margin being \(23/3600>0\).
This proves (1).

## 2. Two distant outer D rays force |x_D|>29/100

The prior
[HUMAN_S2_K4_NEAR_INNER_FIVE_HUNDREDTHS.md](HUMAN_S2_K4_NEAR_INNER_FIVE_HUNDREDTHS.md)
proved a separate full-orientation far-cap polar lemma:
**every** whole square in \(y\le-h_D\) with
\(h_D\ge5/8\) at the present disk ceiling
has center satisfying
\[
|p_x|<(-p_y)/\sqrt3.
\]
Thus the two D center rays (both outer, since
\(-p_y\ge h_D+1/2>1\)) lie in
the ordinary nonwrapping southern arc
\[
-2\pi/3<\phi_-<\phi_+<-\pi/3.
\]
The arbitrary-frame pair theorem
HUMAN_STABLE_OUTER_ANGLE.md gives
\[
\phi_+-\phi_->\delta_0:=\pi/4-1/500.
\]
It follows that
\[
\phi_-<-\pi/3-\delta_0
=-\pi/2-\tau,\qquad
\phi_+>-2\pi/3+\delta_0
=-\pi/2+\tau,
\]
where
\[
\tau=\pi/12-1/500>0.                         \tag{4}
\]
Thus the left D center has negative x and the right
D center has positive x. Each has center angular
deviation from -y strictly greater than \(\tau\).

For the quantitative margin, use
\[
t=\tan(\pi/12)=2-\sqrt3
\in(267/1000,3/10).
\]
The rational bounds follow from
\((1733/1000)^2>3>(17/10)^2\).
Also \(\tan(1/500)<1/250\), by
\(\tan'(x)=\sec^2 x<2\) on \([0,1/500]\).
The tangent subtraction identity gives the
**exact rational lower comparison**
\[
\tan\tau=\frac{t-\tan(1/500)}
 {1+t\tan(1/500)}
>\frac{267/1000-1/250}
 {1+(3/10)(1/250)}
=\frac{1315}{5006}.                            \tag{5}
\]
Since each D center has \(-y_D>9/8\), its
transverse coordinate satisfies
\[
|x_D|=(-y_D)|\tan(\phi_D+\pi/2)|
>\frac98\,\tan\tau
>\frac98\cdot\frac{1315}{5006}
>\frac{29}{100}.
\]
The final positive rational difference is
\[
\frac98\cdot\frac{1315}{5006}
-\frac{29}{100}=\frac{5527}{1001200}>0.
\]
This proves (2) and the theorem. QED.

## Exact scope

The x-coordinate signs are **center** signs, not
entire-square quadrant memberships or a choice
of actual R-U/D pair-separating axis. The near-inner
hypothesis is essential: if U has an outer center,
its two-center angular argument must be reconsidered.
There is no claim that the narrowed S2/k4 case is
realizable at the sharp radius, nor is the
unrestricted \(R_8\ge\widehat R\) proved.

[verify_s2_transverse_center_anchors.py](verify_s2_transverse_center_anchors.py)
audits the integer/squared-rational margins in
(3) and (5); the continuous angular reasoning is
given here, not delegated to the script.
