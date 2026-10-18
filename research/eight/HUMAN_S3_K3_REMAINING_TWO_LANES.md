# The surviving S3/k=3 strip has two outer-R angular lanes and two far-singleton corridors

Research continuation, 2026-10-12. This note records **actual
continuous-domain pruning**, not a claim that the S3/k=3 branch
is impossible. It combines the just-proved
[HUMAN_FIVE_SQUARE_INNER_OUTER_FAN.md](HUMAN_FIVE_SQUARE_INNER_OUTER_FAN.md)
with existing full-frame cap theorems, and avoids silently assigning
parallel square frames.

## Statement

Let eight disjoint-interior unit squares fit in \(D_R\) with
\(R^2\le9789/2500\), with unique central origin-containing square C.
Assume all seven exterior squares have **exclusive, exactly one**
central-owned whole-square side statuses S3=(3+1,2+1).
After symmetries normalize
\[
R:3,\quad L:1,\quad U:2,\quad D:1.
\]
Assume exactly **k=3 outer exterior centers** (norm \(\ge1\)).
Write \(h_R,h_U>0\) for the offsets of the R and U central sides.

Then the *only as-yet-unexcluded* parameter region satisfies
\[
\boxed{17/200<h_R<13/100,\qquad
17/200<h_U<21/100.}                            \tag{1}
\]

There are exactly two inner R centers, two inner U centers,
and three outer centers (one R member and the distinct L,D
singletons). If \(\psi\) denotes the polar center-ray angle
of the **outer** R-member, then
\[
\boxed{
\psi\in(-5\pi/36,-2\pi/45)
\;\;\cup\;\;
(7\pi/36,13\pi/45).
}                                                   \tag{2}
\]
Thus its only possible angular sectors are
**strictly between -25 and -8 degrees**, or
**strictly between 35 and 52 degrees**.
No assertion is made that either sector actually contains
a realizable eight-square packing.

The far singleton center transverse coordinates satisfy
\[
\boxed{|p_L.y|<3/20,\qquad |p_D.x|<11/32.}          \tag{3}
\]
Consequently L's ray is within \(\pi/24\) of the
negative x-axis, and D's ray is within \(\pi/12\)
of the negative y-axis.

## Proof of the exact offset strip

The R triple has a far opposite L singleton.
By the arbitrary-orientation one-square cap
envelope for L,
\[
(2-h_R)^2+1/4\le q_+,
\]
so \(h_R>17/200\); at \(h_R=17/200\),
the left side exceeds q_+ by 13/8000.
Similarly, the far D singleton forces \(h_U>17/200\).

Since L and D have far-cap normal projections greater
than one, they are distinct **outer** centers.
The R triple has at least one outer center by the
triple-inner cap lemma. With k=3, it has *exactly*
one outer, two inner; both U centers are inner.
If \(h_R\ge13/100\), the previously proved
HUMAN_TRIPLE_CAP_TWO_OUTER_IMPROVED.md
forces two outer R centers and hence k>=4.
Thus \(h_R<13/100\).

Finally HUMAN_FIVE_SQUARE_INNER_OUTER_FAN.md
excludes **every** such five-square R/U configuration
with \(h_R>17/200\) and \(h_U\ge21/100\).
Therefore \(h_U<21/100\).
This proves (1) without assuming a contact graph.

## Proof of the outer R angular dichotomy

For the four distinct inner R/U labels, put
\[
\alpha=\arcsin(h_U+1/2)>
\arcsin(117/200)>11\pi/60.
\]
For the last inequality, use
\(\sin x<x\) for \(x>0\),
\(\pi<22/7\), and
\[
11\pi/60<121/210<117/200.
\]

Write the inner center-ray angles \(R_-,R_+,U_+,U_-\)
as in the four-inner fan lemma.
Their exact angular order gives
\[
-\pi/3<\theta_{R_-}<-\alpha,\quad
0<\theta_{R_+}<\pi/3-\alpha<3\pi/20,\quad
\pi/3<\theta_{U_+}<2\pi/3-\alpha.
\]
Each of these three inner centers has radial norm
**strictly greater** than \(117/200\).
This is immediate from the R+ and U+ whole-cap
center projections. For R- one has
\(r>\tfrac12/\cos\alpha>
100/\sqrt{26311}>117/200\);
the last inequality is
\(400000000-117^2\cdot26311=39828721>0\).

Let \(\psi\) be the outer R center angle. Its
x projection is \(>117/200\), its radius is
\(<283/200\), and therefore
\[
|\psi|<3\pi/8
\]
by the exact comparison
\(117/283>2/5>\cos(3\pi/8)\).
The mixed inner/outer angular lemma in
HUMAN_FIVE_SQUARE_INNER_OUTER_FAN.md proves
that **every** center of norm \(>117/200\) and
\(<1\) is separated in angle by more than
\(7\pi/36\) from every outer center in the
radius ceiling.

The outer R ray cannot lie **below** R-:
such a gap would be
\[
<3\pi/8-\alpha
<3\pi/8-11\pi/60=23\pi/120<7\pi/36.
\]
Nor can it lie **above** U+, since that gap
would be \(<3\pi/8-\pi/3=\pi/24<7\pi/36\).
Hence it lies between those rays, and
\[
\psi>\theta_{R_-}+7\pi/36>-5\pi/36,
\quad
\psi<\theta_{U_+}-7\pi/36
<17\pi/36-\alpha<13\pi/45.                    \tag{4}
\]

But the outer R ray is also more than \(7\pi/36\)
away from the inner R+ ray, whose angle
lies in \((0,3\pi/20)\).
Thus either
\[
\psi<\theta_{R_+}-7\pi/36
<3\pi/20-7\pi/36=-2\pi/45,
\]
or
\[
\psi>\theta_{R_+}+7\pi/36>7\pi/36.
\]
Combining with (4) yields exactly (2). QED.

## Proof of the far singleton center corridors

The L square lies in the *whole* far left cap
\(x\le-(1-h_R)\), with offset \(1-h_R>87/100\).
Apply the arbitrary-frame one-square cap envelope
in HUMAN_ONE_SQUARE_CAP_ENVELOPE.md, then (1):
\[
(|p_L.y|+1/2)^2
\le q_+-(2-h_R)^2
<q_+-(187/100)^2=4187/10000
<(13/20)^2,
\]
the last positive rational squared margin
being \(19/5000\).
Hence \(|p_L.y|<3/20\).
Also \(-p_L.x\ge3/2-h_R>137/100\), so
\[
|p_L.y/p_L.x|<15/137<1/9
<\tan(\pi/24),
\]
where \(\tan x>x\) on \((0,\pi/2)\)
and \(\pi/24>1/8>1/9\).
Thus L is within \(\pi/24\) of the negative x-axis.

Similarly D has offset \(1-h_U>79/100\).
The same cap envelope yields
\[
(|p_D.x|+1/2)^2
<q_+-(179/100)^2
=1423/2000<(27/32)^2,
\]
with strict margin \(53/128000>0\).
Therefore \(|p_D.x|<11/32\), while
\(-p_D.y\ge3/2-h_U>129/100\).
Consequently
\[
|p_D.x/p_D.y|
<275/1032<2-\sqrt3=\tan(\pi/12).
\]
The rational radical comparison is exact:
\(1789^2-3\cdot1032^2=5449>0\).
This places D's ray strictly in
\((-7\pi/12,-5\pi/12)\) and proves (3). QED.

## What remains after this pruning

The low-k S3 case has **not** been excluded: its remaining
offset rectangle (1), the two *disjoint* outer R angular
sectors (2), the two distant-singleton corridors (3),
and the original inner-ray fan still contain continuous
square centers, orientations, and pair separators.
In particular the center-ray constraints are **not**
full-square quadrant memberships.

A next sharp proof should combine the R triple's
**actual inter-square separating axes** with these
narrow angular lanes and far-cap disk vertex bounds.
No numerical candidate, fractional-center relaxation,
or merely positive center coordinate establishes
the missing \(R_8\ge\widehat R\).
