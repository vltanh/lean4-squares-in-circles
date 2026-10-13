# Same-weak-sign mixed cap centers excluded at h>=79/250

**Status: complete arbitrary-orientation hand theorem with exact rational margins.**
Research continuation 2026-10-12. This improves the earlier
HUMAN_MIXED_HIGH_CAP_8_25.md bound h>=8/25 to the
new \(h\ge79/250=0.316\), by combining
[HUMAN_CAP_ENVELOPE_79_250.md](HUMAN_CAP_ENVELOPE_79_250.md)
with a coupled outer-center radial inequality.

## Theorem

Let two distinct genuine unit squares with disjoint open
interiors fit in a disk \(R^2\le q_+:=9789/2500\).
Suppose both **whole squares** lie beyond the same
outward cap line \(y=h\), with
\[
\boxed{h\ge79/250}.
\]
Let p be an **inner** center (\(|p|<1\)) and
q an **outer** center (\(|q|\ge1\)).
Then their transverse signed center x-coordinates
must be **strictly opposite**:
\[
\boxed{p_xq_x<0.}
\]
The theorem includes the zero-sign boundary,
and it holds for arbitrary independent unit-square frames.

## All-frame exact hand proof

If h>=1/2, the inner center cannot exist because
p_y>=h+1/2>=1. Thus take 79/250<=h<1/2.

Suppose p_xq_x>=0. Because h>=79/250>7/24,
the previous fully proved
[HUMAN_MIXED_NEAR_CAP_POLARITY.md](HUMAN_MIXED_NEAR_CAP_POLARITY.md)
applies. It handles the zero-sign boundary,
rules out q_x=0, and after reflecting x gives
\[
0\le p_x<1/4,\qquad q_x>7/10.                 \tag{1}
\]

Apply the new **sharp all-orientation one-square
cap envelope** to the whole *outer* square:
\[
(1+h)^2+(q_x+1/2)^2\le q_+.
\]
Put \(H=79/250\) and \(X=489/500\).
The exact positive comparison is
\[
(1+H)^2+(X+1/2)^2-q_+
=\boxed{37/50000>0}.
\]
Thus the actual outer center must satisfy
\[
\boxed{7/10<q_x<X=489/500.}                  \tag{2}
\]

The whole-cap projections and the inner norm bound give
\[
a:=H+1/2=102/125\le p_y<1,\quad q_y\ge a.
\]
Every true unit square under the search ceiling has
center norm \(<r_0:=283/200\), so
\[
q_y<\sqrt{r_0^2-q_x^2}.
\]
Retain the **radial correlation** between
q_x and q_y. From (2) and the exact comparison
\[
r_0^2-(489/500)^2-(409/400)^2
=\boxed{939/4000000>0},
\]
we have
\[
\boxed{\sqrt{r_0^2-q_x^2}>C:=409/400.}       \tag{3}
\]

Since q_x>7/10>p_x>=0, its signed x separation
obeys \(0<q_x-p_x\le q_x\).
We now consider the two exhaustive center-y orders.

**If q_y>=p_y**, then
\(0\le q_y-p_y<\sqrt{r_0^2-q_x^2}-a\), giving
\[
\begin{aligned}
|q-p|^2
&<q_x^2+\big(\sqrt{r_0^2-q_x^2}-a\big)^2\\
&=r_0^2+a^2-2a\sqrt{r_0^2-q_x^2}\\
&<r_0^2+a^2-2a C\\
&=\boxed{999361/1000000<1}.
\end{aligned}
\]
The strict positive squared-distance reserve is
\(639/1000000\).

**If q_y<p_y**, then
\(0<p_y-q_y<1-a=23/125\), so
\[
|q-p|^2
<X^2+(1-a)^2
=\boxed{49517/50000<1}.
\]
The strict squared-distance reserve is \(483/50000\).

Both alternatives contradict \(|q-p|\ge1\),
which follows from the disjoint open inscribed
radius-1/2 disks of the two genuine unit squares.
Thus p_xq_x>=0 is impossible, proving the
strict opposite-center-sign conclusion. QED.

[verify_mixed_high_cap_79_250.py](verify_mixed_high_cap_79_250.py)
independently audits all the fractions and
strict positive margins. No numerical optimization
or unproved global feasibility classifier is used.

## Current S2/k4 consequence

In exclusive S2=(3+0,2+2), k=4, the
nearer 2+2 whole cap has precisely one
inner-center and one outer-center actual square,
with offset \(7/24<h_U<97/200\).
The newest **necessary** partition is now:

| Cell | h_U | Mixed center transverse signs |
| --- | --- | --- |
| A | \(79/250\le h_U<97/200\) | Strictly opposite |
| B | \(7/24<h_U<79/250\) | Strictly opposite |
| C | \(7/24<h_U<79/250\) | Weak same signs; preserve the previous whole-quadrant, inner/outer angle and frame-defect conditions |

This **excludes the entire former cell-C band
\([79/250,8/25)\)** in addition to all previous
higher-offset exclusions, for every true square frame.
The residual same-sign interval has width
\(79/250-7/24=73/3000\), strictly positive.
Cells A/B also remain open, with many
additional square-pair and central-placement constraints.

**Counterexample guardrail:** a single genuine
rational rotated square at offset h=3/10
violates the one-square envelope, even below
the search radius ceiling. This does *not*
contradict the new *mixed two-square* theorem,
which starts at h=79/250 and assumes
one inner and one outer center.

The unrestricted eight-square sharp inequality
\(R_8\ge\widehat R\), global equality
classification, and Lean proof remain OPEN.
