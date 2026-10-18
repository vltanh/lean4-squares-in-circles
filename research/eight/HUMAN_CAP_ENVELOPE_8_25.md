# Stronger computer-to-hand cap envelope: h>=8/25

**Status: complete analytical arbitrary-frame hand theorem**
at the eight-square search ceiling. Research continuation 2026-10-12.
This strictly improves HUMAN_CAP_ENVELOPE_ONE_THIRD.md from
h>=1/3 to **h>=8/25**. Its height bound is proved
**noncircularly** by using a rational polynomial certificate on
the top parameter edge *before* using that height bound.

## Theorem

If a genuine unit square S of any independently chosen frame, with
center p=(x,y), is contained in
\[
D_R\cap\{x\ge h\},\quad
R^2\le q_+:=9789/2500,\quad h\ge8/25,
\]
then the sharp axis-aligned one-square cap envelope holds:
\[
\boxed{R^2\ge(1+h)^2+(|y|+1/2)^2.}             \tag{E}
\]
The disk-ceiling premise is essential to the current proof. The
envelope **is false at h=3/10**, even below q_+; see
RATIONAL_ROTATED_CAP_ENVELOPE_THREE_TENTHS.md.

## 1. Global cap parameter bound and true square vertices

Reflect in the x axis to assume y>=0. Normalize the frame to
positive or negative tilt with unsigned angle theta in [0,pi/4].
Put c=cos(theta), s=sin(theta), L=c+s, D=c-s.
The whole-cap center projection is
\(x\ge h+L/2\).

For either tilt sign the true square's (1,1) support is c,
and 3c+s is concave with endpoint minimum 2sqrt2, so
\[
\max_{v\in S}(v_x+v_y)
\ge h+y+(3c+s)/2\ge h+y+\sqrt2.
\]
The containing disk and q_+<98/25 give
\[
\boxed{h+y<7/5}.                                \tag{1}
\]
This uses true support geometry and **not** the envelope (E).

For later use define the following *actual* vertices at
the **minimal permitted** center x=h+L/2:

* Negative tilt e=(c,-s), f=(s,c):
  \(V_-=(h+L,y+D/2)\).
* Positive tilt e=(c,s), f=(-s,c):
  \(V_{\rm top}=(h+c,y+L/2)\),
  \(V_{\rm right}=(h+L,y-D/2)\).

All selected vertex x coordinates are positive, so moving the
actual center x to the right only **increases** their squared norms.
For the negative frame, the squared norm Q_- of V_- has
\[
Q_-''=-2hL-6cs-yD<0.                             \tag{2}
\]
For the positive frame, the top vertex squared norm Q_top
has \(Q_{\rm top}''=-2(c^2-s^2)-2hc-2cs-yL<0\).
These are exact differentiations on theta in [0,pi/4].

## 2. Independent exact polynomial positivity certificate

Set
\[
z=\tan(\theta/2)\in[0,\sqrt2-1]\subset[0,1/2],
\quad q_{\rm axis}=(h+1)^2+(y+1/2)^2.
\]
A direct expansion of **the two actual positive-frame
vertices**, using c=(1-z²)/(1+z²), s=2z/(1+z²), gives
\[
c^2|V_{\rm top}|^2+s^2|V_{\rm right}|^2-q_{\rm axis}
=\frac{z(1-z)P_{h,y}(z)}{(1+z^2)^4},             \tag{3}
\]
where P is **affine in h,y**:
\[
\begin{aligned}
P_{h,y}(z)={}&h(4z^6+4z^5+16z^4+12z^2-4z)\\
&+y(2z^6-2z^4-8z^3-2z^2-8z+2)\\
&+(z^5+5z^4+14z^3+6z^2-3z+1).
\end{aligned}                                    \tag{4}
\]

We prove by a finite **exact rational Bernstein certificate** that
\[
\boxed{P_{h,y}(z)>0}
\]
on the **closed quadrilateral**
\[
\mathcal P=\{h\ge8/25,\ y\ge0,\ y\le39/40,\
h+y\le7/5\}
\]
with vertices
\[
(8/25,0),\ (7/5,0),\
(8/25,39/40),\ (17/40,39/40).                  \tag{5}
\]

Because P is affine in h,y, verifying its four
vertices suffices. For each rational interval [a,b],
write \(z=a+(b-a)t\) and expand P in the degree-six
Bernstein basis
\[
P(a+(b-a)t)=\sum_{k=0}^6 b_k\binom6k t^k(1-t)^{6-k},
\quad0\le t\le1.
\]
The basis is nonnegative and sums to one. The table
records the **minimum of all seven exact Bernstein
coefficients** on each subinterval; hence the entire
continuum has P at least the tabulated positive value.

| (h,y) | z subinterval | min Bernstein coefficient |
| --- | --- | ---: |
| (8/25,0) | [0,1/2] | 169/375 |
| (7/5,0) | [0,1/4] | 3601/19200 |
| (7/5,0) | [1/4,1/2] | 779/1280 |
| (8/25,39/40) | [0,1/4] | 227299/409600 |
| (8/25,39/40) | [1/4,3/8] | 1151851/26214400 |
| (8/25,39/40) | [3/8,1/2] | 202921/24576000 |
| (17/40,39/40) | [0,1/4] | 43889/81920 |
| (17/40,39/40) | [1/4,1/2] | 923/51200 |

Every entry is strictly positive.
[verify_cap_envelope_8_25.py](verify_cap_envelope_8_25.py)
independently constructs the four polynomials and checks
**all 56 exact Bernstein coefficients**, not sampled z values.
The Bernstein-basis identity is the hand proof that
the positivity holds **between** the endpoints.

## 3. Crucial: establish y<39/40 without circularity

Put H=8/25, Y=39/40. We now prove
\[
\boxed{y<Y},                                     \tag{6}
\]
using only (1), the **independent algebraic
certificate (5)**, and true square vertices.
Suppose y>=Y. Then (1) forces
\[
H\le h\le7/5-Y=17/40.
\]

**Negative-frame case.** Evaluate Q_- at y=Y
and the actual h. Because (2) is strictly
negative, its minimum over theta is at an
endpoint. At zero tilt the vertex squared norm is
\((h+1)^2+(Y+1/2)^2\); at diagonal tilt it is
\((h+\sqrt2)^2+Y^2\). At h=H the first
exceeds q_+ by **97/40000** and the
second by **more than 1117/40000**, using
the elementary bound sqrt2>141/100.
Both endpoint values increase with h.
The actual chosen negative-frame vertex norm
also increases when its y coordinate is raised
above Y because \(y+D/2>0\).
Thus any actual y>=Y contradicts disk containment.

**Positive-frame case.** For y=Y and
H<=h<=17/40, P_{h,Y}(z)>0 for all allowed
z **already follows from the two top-edge
vertex Bernstein rows**, by affine interpolation
in h. The identity (3) hence shows that
the *weighted average of two true vertex
squared norms* is at least
\[
q_{\rm axis}(h,Y)\ge q_{\rm axis}(H,Y)
=q_++\frac{97}{40000}>q_+.
\]
Raising the actual center ordinate y above Y
only increases **both** selected true-vertex
squared norms because their y coordinates
\(y+L/2\) and \(y-D/2\) are positive for y>=Y.
Moving the center x right also increases them.
Therefore any y>=Y again contradicts disk
containment. This establishes (6) for both
frame signs.

**There is no circular argument:** the top-edge
polynomial positivity is an unconditional
finite integer calculation, proved in Step 2
before the height assertion (6).

## 4. Complete the full orientation inequality

By (1) and (6), all actual (h,y) lie in
the quadrilateral (5), so the full
Bernstein certificate gives P>0.

For the **positive frame**, (3) shows that
the maximum squared norm of its two *actual
vertices* is >=q_axis, with strict excess
for theta>0. At theta=0 the true axis-parallel
top-right vertex has squared norm q_axis.

For the **negative frame**, the rightmost
actual vertex squared norm Q_- is concave by
(2) and equals q_axis at theta=0. At the
diagonal endpoint its excess over q_axis is
\[
2h(\sqrt2-1)+3/4-y
>2(8/25)(2/5)+3/4-39/40
=\boxed{31/1000>0}.
\]
Therefore negative-frame Q_->=q_axis for all
theta, strictly so at positive tilt.

Increasing the actual center x beyond the
minimal permitted cap coordinate only
increases all the selected true-vertex
squared norms, because their x values
are strictly positive. Thus in **every
frame and every actual position**,
the maximum true vertex squared norm is
at least q_axis. Disk containment yields
(E), and reflecting y proves the |y| form. QED.

## Scope and counterexample guardrail

This improves the previous 1/3 threshold to
**8/25** with a fully auditable hand certificate.
It does *not* reach the final S2/k4 mixed-cap
lower endpoint 7/24. The exact rational
rotated unit square at h=3/10 in
RATIONAL_ROTATED_CAP_ENVELOPE_THREE_TENTHS.md
disproves this **same single-square envelope**
below 8/25; merely extrapolating it to
h=3/10 or h=7/24 would be false.

The theorem can be applied to a further
mixed-inner/outer center-sign contradiction,
but it does not itself solve the
unrestricted eight-square radius inequality
\(R_8\ge\widehat R\), equality classification,
or Lean 4 formalization.
