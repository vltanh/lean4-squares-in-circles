# Sharp one-square cap envelope extends analytically to h>=79/250

**Status: complete arbitrary-frame hand theorem at the n=8 radius
ceiling**, strengthened from the prior h>=8/25 note by
an exact rational Bernstein certificate. Research 2026-10-12.

## Theorem

For any genuine unit square with independent arbitrary frame,
center p=(x,y), whole-cap containment
\(S\subseteq D_R\cap\{x\ge h\}\),
\[
R^2\le9789/2500,\qquad \boxed{h\ge79/250},
\]
implies the **sharp axis-aligned cap envelope**
\[
\boxed{R^2\ge(1+h)^2+(|y|+1/2)^2.}                \tag{E}
\]
The disk ceiling is part of this theorem. This *same one-square*
inequality is false at h=3/10: see the exact genuine rotated
unit-square counterexample
RATIONAL_ROTATED_CAP_ENVELOPE_THREE_TENTHS.md.

## 1. The true-vertex reduction and global parameter bound

Reflect in x to assume y>=0. Let the unsigned
frame tilt be theta in [0,pi/4], with
c=cos(theta), s=sin(theta), L=c+s, D=c-s.
The whole cap forces center x>=h+L/2.

For either frame sign, the **actual square's**
(1,1) supporting value is c. By concavity
of 3c+s between its endpoints 3 and 2sqrt2,
\[
\max_{v\in S}(v_x+v_y)\ge h+y+\sqrt2.
\]
Disk containment and q_+=9789/2500<98/25 imply
\[
\boxed{h+y<7/5}.                                  \tag{1}
\]

At the minimal center x=h+L/2 the following
are *actual true unit-square vertices*:

* Negative frame e=(c,-s), f=(s,c):
  \(V_-=(h+L,y+D/2)\).
* Positive frame e=(c,s),f=(-s,c):
  \(V_{\rm top}=(h+c,y+L/2)\) and
  \(V_{\rm right}=(h+L,y-D/2)\).

All selected x-coordinates are strictly positive,
so moving the actual center x to the right
only increases these squared vertex norms.

For negative tilt, \(Q_-=|V_-|^2\) has
\[
Q_-''=-2hL-6cs-yD<0.
\]
At theta=0 its value is
\(q_{\rm axis}=(h+1)^2+(y+1/2)^2\);
at theta=pi/4 its value is
\((h+\sqrt2)^2+y^2\).
For positive tilt, the maximum of the true
vertex norms is at least the weighted average
\(c^2 Q_{\rm top}+s^2 Q_{\rm right}\).

## 2. A finite all-angles rational Bernstein certificate

Set \(z=\tan(\theta/2)\in[0,\sqrt2-1]\subset[0,1/2]\).
The exact two-vertex identity (verified by direct expansion,
and used in the previous 8/25 hand proof) is
\[
c^2 Q_{\rm top}+s^2Q_{\rm right}-q_{\rm axis}
=\frac{z(1-z)}{(1+z^2)^4}P_{h,y}(z)
\]
with the degree-six polynomial **affine in h,y**
\[
\begin{aligned}
P_{h,y}(z)={}&h(4z^6+4z^5+16z^4+12z^2-4z)\\
&+y(2z^6-2z^4-8z^3-2z^2-8z+2)\\
&+(z^5+5z^4+14z^3+6z^2-3z+1).
\end{aligned}                                    \tag{2}
\]

Put \(H=79/250,\ Y=49/50\).
An **independent exact arithmetic certificate** proves
\(P_{h,y}(z)>0\) throughout the closed quadrilateral
\[
\mathcal Q:\quad h\ge H,\quad 0\le y\le Y,\quad
h+y\le7/5,
\]
whose four parameter vertices are
\[
(H,0),\quad(7/5,0),\quad(H,Y),\quad(21/50,Y).
                                                               \tag{3}
\]

Because P is affine in h and y, it is enough to verify
the **four** parameter vertices. For each rational
z interval [a,b], substitute z=a+(b-a)t and expand
P in the **degree-six Bernstein basis**
\[
P(a+(b-a)t)=\sum_{k=0}^6 b_k\binom6k t^k(1-t)^{6-k},
\quad0\le t\le1.
\]
All basis functions are nonnegative and sum to one;
hence P is at least the **minimum of its seven
exact Bernstein coefficients** throughout the
entire interval. The exact minima are:

| Parameter vertex (h,y) | z interval | min Bernstein coefficient |
| --- | --- | ---: |
| (79/250,0) | [0,1/2] | 1697/3750 |
| (7/5,0) | [0,1/4] | 3601/19200 |
| (7/5,0) | [1/4,1/2] | 779/1280 |
| (79/250,49/50) | [0,1/4] | 283839/512000 |
| (79/250,49/50) | [1/4,3/8] | 1083811/32768000 |
| (79/250,49/50) | [3/8,7/16] | 4322111/1310720000 |
| (79/250,49/50) | [7/16,1/2] | 14654007/419430400 |
| (21/50,49/50) | [0,1/4] | 54823/102400 |
| (21/50,49/50) | [1/4,1/2] | 29/4000 |

Every minimum is **strictly positive**.
[verify_cap_envelope_79_250.py](verify_cap_envelope_79_250.py)
reconstructs all four polynomials from (2)
and checks **all 63 Bernstein coefficients**
and the complete intervals in exact rational
arithmetic. This is a finite hand-understandable
positivity proof, **not** a numerical sample
or a numerical optimizer's success claim.

## 3. Noncircular y-height restriction

We use the **top-edge certificate above** first
to prove, *without assuming the desired envelope*,
\[
\boxed{y<Y=49/50}.                                 \tag{4}
\]
Suppose y>=Y. Then (1) forces H<=h<=7/5-Y=21/50.

For a **negative frame**, evaluate the true vertex
Q_- at the smaller ordinate Y. Its strict concavity
puts Q_- above its lesser theta endpoint.
At h=H, y=Y, those endpoint values exceed
\(q_+=9789/2500\) by respectively
\[
104/15625>0,\qquad5969/250000>0,
\]
where the diagonal endpoint uses
\(\sqrt2>141/100\).
They increase with h. Raising y>=Y only
increases the selected true vertex norm
since y+D/2 is positive. Disk containment
would be violated.

For a **positive frame**, at y=Y and
h∈[H,21/50], the two *top-edge Bernstein
certificates* at (H,Y) and (21/50,Y)
imply by affine interpolation that
P_{h,Y}(z)>0 for all z in [0,1/2].
The true-vertex weighted squared norm is
therefore at least
\[
q_{\rm axis}(h,Y)\ge q_{\rm axis}(H,Y)
=q_++104/15625>q_+.
\]
Raising the actual y from Y only increases
**both** chosen true-vertex squared norms:
their positive y-coordinates are
y+L/2 and y-D/2>Y-1/2>0.
Increasing x also increases both norms.
Thus disk containment again fails.
This proves (4) **noncircularly**:
the top-edge polynomial certificate is an
independent rational identity, proved in
section 2 before (4).

## 4. Deduce the full envelope

By (1),(4), every feasible (h,y) belongs
to the quadrilateral (3), where the
**entire** Bernstein certificate gives P>0.

For the **positive** frame, the exact
weighted true-vertex identity gives a
squared vertex norm at least q_axis.
For the **negative** frame the rightmost
actual vertex Q_- is concave in theta,
equals q_axis at zero tilt, and its
diagonal endpoint has the strictly
positive excess
\[
2h(\sqrt2-1)+3/4-y
>2H(2/5)+3/4-Y
=\boxed{57/2500>0}.
\]
Thus Q_->=q_axis for all theta.
If the actual center x is farther right than
the cap minimum, all selected squared
vertex norms only increase.

Therefore the **maximum true vertex**
squared norm is at least q_axis for
every frame and position. Disk containment
gives (E). Reflecting y removes the y>=0
normalization. QED.

## Exact scope and computational guardrail

The one-square inequality is now proved at
\(h\ge79/250=0.316\) in the n=8 disk ceiling.
It is **false at h=3/10=0.30** by the
strict rational rotated-square witness.
This is an important obstacle to extending
the same one-square technique all the way
to the required S2/k4 lower endpoint 7/24.
Further progress there must exploit the
**mixed inner/outer two-square geometry**
and true separating axes.

The theorem has no global n=8 optimality,
equality or Lean 4 conclusion by itself.
