# Computer-guided hand theorem: the sharp cap envelope holds for h>=1/3

**Status:** complete arbitrary-frame analytic proof at the established
n=8 disk ceiling. This strengthens HUMAN_CAP_ENVELOPE_37_100.md
from h>=37/100 to **h>=1/3**. It must NOT be extrapolated
to h>=7/24: RATIONAL_DIAGONAL_CAP_ENVELOPE_COUNTEREXAMPLE.md
gives an actual rotated square disproving that extension at h=293/1000.

## Theorem

Let a genuine unit square S of arbitrary orientation, with
center (x,y), lie wholly inside
\[
D_R\cap\{x\ge h\},\qquad R^2\le q_+:=9789/2500,\quad h\ge1/3.
\]
Then the sharp axis-aligned cap-envelope inequality holds:
\[
\boxed{R^2\ge(1+h)^2+(|y|+1/2)^2.}               \tag{E}
\]
No assumption of square contact or frame alignment is used.

## 1. Prove a rational feasible-parameter polygon independently

Reflect y to assume y>=0. Write unsigned frame tilt
0<=theta<=pi/4, c=cos(theta), s=sin(theta),
L=c+s and D=c-s. The square's center x obeys
x>=h+L/2. Its (1,1) support is exactly c,
for either sign of the square tilt, giving
\[
\max_{v\in S}(v_x+v_y)
\ge h+y+(3c+s)/2\ge h+y+\sqrt2.
\]
The last bound follows because 3c+s is concave in theta
with endpoint values 3 and 2sqrt2. The disk
bound \(q_+<98/25\) then yields
\[
\boxed{h+y<14/5-\sqrt2<7/5.}                    \tag{1}
\]

**New independent height bound:**
\[
\boxed{y<Y:=49/50.}                              \tag{2}
\]
Proof: suppose y>=Y. For each frame sign choose the following
**true square vertex**, evaluating its squared norm at the
minimal possible center x=h+L/2. Increasing x,h,y
only increases the selected positive-coordinate vertex norms.

For negative tilt e=(c,-s),f=(s,c), use
\(V_-=(h+L,y+D/2)\). Its squared norm \(Q_-\)
has strictly negative second derivative
\[
Q_-''=-2hL-6cs-yD<0.
\]
Its *minimum* on [0,pi/4] is therefore at an endpoint:
\((h+1)^2+(y+1/2)^2\) at zero tilt and
\((h+\sqrt2)^2+y^2\) at diagonal tilt.

For positive tilt e=(c,s),f=(-s,c), use the actual
top vertex \(V_{\rm top}=(h+c,y+L/2)\).
Its squared norm has
\[
Q_{\rm top}''=-2(c^2-s^2)-2hc-2cs-yL<0.
\]
At zero tilt it has the same first endpoint; at diagonal
tilt it equals \(h^2+y^2+1+(h+y)\sqrt2\).

At **h=1/3,y=49/50**, the three endpoint quantities
exceed q_+ by at least respectively
\[
1183/22500,\quad277/5625,\quad347/45000>0.
\]
These bounds use only
\(\sqrt2>7/5\) and \(\sqrt2>141/100\),
both verified by squaring. Strict vertex concavity
therefore excludes y>=49/50 for either frame sign,
proving (2) **without invoking (E)**.

Consequently all admissible (h,y) lie inside
the **closed rational quadrilateral**
\[
h\ge1/3,\quad y\ge0,\quad y\le49/50,\quad
h+y\le7/5,
\]
with vertices
\[
(1/3,0),\ (7/5,0),\ (1/3,49/50),\ (21/50,49/50).
                                                               \tag{3}
\]
Passing to the closed polygon only strengthens the
positivity check below.

## 2. Negative tilt: a two-endpoint concavity certificate

Put \(q_{\rm axis}=(h+1)^2+(y+1/2)^2\).
The actual negative-tilt rightmost vertex norm Q_-
is strictly concave in theta and equals q_axis at theta=0.
At theta=pi/4,
\[
Q_- - q_{\rm axis}
=2h(\sqrt2-1)+3/4-y
>2(1/3)(2/5)+3/4-49/50
=\boxed{11/300>0}.
\]
Thus \(Q_-\ge q_{\rm axis}\) for every
negative tilt, with strict excess at nonzero tilt.

## 3. Positive tilt: exact four-vertex polynomial certificate

For the positive tilt sign use two **actual true vertices**,
evaluated at the minimal permitted center x:
\[
V_{\rm top}=(h+c,y+L/2),\qquad
V_{\rm right}=(h+L,y-D/2).
\]
Let \(Q_{\rm top},Q_{\rm right}\) be their squared norms.
The maximum true-vertex norm squared is at least
\(c^2Q_{\rm top}+s^2Q_{\rm right}\).
Set \(z=\tan(\theta/2)\in[0,\sqrt2-1]\subset[0,1/2]\).
An **exact polynomial identity** (directly checkable by
expansion) is
\[
c^2Q_{\rm top}+s^2Q_{\rm right}-q_{\rm axis}
=\frac{z(1-z)}{(1+z^2)^4}P_{h,y}(z),
\]
where the degree-six polynomial is **affine in (h,y)**:
\[
\begin{aligned}
P_{h,y}(z)={}&h(4z^6+4z^5+16z^4+12z^2-4z)\\
&+y(2z^6-2z^4-8z^3-2z^2-8z+2)\\
&+(z^5+5z^4+14z^3+6z^2-3z+1).
\end{aligned}                                      \tag{4}
\]
It is enough to prove P>0 at the **four**
(h,y) vertices in (3). The following finite table
provides a rigorous rational certificate, not sampled
function values.

For each interval [a,b], substitute z=a+(b-a)t
and write the degree-six polynomial in the
**Bernstein basis**:
\[
P(a+(b-a)t)=\sum_{k=0}^{6}
 b_k\binom6k t^k(1-t)^{6-k},\qquad 0\le t\le1.
\]
All seven basis functions are nonnegative and
sum to one. The table reports the **minimum of
all seven exact Bernstein coefficients b_k**
on each rational subinterval. Thus P is at least
the displayed strictly positive rational number
**throughout the continuum** of the interval.

| (h,y) | z subinterval | min Bernstein coefficient |
| --- | --- | ---: |
| (1/3,0) | [0,1/2] | 4/9 |
| (7/5,0) | [0,1/4] | 3601/19200 |
| (7/5,0) | [1/4,1/2] | 779/1280 |
| (1/3,49/50) | [0,1/4] | 169331/307200 |
| (1/3,49/50) | [1/4,3/8] | 278637/6553600 |
| (1/3,49/50) | [3/8,1/2] | 173087/18432000 |
| (21/50,49/50) | [0,1/4] | 54823/102400 |
| (21/50,49/50) | [1/4,1/2] | 29/4000 |

The independent exact-fraction script
[verify_cap_envelope_one_third.py](verify_cap_envelope_one_third.py)
constructs P from (4), expands **all 56**
rational Bernstein coefficients, checks that
the eight subintervals cover [0,1/2] for their
respective vertices, and checks every displayed
strict positive minimum. The argument for
positivity **between endpoints** is the
explicit Bernstein-basis identity, not a grid.

Affinity in (h,y) transfers this strict positivity
to the entire quadrilateral (3). Therefore the
weighted average of two **true positive-tilt
vertex norms** is at least q_axis, strictly
larger at nonzero tilt. At theta=0 the
axis-parallel true top-right vertex has norm q_axis.

Finally, if the actual square center x exceeds its
minimum h+L/2, the selected vertices' x coordinates
are all positive; their squared norms only increase.
Thus in both frame signs, at any center, the
**farthest actual true vertex** has squared norm
at least q_axis. Disk containment gives
\(R^2\ge q_{\rm axis}\). Reflect y to
remove the y>=0 normalization. This proves (E). QED.

## Scope

The strict offset threshold h>=1/3 and disk
ceiling \(R^2\le q_+\) are essential premises of
the **current hand certificate**. At h=293/1000,
an actual 45-degree whole-cap unit square violates
(E) while satisfying the same radius ceiling;
see the companion rational/radical counterexample.

This proof uses exact true-square vertices,
orientation-independent concavity, a finite
rational polynomial certificate and no
sampling-based step. It is **not** a proof of
the unrestricted n=8 sharp packing bound,
global equality classification or Lean formalization.
