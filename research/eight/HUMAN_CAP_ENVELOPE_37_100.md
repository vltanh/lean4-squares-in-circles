# Computer-guided extension of the sharp one-square cap envelope to h>=37/100

**Status: complete analytic hand theorem at the n=8 search ceiling** (not a Lean
formalization). Research continuation 2026-10-12.

The numerical two-square optimization described in
[COMPUTER_ASSISTED_ATTACK_ROADMAP.md](COMPUTER_ASSISTED_ATTACK_ROADMAP.md)
suggested the axis-parallel cap geometry is extremal for *mixed*
inner/outer pairs. The exact analytic step extracted here is stronger
than a numerical observation: it extends the known one-square
arbitrary-frame envelope from [HUMAN_ONE_SQUARE_CAP_ENVELOPE.md](HUMAN_ONE_SQUARE_CAP_ENVELOPE.md)
at offset \(h\ge2/5\) down to \(h\ge37/100\) **under the already
established disk ceiling**.

## Theorem

Let a unit square S of *arbitrary* orientation lie wholly within
\[
D_R\cap\{x\ge h\},\qquad
R^2\le q_+:=9789/2500,\quad h\ge37/100.
\]
Write its actual center as \(p=(x,y)\). Then
\[
\boxed{R^2\ge(h+1)^2+(|y|+1/2)^2.}               \tag{E}
\]

No parallel-frame, physical-contact or stress hypothesis is used.
The restriction \(R^2\le q_+\) is essential to the *present proof* of
this lowered \(37/100\) threshold; the earlier \(2/5\) theorem has
the stronger stand-alone domain \(R^2\le98/25\).

### 1. Three exact preliminary bounds

Reflect in the x axis so \(y\ge0\). Normalize the unsigned frame angle
to \(0\le\theta\le\pi/4\), and put
\[
c=\cos\theta,\quad s=\sin\theta,\quad
L=c+s,\quad D=c-s.
\]
The full horizontal projection has width L, and hence the center
has \(x\ge h+L/2\), with \(1\le L\le\sqrt2\).

The disk and whole-cap condition already give
\[
\boxed{h+y<7/5.}                                 \tag{A}
\]
Indeed the true square support in direction (1,1) is c regardless
of the sign of the frame angle. Thus
\[
\max_{z\in S}(z_x+z_y)
\ge h+y+(3c+s)/2\ge h+y+\sqrt2.
\]
The last inequality holds on the whole angle interval because
\(3c+s\) is concave, with endpoint values 3 and \(2\sqrt2\).
On the other hand, the disk gives
\(\max(z_x+z_y)\le\sqrt2 R<14/5\).
Use \(\sqrt2>7/5\) to get (A).

We also have the following **new cap-specific bound**:
\[
\boxed{0\le y<1.}                                \tag{B}
\]
Here is a direct geometric proof *independent of the desired envelope*.
Suppose \(y\ge1\). Move the center's x coordinate down to its
minimal allowed value \(h+L/2\) when estimating the true vertices below.
Both selected vertex x coordinates are positive, so this only
decreases their squared norms. All selected y coordinates are positive,
so their squared norms increase with y. We may therefore replace
\(h\) by \(37/100\) and \(y\) by 1 to find universal lower bounds.

For the **negative frame angle** use the actual rightmost vertex
\[
V_-=(h+L,\ y+D/2),\quad Q_-=|V_-|^2.
\]
As established by direct differentiation in the original cap note,
\[
Q_-''(\theta)=-2hL-6cs-yD<0.
\]
Its minimum on \([0,\pi/4]\) is at an endpoint. At \(\theta=0\)
the squared norm is \((1+h)^2+(y+1/2)^2\), and at
\(\pi/4\) it is \((h+\sqrt2)^2+y^2\).
At \(h=37/100,y=1\), both endpoint values exceed \(q_+\):
the margins are respectively \(2113/10000>0\) and
more than \(2573/10000>0\), the latter using \(\sqrt2>7/5\).

For the **positive frame angle** use the actual top vertex
\[
V_{\rm top}=(h+c,\ y+L/2),\quad Q_{\rm top}=|V_{\rm top}|^2.
\]
Its exact second derivative is
\[
Q_{\rm top}''=
-2(c^2-s^2)-2hc-2cs-yL<0
\quad(0\le\theta\le\pi/4,\ h>0,\ y\ge0).
\]
Thus its minimum is again at an endpoint.
The value at \(\theta=0\) equals the previous
\(q_{\rm axis}=(1+h)^2+(y+1/2)^2\), and at \(\pi/4\)
it is
\[
h^2+2+(h+1)\sqrt2
\]
when \(y=1\).
At \(h=37/100,y=1\), the \(\theta=\pi/4\) value
exceeds \(q_+\) by more than \(1393/10000\),
again using \(\sqrt2>7/5\).
This contradicts disk containment in both frame-sign cases.
Therefore (B) is proved.

Finally, from (A),(B) we know \((h,y)\) lies in the
closed polygonal region with vertices
\[
(37/100,0),\quad(7/5,0),\quad(37/100,1),\quad(2/5,1).
                                                               \tag{C}
\]
Using the *closed* enclosing polygon only makes the next
uniform positivity check stronger.

### 2. Negative frame: a two-endpoint concavity proof

Define the axis-parallel comparison squared norm
\[
q_{\rm axis}=(h+1)^2+(y+1/2)^2.
\]
For a negative square-frame angle the rightmost actual vertex
\(V_-=(h+L,y+D/2)\) satisfies \(Q_-''<0\), as above.
At \(\theta=0\), \(Q_-=q_{\rm axis}\).
At \(\theta=\pi/4\),
\[
\begin{aligned}
Q_--q_{\rm axis}
&=2h(\sqrt2-1)+3/4-y\\
&>(2\sqrt2-1)h-13/20\\
&>(9/5)(37/100)-13/20\\
&=2/125>0,
\end{aligned}
\]
where we used \(h+y<7/5\) and \(\sqrt2>7/5\).
A concave function is at least the smaller of its two
endpoint values. Thus the actual farthest squared vertex norm
is \(\ge q_{\rm axis}\) in every negative frame,
strictly so away from \(\theta=0\).

### 3. Positive frame: an exact affine polynomial over four vertices

For a positive frame angle, two *actual* vertices at the
minimal allowed center x coordinate are
\[
V_{\rm top}=(h+c,\ y+L/2),\qquad
V_{\rm right}=(h+L,\ y-D/2).
\]
Write their squared norms as \(Q_{\rm top},Q_{\rm right}\).
They suffice because the maximum actual vertex norm squared
is at least \(c^2Q_{\rm top}+s^2Q_{\rm right}\).

Set \(z=\tan(\theta/2)\in[0,\sqrt2-1]\subset[0,1/2]\).
Using \(c=(1-z^2)/(1+z^2)\), \(s=2z/(1+z^2)\),
the direct polynomial identity from the original envelope
note is
\[
c^2Q_{\rm top}+s^2Q_{\rm right}-q_{\rm axis}
=\frac{z(1-z)P_{h,y}(z)}{(1+z^2)^4},
\]
where \(P_{h,y}\) is **affine** in h and y:
\[
\begin{aligned}
P_{h,y}(z)={}&h(4z^6+4z^5+16z^4+12z^2-4z)\\
&+y(2z^6-2z^4-8z^3-2z^2-8z+2)\\
&+(z^5+5z^4+14z^3+6z^2-3z+1).
\end{aligned}
\]

By affinity, it is enough to prove \(P>0\)
on the four vertices (C). Here is a complete exact rational
positivity certificate, no angular samples:

* **(37/100,0).** The polynomial is
  \[
  1-\frac{112}{25}z+\frac{261}{25}z^2
  +14z^3+\frac{273}{25}z^4+\frac{62}{25}z^5+\frac{37}{25}z^6.
  \]
  Its quadratic part is everywhere strictly positive,
  with discriminant \(-13556/625<0\); all higher
  coefficients are nonnegative.
* **(7/5,0).** The quadratic part is
  \(1-(43/5)z+(114/5)z^2\),
  with discriminant \(-431/25<0\).
  Every higher coefficient is positive.
* **(37/100,1).** The polynomial
  \[
  P_C=\frac{87}{25}z^6+\frac{62}{25}z^5+
  \frac{223}{25}z^4+6z^3+
  \frac{211}{25}z^2-\frac{312}{25}z+3
  \]
  has \(P_C''(z)>0\) for \(z\ge0\).
  Its tangent at \(a=2/5\) is the strict lower bound
  \[
  P_C(z)\ge \frac{1851}{78125}
              -\frac{2596}{78125}z
  \ge\frac{553}{78125}>0
  \quad(0\le z\le1/2).
  \]
* **(2/5,1).** The polynomial
  \[
  P_D=\frac{18}{5}z^6+\frac{13}{5}z^5+
  \frac{47}{5}z^4+6z^3+\frac{44}{5}z^2
  -\frac{63}{5}z+3
  \]
  has \(P_D''(z)>0\) for \(z\ge0\).
  Its tangent at \(a=79/200\) is
  \[
  P_D(z)\ge
  \frac{1041716561351}{32000000000000}
  +\frac{761606023}{400000000000}z>0.
  \]

Every \((h,y)\) satisfying (A),(B) is a convex combination
of the four vertices (C), so \(P_{h,y}(z)>0\) for
every allowed \(z\).
The weighted sum of two *true vertex* squared norms
is therefore at least \(q_{\rm axis}\)
(strict at every positive nonzero frame angle).

Combining with section 2 proves the envelope
\[
R^2\ge q_{\rm axis}=(h+1)^2+(y+1/2)^2.
\]
Reflect the sign of y to get the theorem (E).
The argument uses only actual square vertices,
a finite set of exact polynomials and elementary
concavity; it covers the entire continuum. QED.

## Scope, equalities and exact verification

The proof does *not* claim the same 37/100 cutoff
for arbitrary larger disks. It also does not assert
any exclusion involving two or more square labels.
It only strengthens the transverse center envelope
for a **single true rotated square** inside the
already justified n=8 squared-radius ceiling.

[verify_cap_envelope_37_100.py](verify_cap_envelope_37_100.py)
replays the exact polynomial/tangent and disk-ceiling
comparisons using rational arithmetic. The computer was used
to locate the simple threshold and tangent points;
the argument above is a hand proof without relying
on numerical optimization or sampled positivity.
