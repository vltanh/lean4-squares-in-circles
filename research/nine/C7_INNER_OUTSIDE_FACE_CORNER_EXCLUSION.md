# A uniform outgoing-ray exclusion sharpens the C7 inner-pair angle

**Status: complete hand implications; two independent full hand audits passed.**
Suppose a physical ring encloses unit squares and every boundary-square
center has norm strictly less than \(M=91/60\). Keep

\[
k=3721/7200,\qquad e=k-1/2=121/7200,\qquad
d=\sqrt{5/2}-M
\]

from `C7_INNER_SIDE_CORNER_RESTRICTIONS.md`. Every enclosed center
has both own-coordinate magnitudes less than \(k\), and every enclosed
vertex has norm greater than \(d>19/300\).

We prove that an enclosed center cannot have one own-coordinate
magnitude at least \(1/2\) and the other at least \(3/8\). The
optimization retains every orientation and every separator owner of
the boundary square which meets an explicit outgoing ray. It then
improves the whole extra-pair restriction to

\[
\boxed{\sin\theta<4/15,\qquad 0\le\theta\le\pi/4.}
\]

The parallel endpoint is already excluded separately. No common-frame
normalization of the actual unit squares is made here, and a whole
nonparallel C7 capacity or sharp-cap routing theorem is still missing.

## 1. A sharp rectangle-ray lemma with all outer frames retained

Put

\[
K=[1/24,1]\times[1/24,7/8],\qquad z=(1/2,3/8).
\]

**Lemma.** If a unit square \(S\) is interior-disjoint from \(K\) and
meets \(\{t z:t\ge2\}\), then

\[
|C_S|^2\ge37/16>\left(91/60\right)^2.
\tag{1}
\]

The first bound is sharp: the aligned unit centered at \((3/2,1/4)\)
lies to the right of \(K\) and meets the ray at \((1,3/4)\).
The last comparison in (1) is \(8325>8281\) over denominator 3600.

### 1.1. A separator owned by the rectangle

Only the positive horizontal and vertical normals are possible. For a
rightward separator, put \(h_S=H_S(e_x)=H_S(e_y)\in[1/2,1/\sqrt2]\).
Then

\[
C_x\ge1+h_S,\qquad C_y\ge3/4-h_S>0.
\]

The squared sum increases with \(h_S\), so its minimum at \(h_S=1/2\)
is \(37/16\). For an upward separator, the ray reaches height
\(7/8\) only at first coordinate at least \(7/6\). Thus

\[
C_y\ge7/8+h_S,\qquad C_x\ge7/6-h_S>0,
\]

and the increasing squared sum is at least

\[
(11/8)^2+(2/3)^2=1345/576>37/16.
\tag{2}
\]

### 1.2. The exact lower expression for a square-owned separator

Let \(n\) be an own side normal of \(S\), directed from \(K\) to
\(S\), and let \(m\) be a perpendicular own normal. Write

\[
H=\max_{x\in K}n\cdot x,
\quad z_n=n\cdot z,
\quad z_m=m\cdot z,
\quad \lambda=H/z_n.
\]

One has \(z_n>0\). Indeed \(z\) is strictly inside \(K\), so
\(H>z_n\); if \(z_n\le0\), no point \(t z\), \(t\ge2\),
could lie on the outward side of the supporting line of \(K\).

The two own-coordinate constraints on the outer center are

\[
n\cdot C_S\ge H+1/2,\qquad
|m\cdot C_S-tz_m|\le1/2.
\]

Ray membership also gives \(t z_n\ge n\cdot C_S-1/2\ge H\),
so \(t\ge\lambda\). Consequently the exact expression needed below is

\[
|C_S|^2\ge(H+1/2)^2+
       \bigl(\max\{|\lambda z_m|-1/2,0\}\bigr)^2.
\tag{3}
\]

We cover the positive quadrant and both possible mixed signs of \(n\).
Both-negative normals have \(z_n<0\) and are already impossible.

### 1.3. Positive-quadrant own normals

Write \(n=(a,b)=(\cos\alpha,\sin\alpha)\),
\(0\le\alpha\le\pi/2\), and choose \(m=(-b,a)\). Here

\[
H=a+7b/8,\qquad
\lambda=\frac{8a+7b}{4a+3b},\qquad
g=\lambda z_m=\lambda\frac{3a-4b}{8}.
\]

The signed quantity \(g\) strictly decreases from \(3/4\) to
\(-7/6\). In fact \(\lambda'=4/(4a+3b)^2\le4/9\),
\(z_m'=-z_n\), and

\[
g'=\lambda' z_m-H<0:
\]

if \(z_m\ge0\), the first term is at most \(1/6\) while
\(H\ge7/8\); if \(z_m<0\), the first term is negative.

When \(g>1/2\), the center whose squared norm is the right side of
(3) is

\[
C_* =\lambda z+\tfrac12(n-m).
\]

Parameterize this interval by \(t=b/a<3/4\). Then
\(\lambda=(8+7t)/(4+3t)\) increases with \(t\), while both
\(a+b\) and \(b-a\) increase over this interval. Thus both coordinates
of \(C_*\) increase from their values \((3/2,1/4)\) at \(t=0\).
This proves (1) in the first regime.

When \(g<-1/2\), use \(t=a/b\). At \(t=2/3\),

\[
-g=111/(68\sqrt{13})<1/2,
\]

so monotonicity of \(g\) puts the entire present regime in
\(0\le t<2/3\). Now

\[
\lambda=\frac{8t+7}{4t+3},\qquad
C_* =\lambda z+\tfrac12(n+m),
\]

and its coordinate derivatives are

\[
\begin{aligned}
(C_*)_x'&=-\frac2{(4t+3)^2}
  +\frac{1+t}{2(1+t^2)^{3/2}}>0,\\
(C_*)_y'&=-\frac3{2(4t+3)^2}
  +\frac{1-t}{2(1+t^2)^{3/2}}>0.
\end{aligned}
\]

For the first inequality use
\((1+t)/(1+t^2)^{3/2}\ge1/(1+t^2)\ge9/13\).
For the second, clear the positive factors and use
\(\sqrt{1+t^2}\le1+t^2/2\): the numerator is at least

\[
6+15t-\tfrac{25}{2}t^2-16t^3-\tfrac32t^4
\ge6-\tfrac89t>0.
\]

Hence these coordinates increase from \((2/3,11/8)\), proving (2)
throughout this second regime.

Finally, the region \(|g|\le1/2\) is a single interval. There the
right side of (3) is \((H+1/2)^2\). The positive function
\(H+1/2\) is concave in \(\alpha\), so its minimum on that
interval is at an endpoint. The endpoint values have just been
bounded by (1) and (2). This covers the entire positive quadrant.

### 1.4. Downward mixed-sign own normals

Write \(n=(a,-b)\), \(m=(b,a)\), with \(a>0,b\ge0\), and
put \(t=b/a\). Positivity of \(z_n\) means \(0\le t<4/3\).
Now

\[
H=a-b/24,\qquad
\lambda=\frac{8-t/3}{4-3t},\qquad
\lambda'=\frac{68/3}{(4-3t)^2}\ge\frac{17}{12}.
\]

Consider \(C_* =\lambda z+(n-m)/2\). Its coordinates start at
\((3/2,1/4)\). Their derivatives are strictly positive:

\[
\begin{aligned}
(C_*)_x'&=\lambda'/2-
       \frac{1+t}{2(1+t^2)^{3/2}}
       \ge17/24-1/\sqrt2>0,\\
(C_*)_y'&=3\lambda'/8-
       \frac{1-t}{2(1+t^2)^{3/2}}>0.
\end{aligned}
\]

For the second bound, the subtracted term is at most \(1/2\),
whereas the first term is at least \(17/32\). The elementary
bound on the first subtracted term follows from
\(1+t\le\sqrt2\sqrt{1+t^2}\).

Since both coordinates of \(C_*\) and of \(m\) are nonnegative,
\(m\cdot C_*=\lambda z_m-1/2\ge0\). Thus the unclipped formula
is exactly the expression in (3), not merely a proposed center.
The increasing coordinates prove (1) throughout this mixed-sign branch.

### 1.5. Leftward mixed-sign own normals

Write \(n=(-b,a)\), \(m=(a,b)\), and \(t=b/a\). Here
\(0\le t<3/4\), and

\[
H=7a/8-b/24,\qquad
\lambda=\frac{7-t/3}{3-4t},\qquad
\lambda'=\frac{27}{(3-4t)^2}\ge3.
\]

Again take \(C_* =\lambda z+(n-m)/2\). It starts at
\((2/3,11/8)\). Its derivative bounds are

\[
(C_*)_x'\ge3/2-1/2>0,\qquad
(C_*)_y'\ge9/8-1/\sqrt2>0.
\]

As before, positivity of both coordinates proves that the tangential
clipping in (3) is inactive. The norm is therefore bounded by (2).
This exhausts all SAT owners and signs and proves the lemma.

## 2. A whole excluded region for an enclosed unit's center

Suppose an enclosed unit has own-coordinate magnitudes at least
\(1/2\) and \(3/8\), respectively. Change own-axis signs and order
so its center is \((\xi,\eta)\) with

\[
1/2\le\xi<k,\qquad3/8\le\eta<k.
\]

Since \(k-1/2<1/24\), that unit contains the entire fixed rectangle
\(K\) of Section 1. The point \(z=(1/2,3/8)\) is strictly inside
the unit. Follow its ray \(t z\), \(t\ge1\), outward through the
bounded region. The ray lies inside \(K\) for \(1\le t<2\), so
its first boundary-square encounter has \(t\ge2\). That boundary
square is interior-disjoint from \(K\), and the lemma forces center
norm greater than \(M\), a contradiction.

Thus, whenever an enclosed unit has one own-coordinate magnitude at
least one half, the other magnitude is strictly less than \(3/8\).

## 3. The improved whole-pair angular restriction

Take any two interior-disjoint enclosed units. Use the same owned SAT
normal and support corner as in Section 3 of
`C7_INNER_SIDE_CORNER_RESTRICTIONS.md`. In the own frame of the unit
whose supporting corner is \(p=(p_1,p_2)\), write the normal as
\((c,s)=(\cos\theta,\sin\theta)\), \(c\ge s\ge0\). Then

\[
p_1>-e,\qquad p_2>-e,\qquad cp_1+sp_2<e,\qquad |p|>d.
\tag{4}
\]

If \(p_1,p_2\ge0\), then

\[
e>cp_1+sp_2\ge s(p_1+p_2)\ge s|p|>sd,
\]

so \(s<e/d<121/456<4/15\).

If \(p_2<0\), the corresponding center coordinate is less than
\(-1/2\). Section 2 then gives \(p_1>1/8\). But

\[
cp_1+sp_2>c/8-se\ge(1/\sqrt2)(1/8-e)>e,
\]

contradicting (4). The last bound already follows from
\(1/\sqrt2>7/10\) and \(e<1/50\).

The remaining case is \(p_1<0\). Section 2 gives \(p_2>1/8\),
and (4) implies

\[
\frac{s}{1+c}<8e=121/900.
\]

If \(s\ge4/15\), use \(c\le1-s^2/2\) and monotonicity to get

\[
\frac{s}{1+c}\ge\frac{s}{2-s^2/2}
\ge\frac{30}{221}>\frac{121}{900},
\]

a contradiction. These cases are exhaustive, proving \(\sin\theta<4/15\).

## 4. A common-frame inscribed-square consequence

Bisect the two actual inner frame angles, so each makes angle
\(\phi=\theta/2\) with this auxiliary frame. Each actual unit contains
a centered square parallel to the auxiliary frame, of side

\[
\ell=\frac1{\cos\phi+\sin\phi},\qquad
\ell^2=\frac1{1+\sin\theta}>\frac{15}{19}>\frac{49}{64}.
\]

Thus both contain common-oriented squares of side strictly greater than
\(7/8\). Their original centers and arbitrary relative translations
are retained. This is an inscribed-object consequence only; it does
not align, enlarge or replace either actual unit square in the packing.
Whole-square cap routing remains necessary before applying the sharp
three-square cap theorem.
