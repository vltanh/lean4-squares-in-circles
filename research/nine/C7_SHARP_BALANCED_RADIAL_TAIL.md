# A sharp continuous radial-tail bound in the balanced center sector

**Status: complete hand implication; root and independent full hand audits passed.**
Put \(M=91/60\) and \(k=3721/7200\). Let

\[
T=(a,b)+[-1/2,1/2]^2,\qquad
9/20\le a\le k,\qquad 2a/3\le b\le a.
\tag{1}
\]

If an arbitrary unit square \(S\), interior-disjoint from \(T\),
meets the outgoing ray \(\{t(a,b):t>1\}\) beyond \(T\), then

\[
\boxed{|C_S|^2\ge
F_R(a,b):=(a+1)^2+
\left(b\left(1+\frac1{2a}\right)-\frac12\right)^2.}
\tag{2}
\]

This is sharp: the aligned unit centered at
\((a+1,b(1+1/(2a))-1/2)\) touches \(T\)'s right face and the
outgoing ray at a vertex. The theorem retains both SAT owners and every
normal sign. It is a continuous two-coordinate restriction, not a finite
parameter cover. Its present scope is the balanced sector (1).

## 1. Rectangle-owned separators

Let \(h\in[1/2,1/\sqrt2]\) be either coordinate halfwidth of
\(S\). If \(T\) owns the rightward separator, then

\[
C_x\ge a+1/2+h,
\qquad C_y\ge b(1+1/(2a))-h.
\]

The resulting lower bound

\[
(a+1/2+h)^2+
\max\{b(1+1/(2a))-h,0\}^2
\]

increases with \(h\): here \(b(1+1/(2a))\le a+1/2\).
At \(h=1/2\) it is (2). The second coordinate in (2) is positive,
since (1) gives

\[
b(1+1/(2a))-1/2\ge2a/3-1/6\ge2/15>0.
\]

For an upward separator the corresponding lower bound is

\[
(b+1/2+h)^2+
\max\{a(1+1/(2b))-h,0\}^2.
\]

It also increases with \(h\). On the interval where the second term
is positive, half its derivative is at least

\[
b+3/2-a-a/(2b)
\ge3/4-(a-b)\ge3/4-k/3>0.
\]

Its minimum is therefore

\[
F_U(a,b):=
\left(a(1+1/(2b))-1/2\right)^2+(b+1)^2.
\tag{3}
\]

Write \(\rho=a/b\in[1,3/2]\). Direct expansion gives

\[
F_U-F_R=(\rho-1)^3
\left(\frac b\rho+\frac{\rho+1}{4\rho^2}\right)\ge0.
\tag{4}
\]

Negative coordinate normals cannot separate a square on the outgoing
ray from \(T\). This covers the rectangle-owned cases.

## 2. The exact square-owned expression

Let \(n\) be an own normal of \(S\), directed from \(T\) to
\(S\), and let \(m\) be a perpendicular own normal. Put

\[
z=(a,b),\quad z_n=n\cdot z,\quad z_m=m\cdot z,
\quad H=z_n+H_T(n),\quad \lambda=H/z_n.
\]

Ray membership forces \(z_n>0\), because \(H>z_n\). In particular
\(H>0\) and \(\lambda>1\). As in the earlier rectangle-ray
lemma, separation and the tangential strip of \(S\) give

\[
|C_S|^2\ge(H+1/2)^2+
\max\{|\lambda z_m|-1/2,0\}^2.
\tag{5}
\]

We bound (5) over the positive quadrant and both possible mixed signs.

## 3. Positive-quadrant normals

Write \(n=(u,v)=(\cos\gamma,\sin\gamma)\) and
\(m=(-v,u)\), for \(0\le\gamma\le\pi/2\). Then

\[
H=(a+1/2)u+(b+1/2)v,
\qquad \lambda=1+\frac{u+v}{2(au+bv)},
\qquad g=\lambda(-av+bu).
\]

The function \(g\) strictly decreases. Indeed,

\[
\lambda'=\frac{a-b}{2(au+bv)^2},\qquad
g'=\lambda' z_m-H.
\]

If \(z_m\ge0\), the first term is at most
\((a-b)/(2b)\le1/4\), while \(H\ge b+1/2\ge4/5\).
If \(z_m<0\), the first term is nonpositive. This proves the claim.

### 3.1. The regime \(g>1/2\)

The center realizing the right side of (5) is

\[
C_* =\lambda z+(n-m)/2.
\]

Here \(z_m>0\), so \(v/u<b/a\le1\). With \(t=v/u\),
\(\lambda=1+(1+t)/(2(a+bt))\) is increasing. Both coordinates
of \(C_*\) increase: besides the increasing multiples of
\(\lambda\), the two summands \((u+v)/2\) and \((v-u)/2\)
increase for \(0\le t<1\). Their initial center is

\[
(a+1,b(1+1/(2a))-1/2).
\]

Both coordinates are positive. Thus (5) is at least \(F_R\).

### 3.2. The regime \(g<-1/2\)

Use \(t=u/v\). This whole regime has \(0\le t<3/4\).
To see this, at \(t=3/4\) one has

\[
|g|=\frac45(a-3b/4)
 +\frac7{10}\frac{a-3b/4}{3a/4+b}
\le\frac25a+\frac{21}{85}<\frac12,
\]

where \(a<21/40\), \(b\ge2a/3\), and
\((\rho-3/4)/(3\rho/4+1)\le6/17\) were used.
The strict monotonicity of \(g\) then gives the asserted interval.

Now the center in (5) is

\[
C_* =\lambda z+(n+m)/2,
\qquad \lambda=1+\frac{1+t}{2(at+b)},
\qquad \lambda'=-\frac{a-b}{2(at+b)^2}.
\]

Its coordinate derivatives are positive. After division by positive
factors, the two required inequalities are

\[
\frac{\rho(\rho-1)}{(\rho t+1)^2}
 <\frac{1+t}{(1+t^2)^{3/2}},
\qquad
\frac{\rho-1}{(\rho t+1)^2}
 <\frac{1-t}{(1+t^2)^{3/2}}.
\tag{6}
\]

Both left sides increase with \(\rho\in[1,3/2]\). For the first
inequality, use

\[
\frac{\rho(\rho-1)}{(\rho t+1)^2}
\le\frac{3/4}{(1+3t/2)^2}<\frac1{1+t}
\le\frac{1+t}{(1+t^2)^{3/2}}.
\]

The last comparison follows from
\((1+t^2)^{3/2}\le(1+t)^2\) on \([0,1]\).
For the second inequality it suffices to put \(\rho=3/2\) and use
\(\sqrt{1+t^2}\le1+t^2/2\). The remaining difference is bounded
below by the concave polynomial

\[
G(t)=\frac12+2t-\frac32t^2-\frac94t^3-\frac14t^4.
\]

It is positive on \([0,3/4]\), since
\(G(0)=1/2\), \(G(3/4)=131/1024\), and \(G''<0\).
This proves (6). Both coordinates therefore increase from the positive
initial center

\[
(a(1+1/(2b))-1/2,b+1),
\]

so (5) is at least \(F_U\ge F_R\).

### 3.3. The middle regime

By monotonicity of \(g\), the set \(|g|\le1/2\) is one interval.
There (5) equals \((H+1/2)^2\). The positive function
\(H+1/2\) is concave in \(\gamma\), so its minimum occurs at
one of the interval's endpoints. Those endpoints were covered by the
previous two regimes, with continuity. Thus the entire positive quadrant
satisfies (2).

## 4. Mixed-sign normals

For \(n=(u,-v)\), \(m=(v,u)\), put \(t=v/u<a/b\).
Then

\[
\lambda=
\frac{a+1/2+(1/2-b)t}{a-bt},\qquad
\lambda'=\frac{a+b}{2(a-bt)^2}.
\]

The candidate \(C_* =\lambda z+(n-m)/2\) starts at the right
center of Section 3.1. Its derivatives obey

\[
(C_*)_x'\ge\frac12\left(1+\frac ba\right)-\frac1{\sqrt2}
\ge\frac56-\frac1{\sqrt2}>0,
\]

\[
(C_*)_y'\ge\frac{b(a+b)}{2a^2}-\frac12
\ge\frac59-\frac12>0.
\]

Here \((1+t)/(2(1+t^2)^{3/2})\le1/\sqrt2\) and
\((1-t)/(2(1+t^2)^{3/2})\le1/2\) were used. Both candidate
coordinates stay positive, so \(m\cdot C_*\ge0\); hence its
unclipped squared norm is exactly (5). The increasing coordinates give
\(F_R\).

For \(n=(-v,u)\), \(m=(u,v)\), put \(t=v/u<b/a\).
This time

\[
\lambda=
\frac{b+1/2+(1/2-a)t}{b-at},\qquad
\lambda'=\frac{a+b}{2(b-at)^2}.
\]

The same candidate starts at the upper center of Section 3.2. Its
derivatives satisfy

\[
(C_*)_x'\ge\frac{a(a+b)}{2b^2}-\frac12>0,
\qquad
(C_*)_y'\ge\frac{a+b}{2b}-\frac1{\sqrt2}>0.
\]

Again both coordinates remain positive, the tangential clipping is
inactive, and the norm is at least \(F_U\ge F_R\). Normals with
both coordinates negative have \(z_n<0\) and are impossible. This
exhausts all square-owned cases and proves (2).

## 5. Continuous consequence for enclosed centers

For a C7 enclosed unit satisfying (1), the outgoing ray eventually meets
an actual boundary unit. Its center has norm strictly less than \(M\).
Consequently

\[
(a+1)^2+
\left(b\left(1+\frac1{2a}\right)-\frac12\right)^2<M^2,
\]

or equivalently

\[
\boxed{b<\frac{a}{a+1/2}
\left(\frac12+\sqrt{M^2-(a+1)^2}\right).}
\tag{7}
\]

The radical is defined by the preceding strict inequality. Sign changes
and interchange of own coordinates preserve this conclusion. Outside
the balanced sector, the explicit alternative \(b<2a/3\) remains;
it is not silently discarded. The intended further use of (7) is in the
whole four-square or ring capacity argument, with all actual outer
frames and both SAT owner branches retained. That whole exit is still
unproved here.
