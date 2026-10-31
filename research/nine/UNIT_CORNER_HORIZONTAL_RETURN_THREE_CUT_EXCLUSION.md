# A whole unit cannot fit beside a corner under linked horizontal-return cuts

Date: October 26, 2026.

**Status: complete whole-orientation theorem, freshly independently
reviewed in REVIEW_COMMON_HORIZONTAL_CENTRAL_ROOT_RECOVERY_2026_10_26.md.**
No circle or graph is assumed. Every displayed relation is a necessary
part of the statement; the contact cuts are not varied independently.

## 1. Full geometric statement

Let
\[
\begin{gathered}
x,t,u,v>0,\quad x^2+t^2=u^2+v^2=1,\quad
x>24/25,\quad t<27/100,\\
u\ge v>1/3,\quad u<33/35,\qquad
0<\lambda\le1,\quad0<\ell<19/25,\\
\eta=x+\ell t-u,\qquad v=1+t-\ell x,\qquad
\alpha=xu+tv,\quad\beta=xv-tu>0.
\end{gathered}
\tag{1}
\]
Put \(A=[-1,0]\times[0,1]\).
There is no unit square E of any orientation, interior-disjoint from A,
whose every point satisfies
\[
\begin{gathered}
X\ge-\lambda,\quad0\le Y\le1+t,\\
-tX+x(Y-1)\le0,\qquad
xX+tY\le1+t,\qquad
vX-uY\le v\eta.
\end{gathered}
\tag{2}
\]
All containing cuts and physical touching conditions are weak.

## 2. Exact separating-axis localization

For a coordinate separator between A and E, the right case places
E in \(X\ge0\). The left case allows horizontal width at most
\(\lambda-1\le0\); the upper case vertical width at most t<1;
the lower case width zero. These are impossible for a unit square.

For a noncoordinate E side-axis separator, use positive components
\(\xi,\zeta\), \(\xi^2+\zeta^2=1\), and put
\(H_0=(\xi+\zeta)/2\), \(J_0=(\xi-\zeta)/2\).
Orient the normal from A toward E.

For a southwest normal \((-\xi,-\zeta)\), (2) bounds its minimum
on E by \(\xi\lambda-1-\xi\zeta<\xi\), below its maximum on A.
For northwest \((-\xi,\zeta)\), that minimum is at most
\[
\xi\lambda+\zeta(1+t)-1-\xi\zeta<\xi+\zeta,
\]
again below the maximum on A. Here \(\lambda\le1,t<1\).

For northeast \((\xi,\zeta)\), suppose E has a point with X<0.
Its center has \(X_c<H_0\). The weak separation implies
\(Y_c>1-J_0\). The actual first-cut half-support is
\[
H_U=\frac{|x\zeta-t\xi|+t\zeta+x\xi}{2},
\]
and
\[
H_U-tH_0-xJ_0
=\frac{|x\zeta-t\xi|+x\zeta-t\xi}{2}\ge0.
\]
Thus the maximum of \(-tX+xY\) on E is strictly greater than x,
contradicting the first cut.

For southeast \(p=(\xi,-\zeta)\), \(j=(\zeta,\xi)\), write
\[
E=[\rho,\rho+1]p+[\tau,\tau+1]j.
\]
Separation from A gives \(\rho\ge0\). An X<0 point would force
\(\tau<0\), and then
\(\min_EY=-(\rho+1)\zeta+\tau\xi<0\), contradicting (2).

This exhaustive weak separating-axis cover proves that a possible E
must lie wholly in the first quadrant.

## 3. The complete orientation range has three support minima

Represent an E side direction by
\((\cos\phi,\sin\phi)\), \(0\le\phi\le\pi/2\), and put
\[
\begin{gathered}
H_0=(\cos\phi+\sin\phi)/2,\qquad r=v/u,\\
H_N=\frac{|v\cos\phi-u\sin\phi|+v\sin\phi+u\cos\phi}{2},\\
H_C=\frac{x\cos\phi+t\sin\phi+|t\cos\phi-x\sin\phi|}{2}.
\end{gathered}
\]
The quadrant and return cut force the C support to be at least
\[
\mathcal F(\phi)=(x+tr)H_0+(t/u)H_N+H_C-tr\eta.
\tag{3}
\]
The sign changes are at
\(\phi_C=\arctan(t/x)\) and \(\phi_N=\arctan(v/u)\).
Their strict order follows from \(\beta>0\).
On each entire intervening interval, the second derivative of (3)
is the negative of its positive support sum. The function is strictly
concave there, so its minimum is at the coordinate, C, or N alignment.
The two coordinate endpoints describe the same square.

### Coordinate alignment

The exact excess is
\[
\mathcal F(0)-(1+t)
=t\left(r(1-\eta)-\frac{t}{1+x}\right).
\tag{4}
\]
The endpoint equations in (1) imply
\[
1-\eta=\frac{x-1-t+\alpha}{x}.
\]
Also \(u\ge v\) and \(\beta>0\) imply
\(\alpha>u\ge1/\sqrt2>7/10\).
Thus \(1-\eta>39/100\), while \(r>35/99\). Therefore
\[
r(1-\eta)>\frac{91}{660},\qquad
\frac{t}{1+x}<\frac{27}{196},\qquad
\frac{91}{660}-\frac{27}{196}=\frac1{8085}>0.
\tag{5}
\]
This gives a positive whole-domain excess.

### Alignment with the C cut

Direct substitution, followed by the two exact endpoint equations, gives
\[
\begin{split}
\mathcal F(\phi_C)-(1+t)
&=t\{r(x+t-\eta)-(1+t-x)\}\\
&=t(1-\ell)(x+rt)>0.
\end{split}
\tag{6}
\]
This is an exact factorization; no angular relaxation is needed.

### Alignment with the return cut

The exact substitution gives
\[
\mathcal F(\phi_N)-(1+t)=\frac{\alpha}{u}(v-\eta).
\tag{7}
\]
After multiplying by u, the identity reduces to
\(u\{x(u+\eta)+t(v-1)-1\}=u(x^2+t^2-1)=0\).

Since \(u\ge v>1/3\) on the unit quarter-circle,
\(u+v>(1+2\sqrt2)/3>5/4\). Hence
\[
v-\eta=u+v-x-\ell t
>\frac54-1-\frac{19}{25}\frac{27}{100}
=\frac{28}{625}>0.
\tag{8}
\]
Thus all three exact support minima exceed the allowed value.
Concavity proves this for every intervening orientation, contradicting
(2). The whole unit is excluded.

The proof retains \(\lambda=1\), all weak separators and every square
orientation. It uses no parameter grid or computational sign packet.

