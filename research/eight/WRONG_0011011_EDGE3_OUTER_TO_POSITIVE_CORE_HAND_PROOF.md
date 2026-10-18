# 0011011: the whole negative outer-to-positive core edge-3 transition

## Theorem

At \(Q=9789/2500\), a negative outer source and positive core target
on edge 3 have corrected cost \(C>\gamma=.89765\) for every retained
separator and every angle
\[
 \ell=\pi/2-.7\le\phi\le\pi/2+.7.
\]
Both target core pieces are included. Reflected reversal supplies
edge 5. The only imported result is the aligned mixed-quarter
theorem, whose strict bound is .89777 at \(\phi=\pi/2\).

The proof consists of continuous contact reductions, one uniform
strong-convexity estimate, eight fixed concave scalar supports, two
degree-eight polynomial identities, and 127 fixed exact comparisons.
No discovered minimum or subdivision tree is an assumption.

Put
\[
 a_c=7/12,\ d_c=1/2+\sqrt2/24,\ d=\sqrt{Q/2}-1/2,\
 a_0=\sqrt{Q-1/4}-1/2,\quad g=.94831.
\]
The source own-frame center is \((a,+b)\), where
\[
 a=a(b)=\sqrt{Q-(b+1/2)^2}-1/2,\quad0\le b\le d.
\]
The target own-frame center is \((A,-B)\), on the core side or corner.
Its label is \(.04970+gB\); the source label is
\[
 T(b)=.01670+2.42322b-.91744b^2-.95769a(b)b.
\]
Hence
\[
 C=\phi-.04970-T(b)-gB.
 \tag{1}
\]
With \(s=\sin\phi,c=\cos\phi,W=(1+s+|c|)/2\), the four margins are
\[
\begin{array}{c|l}
1&-b+As-Bc-W\\
2&-ac-bs+A-W\\
3&as-bc-B-W\\
4&a-Ac-Bs-W.
\end{array}
\tag{2}
\]

## 1. Derivatives and two upper lines for the source label

Write
\[
 r=(b+.5)/(a+.5),\qquad r'=Q/(a+.5)^3,\qquad r''>0.
\]
Then
\[
 T'=2.42322-1.83488b-.95769(a-br),
\]
\[
 T''=-1.83488+.95769(2r+br'),\qquad
 T'''=.95769(3r'+br'')>0.
 \tag{3}
\]
In particular \(T''\) increases. Fixed comparisons give
\[
 -.049<T''(.6)<-.048,\quad T''(.7)>0,\quad T'(.6)>.610.
\]
Thus \(T'>.605>0\) everywhere: it decreases up to .6, is at least
\(T'(.6)-.049(.1)>.605\) on [.6,.7], and increases after .7.
We may use monotonicity of \(T\) below.

Let \(k=.1109\). The following two upper lines hold:
\[
 T(b)\le k+.62b\quad(0\le b\le.7),\qquad
 T(b)\le k+.633b\quad(0\le b\le d).
 \tag{4}
\]
Here is a short whole-domain proof. Put \(H=T-.62b\).
On [0,.6], \(H''<-.048\). At \(b_*=.53362\), exact arithmetic gives
\[
 H(b_*)+\frac{H'(b_*)^2}{.096}<.110895<k.
\]
Completing the upper tangent quadratic proves the first bound through
.6. On [.6,.7], \(H'\) is convex and \(H'(.6)<0\).
It can therefore change from negative to positive at most once on
this interval; \(H\) has no interior maximum above both endpoints.
The endpoint values are below \(k\). This proves the first line.

On [0,.7] the second line is weaker. On [.7,d], \(T''>0\),
so \(T-.633b\) is convex and its maximum is at an endpoint.
The .7 endpoint is already covered, and \(T(d)-.633d<k\).
This proves the second line.

We shall also use
\[
 \frac{T'}r<.89\quad(.7\le b\le d).
 \tag{5}
\]
On [.7,.8], \(T'<.674\), \(r>.762\); on [.8,d],
\(T'<.774\), \(r>.871\). Both ratios are below .89.
The monotonicity needed for these endpoint bounds follows from (3).

## 2. Immediate axis reductions

The core center norm is at most \(\sqrt2d_c<.8\), whereas \(W\ge1\).
Thus axis 1 is impossible everywhere.
Axis 2 is impossible below the quarter angle.

For axis 3, the target necessarily lies on the side:
\[
 B\le as-bc-W\le\sqrt{a^2+b^2}-1\le a_0-1<.415<.5.
 \tag{6}
\]
The outer norm bound follows from
\(a^2+b^2=Q-.5-a-b\), with \(a+b\) increasing.
Increasing \(B\) to contact lowers the cost while staying on that
side. At contact,
\[
 B=(a-.5)\sin\phi-(b+.5)\cos\phi-.5
 \quad(\phi\le\pi/2).
 \tag{7}
\]

For axis 4 below the quarter angle, a corner target is impossible:
if \(B\ge.5,\ A\ge d_c\), its constraint requires
\[
 a\ge .5+(d_c+.5)\cos\phi+\sin\phi\ge1.5>a_0.
\]
The middle expression is concave; its left endpoint is greater
than 1.5 and its right endpoint is 1.5.
Consequently \(A=a_c\), and the contact coordinate is
\[
 B=\frac{a-.5}{\sin\phi}-\frac12-\frac{13}{12}\cot\phi.
 \tag{8}
\]
This is below .415 whenever feasible. Indeed, for \(B<.5\),
\[
 W+a_c\cos\phi+B\sin\phi-(1+B)
 =\frac{13}{12}\cos\phi-(B+.5)(1-\sin\phi)\ge0.
\]
Thus \(B\le a-1\le a_0-1\). Contact reductions in (8) remain on
the side, including the closed zero-coordinate endpoint.

## 3. Axis 2 on the upper half

Set \(x=\phi-\pi/2\).
Using \(a\le a_0\), \(A\le a_c\), its inequality gives
\[
 b\le(a_0-.5)\tan x+\frac1{12}\sec x-\frac12.
\]
Use the global line in (4) and \(B\le d_c\) in (1):
\[
 C\ge U_2(x)=\pi/2+x-.0497-k-gd_c+\frac{.633}{2}
 -.633(a_0-.5)\tan x-\frac{.633}{12}\sec x.
\]
This is concave on [0,.7], and both endpoints exceed 1.14.
Axis 2 is therefore completely excluded.

## 4. Axis 3 below the quarter angle

### 4.1. Early angles, \(\ell\le\phi\le1.4\)

The margin in (6) decreases with \(b\) and increases with \(\phi\)
on the lower half. Its value at \(b=.6,\phi=1.4\) is negative,
so every early feasible state has \(b<.6\). The label \(T\) is
concave on that source range by (3).

The following eight rational upper tangents cover \(T\) there.
Each row uses the true tangent at the displayed \(b_*\), with both
its slope and intercept rounded upward. Since \(b\ge0\),
the stated line is an upper bound.

| Whole angle interval | \(b_*\) | \(q\) | \(k_q\), in \(T\le k_q+qb\) |
|---|---:|---:|---:|
| \([\ell,.95]\) | .186 | .849072101 | .036194154 |
| \([.95,1]\) | .208 | .827123134 | .040516466 |
| \([1,1.05]\) | .226 | .809833767 | .044267347 |
| \([1.05,1.1]\) | .245 | .792248783 | .048407521 |
| \([1.1,1.16]\) | .268 | .771892909 | .053626828 |
| \([1.16,1.23]\) | .297 | .747715180 | .060452973 |
| \([1.23,1.31]\) | .335 | .718627475 | .069635209 |
| \([1.31,1.4]\) | .384 | .685655525 | .081467247 |

Inserting the appropriate line into the contact cost, and applying
the full outer-circle support inequality, gives
\[
 F(\phi;q,k_q)=
 \phi-.0497-k_q+\frac{g+q}{2}
 +g\sin\phi-\sqrt Q\sqrt{g^2+q^2-2gq\cos\phi}.
 \tag{9}
\]
For \(N^2=g^2+q^2-2gq\cos\phi\),
\[
 N''+\frac N4=\frac{(g^2-q^2)^2}{4N^3}\ge0.
 \tag{10}
\]
All row slopes are below .85, and
\[
 g\sin\ell-\frac{\sqrt Q}{4}\sqrt{g^2+.85^2}>0.
\]
Thus each function (9) is strictly concave over the entire lower
half. Its two endpoints on its declared interval are both greater
than .89790. The eight whole intervals therefore prove every early
axis-3 state. This is a finite list of scalar concavity inequalities;
it is not an assumption about sampled interior values.

### 4.2. Later lower angles, \(1.4\le\phi\le\pi/2\)

At fixed angle, the derivative of the contact cost in \(b\) is
\[
 g(r\sin\phi+\cos\phi)-T'(b).
\]
For \(b\ge.7\), it is positive by (5) and
\(g\sin1.4>.89\).
Decreasing such a source coordinate to .7 lowers the cost and
increases the contact target coordinate. Equation (6) keeps that
coordinate below .415, so no target boundary is crossed.
It is consequently enough to use the small-arc line
\(T\le k+.62b\) in (9). Concavity (10) and the two endpoint
comparisons give
\[
 F(1.4;.62,k)>.89800,\qquad
 F(\pi/2;.62,k)>.89800.
 \tag{11}
\]

## 5. Axis 4 below the quarter angle: early contact reduction

Consider a feasible angle \(\phi\le1.4\) in (8).
Define
\[
 A_{\rm req}(\phi)=.5+.5\sin\phi+\frac{13}{12}\cos\phi,
\]
\[
 b_z(\phi)=\sqrt{Q-(A_{\rm req}(\phi)+.5)^2}-.5.
 \tag{12}
\]
This is the source coordinate where the contact target has \(B=0\).
Since \(B\ge0\), the source must have \(b\le b_z(\phi)\).
Fixed comparisons imply
\[
 \phi>1.12,\qquad b_z(\phi)\le b_z(1.4)<.551.
 \tag{13}
\]
Indeed \(A_{\rm req}(1.12)>a_0\), and \(A_{\rm req}\) decreases
throughout the feasible early interval.

The contact derivative is
\[
 F_b=\frac{gr}{\sin\phi}-T'(b).
\]
It increases with \(b\), since \(T''<0\) for \(b\le.551\).
We prove that its value at \(b_z\) is still negative.

Let
\[
 v=\frac{13}{12}\sin\phi-\frac12\cos\phi,\qquad
 b_z'=\frac vr.
\]
On the early feasible interval,
\[
 \sin\phi>.9,\quad\cos\phi<.436,\quad r<.65,\quad
 r'>.557,\quad v>.757.
\]
For
\(D(\phi)=gr(b_z)/\sin\phi-T'(b_z)\),
\[
 D'=\left(\frac{gr'}{\sin\phi}-T''\right)b_z'
              -\frac{gr\cos\phi}{\sin^2\phi}>0,
\]
because the following rational lower bound is positive:
\[
 \frac{D'}g>
 \frac{.557(.757)}{.65}-\frac{.65(.436)}{.9^2}>0.
\]
The right endpoint comparison is \(D(1.4)<-.013\).
Thus \(F_b\le D(\phi)<0\) everywhere feasible.
Increasing \(b\) until the target reaches zero strictly lowers
the cost. No source endpoint is hit first, by (13).
Every early axis-4 cost is therefore bounded below by
\[
 K(\phi)=\phi-.0497-T(b_z(\phi)).
 \tag{14}
\]

## 6. A uniform convexity proof for the zero-target boundary

The boundary in (12) is a single smooth interval from its axial
source endpoint to \(\phi=1.4\). Put
\[
 U=A_{\rm req}+.5=1+m,\qquad
 m=.5\sin\phi+\frac{13}{12}\cos\phi,\qquad
 V=b_z+.5=\sqrt{Q-U^2}.
\]
Also \(v^2+m^2=205/144\). Differentiation gives
\[
 b_z''=\frac{U m}{V}-\frac{Qv^2}{V^3}
       =\frac{N(m)}{V^3},
\]
\[
 N(m)=Qm(2m+1)-m(m+1)^3-\frac{205Q}{144}.
 \tag{15}
\]
The useful exact cancellation is
\[
 N'(m)=(4m+1)\{Q-(m+1)^2\}>0.
\]
Feasibility gives \(m\le\kappa=a_0-.5\).
The fixed radical comparison \(N(\kappa)<-1.8\), together with
\(V<1.051\), proves
\[
 b_z''<-\frac{1.8}{1.051^3}<-1.55.
 \tag{16}
\]
Throughout this boundary \(T''<0\), \(T'>.610\). Consequently
\[
 K''=-T''(b_z)(b_z')^2-T'(b_z)b_z''
       >.610(1.55)>.94.
 \tag{17}
\]

At the single rational point \(\phi_*=1.383036\), exact calculations give
\[
 K(\phi_*)>.89777657,\qquad |K'(\phi_*)|<10^{-6}.
\]
The lower tangent quadratic from (17) therefore implies on the
entire feasible boundary
\[
 K(\phi)\ge K(\phi_*)-\frac{K'(\phi_*)^2}{1.88}
                  >.89777656>\gamma.
 \tag{18}
\]
This proves the tight early primary branch. In particular, its
interior minimum is controlled by a hand curvature estimate and
one rational point, not by a numerical minimization assertion.

## 7. Axis 4 below the quarter angle: later support

For \(b\ge.7\), the contact derivative from (8) is positive:
\[
 F_b=\frac{gr}{\sin\phi}-T'>r(g-.89)>0.
\]
As in Section 4.2, decreasing \(b\) to .7 lowers the cost and
keeps the side contact feasible. It is enough to use
\(T\le k+.62b\) for \(\phi\ge1.4\).

Eliminating \(B\) using (8) and applying circle support yields
\[
 G_-(\phi)=\phi-.0497-k+\frac{g+.62}{2}
 +\frac{g(1+\frac{13}{12}\cos\phi)
        -\sqrt Q\sqrt{g^2+.62^2\sin^2\phi}}{\sin\phi}.
 \tag{19}
\]
The lower polynomial in Section 10 proves \(G_->\gamma\)
on \(\pi/2-.171\le\phi\le\pi/2\), which includes
the required interval \([1.4,\pi/2]\).

## 8. The complete upper strip \(0\le x\le.02\)

This section handles both axes 3 and 4 by a contact deformation to
the already proved aligned theorem.

Axis 3 forces the target side by (6); its contact coordinate is
\[
 B=(a-.5)\cos x+(b-.5)\sin x-.5.
\]
At fixed source,
\(B_x\le\max(b-.5,0)\le.4\), so
\[
 C_x=1-gB_x\ge1-.4g>0.
 \tag{20}
\]

For axis 4, the bound \(A\le a_c\) first gives
\[
 B\le(a_0-.5)\sec x-\frac12+\frac1{12}\tan x<.5
 \quad(0\le x\le.02).
\]
Thus it too has \(A=a_c\). Its contact is exactly
\[
 B=(a-.5)\sec x-\frac12+\frac1{12}\tan x,
\]
whose derivative is below .105. Hence again \(C_x>0\).

Decrease \(x\) along the chosen contact. The cost strictly decreases
until alignment or \(B=0\); the coordinate stays on the side.
At alignment use the imported bound .89777.

At a zero-coordinate exit, axis 3 implies
\(a\ge1-.4\sin(.02)>.992\).
Axis 4 implies
\(a\ge.5+.5\cos(.02)-\sin(.02)/12>.992\).
Since \(a(.81)<.992\), either exit has \(b<.81\).
The source label increases, so its cost is
\[
 C\ge\pi/2-.0497-T(.81)>.906.
 \tag{21}
\]
This covers every endpoint of the deformation and every state
in the whole closed upper strip.

## 9. Remaining upper angles, \(.02\le x\le.7\)

For axis 3, use the global line \(T\le k+.633b\) in the contact.
Circle support gives
\[
 F_+(x)=\pi/2+x-.0497-k+\frac{g+.633}{2}
 +g(\sin x+\cos x)
 -\sqrt Q\sqrt{g^2+.633^2+2g(.633)\sin x}.
 \tag{22}
\]
Identity (10), \(N\le g+.633\), and
\(g-\sqrt Q(g+.633)/4>0\) prove strict concavity.
Its endpoints at .02 and .7 are both greater than .91100.

For axis 4, \(A\le a_c\) gives the necessary bound
\[
 B\le\frac{a+a_c\sin x-W}{\cos x}.
\]
This bound is valid even for corner states; the relaxed coordinate
need not lie on the core. The global line and circle support yield
\[
 G_+(x)=\pi/2+x-.0497-k+\frac{g+.633}{2}
 +\frac{g(1-\frac1{12}\sin x)
        -\sqrt Q\sqrt{g^2+.633^2\cos^2x}}{\cos x}.
 \tag{23}
\]
The upper polynomial below proves the whole required interval.

## 10. Two explicit degree-eight positivity rows

Let \(\pi_-=3.141592653589793238<\pi\).
For a row slope \(q\), put
\[
 K_q=\pi_-/2-.0497-k+(g+q)/2-\gamma.
\]
Let \(C_{10},C_8,S_{11},S_9\) be the alternating cosine/sine
polynomials of the indicated degrees. On \(0\le x\le.7\),
\[
 0<C_{10}\le\cos x\le C_8,\qquad
 0\le S_{11}\le\sin x\le S_9\le.7.
\]
For the lower row, \(q=.62\), define
\[
 A_-=C_{10}(K_q-x)+g+\frac{13g}{12}S_{11}.
\]
For the upper row, \(q=.633\), define
\[
 A_+=C_{10}(K_q+x)+g-\frac g{12}S_9.
\]
All angle factors are positive on their declared intervals.
Also \(A_->g>0\), \(A_+\ge g(1-.7/12)>0\). Consequently
\[
 P_\pm=A_\pm^2-Q\{g^2+q^2C_8^2\}>0
 \tag{24}
\]
implies respectively (19) or (23) \(>\gamma\), with the stated
Taylor directions.

The negative terms of degree above eight have total absolute
values below \(10^{-9}\) for the lower row on [0,.171], and
\(10^{-5}\) for the upper row on [.02,.7].
Subtracting the corresponding allowance from the degree-eight
truncation gives a polynomial lower bound for (24).
The nine Bernstein coefficients have the following strict rational
lower bounds:

| Whole interval and row | Coefficients, in order |
|---|---|
| Lower, [0,.171], allowance \(10^{-9}\) | .0136520, .0162755, .0174316, .0172488, .0158580, .0133907, .0099778, .0057480, .0008271 |
| Upper, [.02,.7], allowance \(10^{-5}\) | .0617974, .4122007, .7506755, 1.0578577, 1.3123765, 1.4933330, 1.5837907, 1.5742478, 1.4631437 |

The convention is
\(P(l+(r-l)t)=\sum_{j=0}^8p_j\binom8j t^j(1-t)^{8-j}\).
Every printed lower bound is positive. This proves the two whole
scalar intervals with no hidden interior cases.

## 11. Coverage and arithmetic

Axes 1 and lower axis 2 are impossible; upper axis 2 is covered in
Section 3. Sections 4 and 8--9 cover both halves of axis 3.
Sections 5--7 and 8--10 cover both halves of axis 4.
All target-side reductions, corner relaxations, zero-coordinate
exits, and source-coordinate continuations are explicitly justified.

The companion checker performs 127 fixed comparisons. It checks
all tangent roundings and endpoint bounds, the source upper lines,
the exact boundary curvature and rational-point estimates, and
both polynomial rows including their negative-tail allowances.
The reconstructed arithmetic uses exact fractions, integer
square-root brackets, and alternating trigonometric series.
