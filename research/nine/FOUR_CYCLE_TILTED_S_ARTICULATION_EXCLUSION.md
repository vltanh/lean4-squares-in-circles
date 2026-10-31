# The entire tilted S-articulation all-three-boundary C4 is impossible

**Status: complete hand branch theorem; root and separate independent full hand
audits passed.** Work in the declared radius window

\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 h=\sqrt{R^2-\frac14}-1,
 \qquad \sigma=\frac1{\sqrt2},\quad
 \rho=R-\sigma,\quad r=R-\sqrt2.
 \tag{1}
\]

Let a selected positive component have cycle \(A-B-U-C-A\)
and a radial S leaf L attached to its clear articulation A. Suppose
B,U,C physically touch the circle. The leaf is normalized east,

\[
 L=[h,h+1]\times[-1/2,1/2],\qquad P=(h,0)\in A\cap L.
\]

Assume A is in the entire tilted family. After reflecting the whole
packing across the horizontal axis if necessary, its inward side vectors from P are

\[
 (-a,-b),\quad(-b,a),\qquad
 a\ge b>0,\quad a^2+b^2=1.
 \tag{2}
\]

**Theorem.** No such positive core exists. The proof retains all frames
and physical circle-corner masks of B,U,C, every contact normal and
shared-side application mean, and all four extra squares. It uses the
global circle-force balance only to place B and C on opposite arcs;
the ensuing contradiction is geometric. It does not introduce a
positive multiplier on an additional physical AU contact.

Together with `FOUR_CYCLE_ALIGNED_S_ARTICULATION_EXCLUSION.md`, this
excludes the entire radial S-leaf all-three-boundary C4 core. The D
leaf family is separate.

## 1. The upper and lower boundary-neighbor arcs

Put

\[
 \vartheta=\arctan(3/7).
\]

The full geometric S-neighbor theorem in
`S_LEAF_CONNECTED_BOUNDARY_NEIGHBORS.md`, Section 1, applies after
exactly the reflection in (2). Every physical circle corner of either
neighbor B or C belongs to one of

\[
 J_+=(\pi/9,\pi-\vartheta),\qquad
 J_-=(3\pi/2-\vartheta,2\pi-\pi/9),
 \tag{3}
\]

and every one body's physical corners belong to the same interval.

B and C must have opposite assignments. Indeed, if both were in the
same interval, choose one circle corner on each of B,C,U,L. The
physical boundary contacts BU and UC follow circular corner order,
by `CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md`, Section 2. The path
B--U--C must occupy the arc between B and C that avoids the chosen
corner of L. Because each interval in (3) has length less than pi and
does not contain either leaf corner, that arc is inside the same
interval. This holds for every choice of U's circle corner. All circle
atoms on B,U,C would therefore have the same strict sign of second
coordinate. The S leaf has zero vertical circle resultant. Summing
the positive component's force equations gives a contradiction.
This argument permits zero individual corner weights and uses only
the positive total circle load outside L.

Relabel so B uses \(J_+\) and C uses \(J_-\). A physical circle
corner differs from its own center direction by strictly less than
\(\pi/9\), by
`CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md`, Lemma 2.1. Thus their
center angles \(\beta,\gamma\), chosen in \([0,2\pi)\), obey

\[
 0<\beta<\pi-\vartheta+\pi/9<\pi,
 \qquad
 3\pi/2-\vartheta-\pi/9<\gamma<2\pi.
 \tag{4}
\]

Here \(\vartheta>\pi/8>\pi/9\), because
\(3/7>\sqrt2-1=\tan(\pi/8)\).
We will also use

\[
 \vartheta<5\pi/36.
 \tag{5}
\]

For an exact check, \(\vartheta<\pi/6\) and the triple-angle
formula gives \(\tan(3\vartheta)=207/77<3<2+\sqrt3
=\tan(5\pi/12)\). Both comparison angles are in \((0,\pi/2)\),
which proves (5).

## 2. A's own frame and the exact corner-radius dichotomy

Use the positively oriented orthonormal axes

\[
 e=(a,b),\qquad f=(-b,a),
 \qquad \tau=\arctan(b/a)\in(0,\pi/4].
\]

All coordinates in the next sections are in this frame, with the
circle origin unchanged. Put

\[
 u=ha,\qquad v=hb,\qquad
 A=[u-1,u]\times[-v,1-v].
 \tag{6}
\]

In particular \(u\ge v>0\), \(u^2+v^2=h^2\), and
\(v<h/\sqrt2<1\). Denote A's two left vertices by

\[
 V=(u-1,-v),\qquad Z=(u-1,1-v).
\]

Define the exact threshold

\[
 u_0=\frac{h^2+1-r^2}{2}
     =\sqrt2 R-h-\frac98.
 \tag{7}
\]

We need the uniform estimates

\[
 \boxed{\frac34<u_0<\frac45,
 \qquad h^2-u_0^2>\frac14.}
 \tag{8}
\]

Here are full exact checks. The function \(u_0\) increases with R,
since \(u_0'=\sqrt2-R/\sqrt{R^2-1/4}>0\) whenever \(R^2>1/2\).
At \(R=79/40\), one has \(h<73/80\) and \(\sqrt2>707/500\),
so

\[
 u_0>\frac{55853}{20000}-\frac{73}{80}-\frac98
       =\frac{15103}{20000}>\frac34.
\]

At the upper endpoint,

\[
 u_0=\frac{\sqrt{2210}-\sqrt{1041}}{16}-\frac18<\frac45,
\]

using \(\sqrt{2210}<941/20\) and \(\sqrt{1041}>129/4\).

For the last estimate in (8), both positive factors

\[
 h-u_0=2h+\frac98-\sqrt2R,
 \qquad h+u_0=\sqrt2R-\frac98
\]

increase with R. At the lower endpoint, \(h>91/100\),
\(\sqrt2<99/70\), and \(\sqrt2>707/500\) give

\[
 h-u_0>\frac{17}{112},\qquad
 h+u_0>\frac{33353}{20000}.
\]

Consequently

\[
 h^2-u_0^2>\frac{567001}{2240000}
            =\frac14+\frac{7001}{2240000}>\frac14.
\]

The threshold has the following exhaustive geometric consequence:

* If \(u\le u_0\), then \(v>1/2\) and \(|Z|<r\).
* If \(u>u_0\), then \(|V|<r\).

Indeed \(|V|^2=h^2+1-2u\), proving the second statement.
In the first case, \(v^2=h^2-u^2\ge h^2-u_0^2>1/4\).
Since \(u\ge v\), the sum \(u+\sqrt{h^2-u^2}\) is
nonincreasing in u. Thus

\[
 u+v\ge u_0+\sqrt{h^2-u_0^2}>u_0+\frac12,
\]

and

\[
 |Z|^2=h^2+2-2(u+v)<h^2+1-2u_0=r^2.
 \tag{9}
\]

Equality \(u=u_0\) belongs to the first case; no boundary pose is
discarded.

## 3. An ineligible vertex removes an entire center quadrant

Every point of a physical boundary unit has norm at least r, and
its center has norm at least \(\rho\). The latter follows because
the distance from a square center to a corner is exactly \(\sigma\).
If a unit X touches A, some shared point lies within distance
\(\sigma\) of its center. Equivalently,

\[
 \operatorname{dist}(c_X,A)\le\sigma.
 \tag{10}
\]

The following implication uses (10) with no frame restriction on X.

If \(|Z|<r\), no such boundary center can lie in the closed
upper-left quadrant \(x\le0,y\ge0\). In fact, its nearest point
q in the rectangle (6) has coordinates obtained by clamping its two
coordinates to the rectangle intervals. Therefore
\(|q_x|\le|u-1|\) and \(0\le q_y\le1-v\), including
the possibility \(u-1>0\). Hence \(|q|\le|Z|<r\), and
(10) would give \(|c_X|<r+\sigma=\rho\), a contradiction.

Likewise, if \(|V|<r\), no boundary center satisfying (10) can
lie in the closed lower-left quadrant \(x\le0,y\le0\): the
clamped point now satisfies \(|q_x|\le|u-1|\) and
\(-v\le q_y\le0\), so \(|q|\le|V|<r\).

Set

\[
 \beta'=\beta-\tau,\qquad \gamma'=\gamma-\tau.
\]

The unwrapped bounds (4)--(5) give

\[
 -\pi/4<\beta'<\pi,
 \qquad \pi<\gamma'<2\pi.
 \tag{11}
\]

For the second strict lower bound, use
\(\gamma'>3\pi/2-\vartheta-\pi/9-\pi/4
=\pi+5\pi/36-\vartheta>\pi\).

Every center within distance \(\sigma\) of A also obeys

\[
 x\ge u-1-\sigma,\qquad
 -v-\sigma\le y\le1-v+\sigma.
 \tag{12}
\]

These actual center restrictions, not an arbitrary disk-center
packing relaxation, will determine the needed gap.

## 4. The complete case \(u\le u_0\)

Put

\[
 C_0=1+\sigma,\qquad K=C_0-u,\qquad H=C_0-v.
\]

Both K,H are positive, and \(K\le H<1/2+\sigma<\rho\),
using \(v>1/2\) and \(R>1/2+\sqrt2\).

Section 3 and \(|Z|<r\) force B's center to have positive
first coordinate: by (11), a nonpositive first coordinate for B
would place it in the upper-left quadrant. Consequently (12),
\(|c_B|\ge\rho\), and (11) give

\[
 \beta'\le\arcsin(H/\rho).
\]

For C, (11)--(12) give

\[
 \gamma'\ge\pi+\arccos(K/\rho),
\]

whether its first coordinate is negative or nonnegative. Hence

\[
 \gamma-\beta=\gamma'-\beta'
 \ge\frac\pi2+\arccos(K/\rho)+\arccos(H/\rho).
 \tag{13}
\]

We prove uniformly

\[
 K^2+H^2-\frac65KH<1<\frac{16}{25}\rho^2.
 \tag{14}
\]

The second inequality follows from \(\rho>5/4\). For the first,
at fixed h the expression on the left decreases as \(u+v\)
increases, since \(u^2+v^2=h^2\). The restrictions \(u\ge v>1/2\)
therefore bound it above by

\[
 F(h,C_0)=h^2+\frac45C_0^2-\frac25C_0
       -\left(\frac45C_0+\frac35\right)
                     \sqrt{h^2-\frac14}.
\]

On \(91/100<h<11/10\), this is strictly decreasing in h:
\(\sqrt{h^2-1/4}<49/50\) and \(C_0>17/10\) show
\(2\sqrt{h^2-1/4}<4C_0/5+3/5\), which is exactly the
negative derivative condition. At \(h=91/100\), it increases
with \(C_0\). Using \(C_0<12/7\) and
\(\sqrt{(91/100)^2-1/4}>19/25\) thus gives the exact bound

\[
 F(h,C_0)<\frac{487609}{490000}<1.
\]

For positive x,y less than one, the inequality
\(x^2+y^2-6xy/5<16/25\) implies
\(\arccos x+\arccos y>\arccos(3/5)\).
If \(xy\le3/5\), this follows immediately from the cosine
addition formula. Otherwise square the positive comparison
\(\sqrt{(1-x^2)(1-y^2)}>xy-3/5\); the displayed quadratic
inequality is exactly the result. Applying this to (14), (13) yields

\[
 \boxed{\gamma-\beta>\frac\pi2+\arccos(3/5).}
 \tag{15}
\]

## 5. The complete case \(u>u_0\)

Put again \(K=1+\sigma-u\), and now put \(J=\sigma+v\).
Section 3 and \(|V|<r\) force C's center to have positive
first coordinate, since (11) otherwise puts it in the lower-left
quadrant. The coordinate bounds (12) therefore give

\[
 \gamma'\ge\frac{3\pi}{2}+\arccos(J/\rho),\qquad
 \beta'\le\pi-\arccos(K/\rho),
\]

provided \(0<K,J<\rho\). We verify these inequalities together
with quantitative bounds now.

First \(u>u_0>3/4\) gives

\[
 0<K<\frac14+\sigma<\frac{24}{25}.
\]

The exact threshold identity in (7) gives

\[
 v^2=h^2-u^2<h^2-u_0^2=r^2-(1-u_0)^2
                         <r^2-\frac1{25}.
\]

Since \(0<r<4/5\), we have
\(1/25>r/20\), so

\[
 v^2<r^2-r/20<(r-1/40)^2,
 \qquad v<r-1/40.
\]

The last step uses \(r>11/20>1/40\). Thus

\[
 0<J<\rho-\frac1{40}.
\]

The elementary radius estimates

\[
 \frac54<\rho<\frac{11}{8}
\]

now imply

\[
 \frac K\rho<\frac{96}{125},\qquad
 \frac J\rho<\frac{54}{55}.
 \tag{16}
\]

For completeness, the upper bound on rho follows from
\(R<52/25\) and \(\sigma>141/200\); the lower bound follows
from \(R\ge79/40\) and \(\sigma<29/40\).
Also \(r<4/5\) follows already from \(R<52/25\) and
\(\sqrt2>7/5\). All of these follow by squaring positive rational
comparisons.

The two angle bounds therefore give

\[
 \gamma-\beta\ge\frac\pi2+\arccos(K/\rho)+\arccos(J/\rho)
 >\frac\pi2+\arccos(2/3).
 \tag{17}
\]

Here the last comparison has the explicit exact check

\[
 \begin{aligned}
 &\cos\left(\arccos\frac{96}{125}
                   +\arccos\frac{54}{55}\right)\\
 &\hspace{15mm}=\frac{5184-\sqrt{698581}}{6875}
 <\frac{4384}{6875}<\frac23,
 \end{aligned}
\]

using \(698581>800^2\). The angles being compared belong to
\((0,\pi)\), so the cosine comparison has the stated direction.

## 6. The two physical boundary contacts cannot bridge the gap

In both exhaustive cases, (15) or (17) gives

\[
 \gamma-\beta>\frac\pi2+\arccos(2/3).
 \tag{18}
\]

The center directions of L,B,C are \(0,\beta,\gamma\).
By `CIRCLE_CONTACT_ANGULAR_ORDER.md`, the physical contacts BU and
UC follow consecutive center directions along their minor arcs. The
arc from C to B through zero contains L. Thus B--U--C must follow
the other arc, and U's center angle \(\delta\) satisfies
\(\beta<\delta<\gamma\).

Two touching unit squares have center distance at most \(\sqrt2\).
If their boundary-center radii are s,t, both at least
\(\rho>5/4\), and their minor angle is omega, then

\[
 2st(1-\cos\omega)
 \le(s-t)^2+2st(1-\cos\omega)\le2.
\]

Consequently \(\cos\omega>9/25\). Apply this to each of
BU and UC to obtain

\[
 \gamma-\beta<2\arccos(9/25).
 \tag{19}
\]

But

\[
 \frac\pi2+\arccos(2/3)>2\arccos(9/25).
\]

Indeed both sides lie in \((0,\pi)\), and their cosines are
\(-\sqrt5/3\) and \(-463/625\), respectively. The required
strict comparison follows from

\[
 5\cdot625^2-9\cdot463^2=23804>0.
\]

Equations (18)--(19) contradict one another. This proves the entire
tilted theorem, including \(a=b\), the threshold \(u=u_0\), all
point and side-interior contacts, all shared means and all physical
circle masks. No contact-normal ownership or degree-two equation was
assumed, and every other physical square remains untouched.

No numerical search, pose cover, Lean compilation or CI is a premise.
