# Wrong word 0011011, edge 3: negative outer to negative core

## Whole-family theorem

Let the source be a negative outer-boundary state and the target a negative
core-boundary state. On the entire quarter-one interval
\[
 \ell:=\pi/2-.7\le\phi\le\pi/2+.7,
\]
every retained separating axis gives
\[
 C=\phi-T(b)+c_0+gB>\gamma,\qquad
 c_0=.16823,\quad g=.62312,\quad\gamma=.89765,
\tag{1}
\]
where
\[
 T(b)=.01670+2.42322b-.91744b^2-.95769\,a(b)b.
\tag{2}
\]
The labels in (1)–(2) are exactly the negative role-3 outer and negative
role-4 core labels. The theorem includes the whole target side and corner.

All decimals are exact rationals. The proof uses one explicit degree-8
positive polynomial, a continuous core-coordinate concavity argument,
and three fixed angle intervals for endpoint monotonicity. The companion
checker makes 64 strict rational comparisons. No sampled minimum, adaptive
state subdivision, or unproved contact selection is a premise.

Write
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad
 d=\sqrt{Q/2}-.5,\quad d_c=.5+\frac{\sqrt2}{24},\quad
 a_c=\frac7{12},\quad a_0=\sqrt{Q-.25}-.5.
\]
The source has
\[
 a(b)=\sqrt{Q-(b+.5)^2}-.5,\qquad0\le b\le d.
\]
The target side has \(A=a_c,0\le B\le.5\); its corner has
\[
 A=.5+\sqrt{1/144-(B-.5)^2},\qquad .5\le B\le d_c.
\]
The actual own-frame centers are \((a,+b)\) and \((A,+B)\).

## 1. A global outer-label upper bound and the direct late range

Put \(r=(b+.5)/(a+.5)\), so \(a'=-r\) and
\(r'=Q/(a+.5)^3>0\). Direct differentiation gives
\[
 \begin{aligned}
 T'&=2.42322-1.83488b-.95769(a-br),\\
 T''&=-1.83488+.95769(2r+br'),\\
 T'''&=.95769(3r'+br'')>0.
 \end{aligned}
\tag{3}
\]
The fixed comparisons
\[
 -.049<T''(.6)<-.048,\quad T''(.7)>0,\quad
 .610<T'(.6)<.62
\tag{4}
\]
show \(T'>0\) throughout the arc. Before .6 it decreases to a value
above .610; between .6 and .7 it loses less than .0049; after .7 it
increases. Hence
\[
 T(b)\le T(d)<.67949.
\tag{5}
\]

We will use
\[
 T(b)<k_0+qb,\qquad k_0=.1109,\quad q=.633.
\tag{6}
\]
Here is a short derivation. On \([0,.6]\), let \(H=T-.62b\).
By (4), \(H''<-.048\). At \(b_*=.53362\), the exact quadratic bound gives
\[
 H(b_*)+\frac{H'(b_*)^2}{.096}<.110895.
\tag{7}
\]
Thus \(H<.110895\) on that whole interval.
On \([.6,.7]\), \(H'\) is convex and negative at .6; therefore \(H\)
has no interior maximum above its endpoint values. Both endpoint values
are below .1109. Finally, \(T-qb\) is convex on \([.7,d]\);
its value at .7 is below .1109 by the preceding stronger .62 bound,
and its diagonal value is below .1109 by direct comparison. This proves (6).

The label \(c_0+gB\) increases with \(B\). Therefore
\[
 \begin{array}{ll}
 \phi\ge1.409:&C>1.409-.67949+.16823=.89774>\gamma,\\
 \phi\ge1.098,\ B\ge.5:&
 C>1.098-.67949+.16823+.62312/2=.8983>\gamma.
 \end{array}
\tag{8}
\]
Both cutoffs are below \(\pi/2\). Thus only lower-half angles remain,
and the corner requires only \(\ell\le\phi\le1.098\).

Let \(s=\sin\phi,c=\cos\phi,W=(1+s+c)/2\). The four margins are
\[
 \begin{array}{c|l}
 1&-b+As+Bc-W,\\
 2&-ac-bs+A-W,\\
 3&as-bc+B-W,\\
 4&a-Ac+Bs-W.
 \end{array}
\tag{9}
\]
Axis 1 is impossible: its first three terms are at most the norm of
the core center, less than .8, whereas \(W\ge1\).
Axis 2 is at most \(A-W<0\). It remains to treat axes 3 and 4.

## 2. Axis 3 on the whole remaining interval

Use (6), and subtract \(g\) times the nonnegative axis-3 margin from
the resulting lower cost. Minimizing the remaining source linear
functional over its full circle gives
\[
 F(\phi)=\phi+c_0-k_0+\frac{g+q}{2}
        +g\sin\phi-RN(\phi),
\quad
 N^2=g^2+q^2-2gq\cos\phi.
\tag{10}
\]
Indeed any outer state satisfies
\[
 xa+yb\ge-\frac{x+y}{2}-R\sqrt{x^2+y^2}.
\]
The target coordinate cancels exactly, so this bound covers both core
pieces.

The norm increases with \(\phi\), and
\[
 N''+\frac N4=\frac{(g^2-q^2)^2}{4N^3}>0.
\tag{11}
\]
The exact comparison
\[
 g\sin\ell-\frac R4 N(1.409)>0
\]
therefore gives \(F''<0\) throughout \([\ell,1.409]\).
Its endpoint values satisfy
\[
 F(\ell)>.984,\qquad F(1.409)>1.099.
\tag{12}
\]
Concavity proves (1) for the complete remaining axis-3 range.

## 3. Axis 4 with target on the side

Here \(A=a_c\), and axis 4 gives
\[
 a\ge W+a_c\cos\phi-B\sin\phi.
\]
Using (6) and the positive multiplier \(g/\sin\phi\), the target
coordinate again cancels. The full-circle support lower bound is
\[
 G(\phi)=\phi+c_0-k_0+\frac{g+q}{2}
 +\frac{g(1+13\cos\phi/12)
       -R\sqrt{g^2+q^2\sin^2\phi}}{\sin\phi}.
\tag{13}
\]
This is a direct SAT lower bound; no existence of a contact state is needed.

We prove \(G>\gamma\) by one polynomial on the entire required interval.
Put \(x=\pi/2-\phi\). The larger interval \([.161,.7]\) includes all
\(\ell\le\phi\le1.409\).
Let \(C_n,S_n\) be the degree-\(n\) alternating cosine and sine polynomials,
and set
\[
 \begin{aligned}
 K&=\frac{3.141592653589793238}{2}
      +c_0-k_0+\frac{g+q}{2}-\gamma,\\
 A_*&=C_{10}(x)(K-x)+g+\frac{13g}{12}S_{11}(x),\\
 P&=A_*^2-Q\{g^2+q^2C_8(x)^2\}.
 \end{aligned}
\tag{14}
\]
On this interval \(K-x>0\), \(C_{10}>0\), \(S_{11}\ge0\), and
\[
 C_{10}\le\cos x,\quad S_{11}\le\sin x,\quad C_8\ge\cos x>0.
\]
Consequently \(A_*>0\), and \(P>0\) implies (13) strictly.

Let \(P_8\) be the terms through degree 8 of \(P\), with .000299
subtracted from its constant coefficient. The sum of the absolute negative
discarded terms, each evaluated at .7, is less than .000299; thus
\(P(x)>P_8(x)\) on this interval. In
\[
 P_8(.161+.539t)=\sum_{j=0}^8 b_j\binom8j t^j(1-t)^{8-j},
\]
the coefficients have the following exact strict lower bounds:
\[
 \boxed{
 .6117715,\ .5130297,\ .4132075,\ .3172047,\ .2292187,\
 .1523344,\ .0883327,\ .0378233,\ .0006068.}
\tag{15}
\]
All are positive. Equations (13)–(15) prove every side case of axis 4.

## 4. Axis 4 with target on the corner: exact height reduction

It remains to treat \(\ell\le\phi\le1.098\) and \(.5\le B\le d_c\).
As a function of the source height \(u=a+.5\), the negative label is
exactly
\[
 M(u)=m_0-vu^2-\frac{k}{2}u-(V-ku)\sqrt{Q-u^2},
\tag{16}
\]
where
\[
 v=.91744,\quad k=.95769,\quad V=3.819505,\quad
 m_0=1.6636925+vQ.
\]
Expanding \(b=\sqrt{Q-u^2}-.5\) in (2) gives \(M(u)=-T(b)\).
Writing \(z=\sqrt{Q-u^2}\), its derivatives are
\[
 \begin{aligned}
 M'&=-2vu-k/2+kz+(V-ku)u/z,\\
 M''&=-2v-2ku/z+Q(V-ku)/z^3,\\
 M'''&=3Q(Vu-kQ)/z^5>0\qquad(u\ge1.4).
 \end{aligned}
\tag{17}
\]
The fixed bounds
\[
 M'(1.4)>.773,\quad M''(1.4)>-.204,\quad M''(1.5)>0
\]
imply
\[
 M'(u)>.75\qquad(1.4\le u\le a_0+.5).
\tag{18}
\]
On \([1.4,1.5]\), its possible loss is less than .0204; thereafter
\(M''>0\). Also \(M''(1.7)<3.212\).

The separator implies \(a+.5\ge u_*(B,\phi)\), where
\[
 u_*=1+(A(B)+.5)\cos\phi-(B-.5)\sin\phi.
\tag{19}
\]
This decreases with both \(B\) and \(\phi\), and its rectangle corners give
\[
 1.4<u_*<1.7.
\tag{20}
\]
Since \(M\) increases, every actual pair has the lower bound
\[
 C\ge f(B,\phi):=\phi+M(u_*)+c_0+gB.
\tag{21}
\]
In fact the continued contact heights in (20) lie within the physical
outer-height range. The argument only uses monotonicity, so it does not
require an original pair to be at contact.

## 5. The complete corner reduces to two endpoint curves

Put \(w=(B-.5)/(A-.5)\), \(0\le w\le1\). Then
\[
 A'=-w,\quad A''=-12(1+w^2)^{3/2},\quad
 (u_*)_B=-w\cos\phi-\sin\phi.
\]
Cauchy–Schwarz gives \((u_*)_B^2\le1+w^2\). Differentiating (21),
\[
 f_{BB}=M''(u_*)_B^2+M'\cos\phi\,A''.
\]
Using (18), \(M''<3.212\), and \(\cos1.098>.455\), we obtain
\[
 f_{BB}<
 3.212(1+w^2)-12(.75)(.455)(1+w^2)^{3/2}<0.
\tag{22}
\]
The last inequality follows already at \(w=0\).
Thus the minimum over the whole core corner is at its join or diagonal.

For a fixed core endpoint \((A_e,B_e)=(a_c,.5)\) or \((d_c,d_c)\), write
\[
 \begin{aligned}
 u_e(\phi)&=1+(A_e+.5)\cos\phi-(B_e-.5)\sin\phi,\\
 h_e(\phi)&=(A_e+.5)\sin\phi+(B_e-.5)\cos\phi,\\
 H_e(\phi)&=\phi+M(u_e(\phi))+c_0+gB_e.
 \end{aligned}
\tag{23}
\]
Then \(u_e\) decreases, \(h_e\) increases because \(h_e'=u_e-1>0\), and
\[
 H_e'=1-M'(u_e)h_e.
\tag{24}
\]
The function \(M'\) is convex by (17). On each of the three fixed intervals
\[
 [\ell,.95],\qquad[.95,1.03],\qquad[1.03,1.098],
\]
the two endpoint products
\[
 M'(u_e(L))h_e(H),\qquad M'(u_e(H))h_e(H)
\tag{25}
\]
are below .920, for each of the two core endpoints.
These twelve exact comparisons prove \(H_e'>.08\) throughout.
Both endpoint curves therefore increase on the complete angle interval.

At the initial angle,
\[
 H_{\rm join}(\ell)>.9196,\qquad
 H_{\rm diagonal}(\ell)>.897784>\gamma.
\tag{26}
\]
Concavity in \(B\) and monotonicity in \(\phi\) now prove all remaining
corner cases.

## 6. Exact arithmetic and exhaustive cover

The checker verifies every fixed comparison in (3)–(8), (11)–(12),
(14)–(15), (17)–(18), and (20)–(26).
It uses rational BigInt arithmetic, integer-square-root endpoint brackets
of denominator \(10^{14}\), and alternating Taylor bounds for the finitely
many trigonometric values. The rational pi bracket follows from Machin's
identity and alternating arctangent series. The degree-8 polynomial and all
its exact coefficients are reconstructed from (14), rather than supplied
as an unexplained sign assertion.

The result contains 64 strict comparisons. All pass in
wrong_0011011_edge3_outer_to_negative_core_arithmetic.json.

The late bounds (8) cover every upper angle without any SAT assumption.
Before those cutoffs, axes 1 and 2 are impossible. Section 2 proves all
axis-3 cases, Section 3 proves the complete axis-4 side, and Sections 4–5
prove the complete axis-4 corner. Joins, angle endpoints, and axis ties
are included. This is the full stated family, not an isolated contact strip.

