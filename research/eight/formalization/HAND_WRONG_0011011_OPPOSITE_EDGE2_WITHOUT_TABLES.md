# Opposite outer quarter edge 2: a whole-domain hand proof

This note completes the table-free version of
`../WRONG_0011011_OPPOSITE_OUTER_EDGE2_QUARTER_HAND_PROOF.md`.
It replaces every derivative-range table in that manuscript. Its
coordinate reductions, aligned contacts, contact flows, and compact-minimum
arguments are unchanged analytic arguments. Together they prove the full
outer/outer edge-2 \((-,+)\) component, and its reflected edge-6 component,
on all four original signed axes and both sides of alignment:

\[
 C=\phi-P(b)-R(B)>.89777>.89765,
 \qquad |\phi-\pi/2|\le .7.                                    \tag{1}
\]

All terminating decimals below are exact rationals. Set

\[
 Q=9789/2500,\quad a(y)=\sqrt{Q-(y+.5)^2}-.5,\quad
 d=\sqrt{Q/2}-.5,\quad b_1=\sqrt{Q-2.25}-.5,
\]
\[
 P(y)=.02478+.93015y+.02363y^2-.11055a(y)y,
 \qquad R(y)=-.01025a(y)+.16031y+.63457a(y)y.
\]

No numerical cover or verification-program result is a premise of this
proof. The elementary point comparisons use integer-square bounds and
adjacent alternating Taylor sums, as described at the end.

## 1. Two uniform bounds for the inverse-contact derivatives

For any outer coordinate \(0\le y\le d\), write

\[
 u=a(y)+.5,\quad v=y+.5,\quad r=v/u,\quad q=Q+1-2u,
 \quad N=4Qu-2u^2-Q(Q+1),\quad f_1=\frac{Q-u}{uq}.
\]

Thus \(1.399<u<1.915\), \(0<r\le1\), and \(q>1.0856\).
We shall use the whole-domain estimates

\[
 r f_1'(u)<\frac14,\qquad f_1<.963,
 \qquad -.002<K_0(u)<.371,
 \quad K_0=\frac Q{u^3}-\frac{3r^2}{q}.                         \tag{2}
\]

Here the prime on \(f_1\) means differentiation with respect to \(u\).
In particular \(f_1'=N/(u^2q^2)\).

For the first inequality there is nothing to prove when \(N\le0\).
When \(N>0\), the circle support inequality at the point
\((1.85,\sqrt{Q-1.85^2})\), whose second coordinate exceeds \(.702\), gives

\[
 v<\frac{Q-1.85u}{.702}.
\]

Consequently it suffices to prove the following quintic positive:

\[
 p(u)=\frac{.702}{4}u^3q^2-(Q-1.85u)N>0.
\]

Put \(t=u-1.8\), so \(|t|<.401\). Its exact expansion is

\[
\begin{aligned}
 p(1.8+t)={}&
 \frac{512687530359}{1562500000000}
 -\frac{884171885847}{312500000000}t
 +\frac{849004292517}{62500000000}t^2\\
 &-\frac{19499756129}{12500000000}t^3
 +\frac{3584061}{1250000}t^4+\frac{351}{500}t^5.
\end{aligned}
\]

The positive fourth-degree term can be discarded. Bounding the third
and fifth terms by their absolute values gives, on this entire interval,

\[
 p>.328-2.830|t|+12.90t^2
 \ge .328-\frac{2.830^2}{4(12.90)}>.17.                         \tag{3}
\]

For the remaining inequalities in (2), the partial fractions

\[
 f_1=\frac{Q}{(Q+1)u}+\frac{Q-1}{(Q+1)q}
\]

show that \(f_1''(u)>0\); both endpoint values at \(1.399,1.915\)
are below \(.963\). Also

\[
 K_0=\frac{3u^3-5Qu+Q(Q+1)}{u^3q}.
\]

The numerator attains its positive-\(u\) minimum at
\(\sqrt{5Q/9}<1.475\), so it is greater than
\(Q[Q+1-(10/3)(1.475)]>-.005\). The denominator is greater than
\(4\): the function \(u^3(Q+1-2u)\) has just one positive critical
point, a maximum, and both displayed endpoints exceed \(4\).
This proves the lower bound. For the upper bound,

\[
 K_0''=
 \frac{12Q}{u^5}
 \left(1-\frac{3u}{2(Q+1)}-\frac{u^2}{(Q+1)^2}\right)
 +\frac{24(Q-1)^2}{(Q+1)^2q^3}>0,
\]

because \(u/(Q+1)<.39\). Both endpoint values are below \(.371\).
This proves all of (2) by whole-domain calculus.

## 2. The complete axial curve, without angle intervals

The axial contact in the parent manuscript is

\[
 (a(y)-.5)\cos x-(y+.5)\sin x=.5,
 \qquad 0\le y\le b_1.
\]

The unique nonnegative angle decreases from a value below \(.571\)
to zero. Use \(y\), rather than \(x\), as its parameter and put

\[
 H(y)=\pi/2-x(y)-P(0)-R(y),\quad
 w=\sqrt{q-.25},\quad
 K=K_0-\frac{r^2/4}{q(q-.25)}.
\]

Implicit differentiation gives

\[
 H'=f_1-\frac{r}{2qw}-R',\qquad
 H''=-r f_1'(u)-\frac{K}{2qw}-R''.                             \tag{4}
\]

The label derivative \(R'\) decreases, and
\(R'(.2)>.973\). By (2), \(H'<.963-.973<0\) for \(y\le.2\).
Thus that entire part reduces to its right endpoint.

For \(y\ge.2\), use \(R''(y)\le R''(.2)<-.552\),
\(K\le K_0<.371\), and

\[
 \frac1{2qw}<\frac1{2(1.0856)(.914)}<.505.
\]

Equation (4) and (2) now give the uniform curvature bound

\[
 H''>-.25-.505(.371)+.552>.11.                                 \tag{5}
\]

There is just one reference evaluation. At the rational angle
\(x_0=.15017\), define

\[
 Z=.5+\cos x_0,\quad Y=\sqrt{Q-Z^2},\quad
 U=Z\cos x_0+Y\sin x_0,\quad
 y_0=Y\cos x_0-Z\sin x_0-.5.
\]

Direct substitution gives

\[
 .5661<y_0<.5662,\quad H(y_0)>.8977853,
 \quad |H'(y_0)|<10^{-5}.                                    \tag{6}
\]

For example, the parent manuscript's angle derivative has magnitude
less than \(10^{-5}\) at this point, and
\(-y_x=U(1-\sin x_0/Y)>1.47\), which gives the last inequality.
Completing a square in (5) proves

\[
 H>.8977853-\frac{10^{-10}}{.22}>.89778                         \tag{7}
\]

on \([.2,b_1]\); monotonicity extends it to \([0,b_1]\).
This replaces both the three curvature rows and the separate angle
tail in Section 3 of the parent manuscript.

## 3. The upper-angle source ratio by circle support

Section 7 of the parent needs

\[
 P'(b)\left(u-\frac{\cos x}{\cos x+r\sin x}\right)<1,
 \qquad0\le b\le d,\quad0\le x\le.7.                          \tag{8}
\]

The expression in parentheses increases with \(x\), and
\(\tan(.7)<.8423\). Since \(P'\) is convex, its endpoint bounds
\(P'(0)<.774\), \(P'(d)<.973\), and \(d>.899\) give

\[
 P'(b)<.774+.223b=.6625+.223v.
\]

With \(K_1=u+.8423v\), the circle support inequality gives
\(K_1\le\sqrt{Q(1+.8423^2)}<2.588\). Hence the parenthesis in (8)
is less than

\[
 u(1-1/K_1)<.614u.
\]

A second application, \(u+.51v\le\sqrt{Q(1+.51^2)}<2.23\), yields

\[
\begin{aligned}
 (.6625+.223v)u
 &<(.6625+.223v)(2.23-.51v)\\
 &=1.477375+.159415v-.11373v^2\\
 &\le1.477375+\frac{.159415^2}{4(.11373)}<1.534.
\end{aligned}
\]

Thus the left side of (8) is less than
\(.614(1.534)=.941876<1\) on the whole domain. This replaces all
five source-ratio rows, with no subdivision of the source coordinate.

## 4. Concavity of the lower-angle support bound

For the support function in Section 8 of the parent manuscript, let

\[
 g=.83829,\quad h=1.061,\quad
 n^2=g^2+h^2-2gh\sin x,
\]
\[
 F(x)=\pi/2-x-P(0)-R(0)-\sqrt Q\,n+h\cos x+(g+h)/2.
\]

We prove \(F''<0\) on the entire \([0,.7]\). Put \(t=\sin x\),
so \(0\le t<.645\). Direct simplification gives

\[
 F''=-h\cos x+
 \frac{\sqrt Q\,gh(g-ht)(h-gt)}{n^3}.
\]

Both factors \(g-ht,h-gt\) are positive. Squaring the two positive
sides shows that the desired inequality is equivalent to

\[
 \mathcal P(t)=(1-t^2)(g^2+h^2-2ght)^3
                  -Qg^2(g-ht)^2(h-gt)^2>0.                    \tag{9}
\]

This is a quintic with rational coefficients. On writing \(t=.645-y\),
\(0\le y\le.645\), its exact coefficients give

\[
 \mathcal P(.645-y)>
 .166+1.553y+4.984y^2
             +y^3(5.818-1.382y-5.629y^2)>0.                  \tag{10}
\]

For transparency, the six coefficients, in ascending order, lie in

\[
 (.16685,.16686),\ (1.55301,1.55302),\
 (4.98475,4.98476),\ (5.81838,5.81839),\
 (-1.38110,-1.38109),\ (-5.62885,-5.62884).
\]

These are bounds on the six coefficients of the single displayed
polynomial, obtained by ordinary rational multiplication; they are
not values on angle cells. The last parenthesis in (10) exceeds
\(5.818-1.382(.645)-5.629(.645)^2>2.5\).

Concavity and the two point values \(F(.01)>.8982\),
\(F(.7)>.986\) prove the parent's full \([.01,.7]\) tail.
Its separate analytic argument for \(0\le x\le.01\) already uses
one uniform positive-curvature estimate and a decreasing contact flow.
No rows from the former seven-interval concavity check remain.

## 5. The upper-angle target ratio by a uniform derivative bound

Put \(z=d-.5\in(0,.4)\), \(w=\sqrt{q-z^2}\), and

\[
 \mathcal F(y)=f_1+\frac{rz}{qw}.
\]

The target-ratio lemma in Section 11 of the parent is
\(\mathcal F>R'\) on the whole outer arc. At zero its difference
exceeds \(.001\). Differentiation gives

\[
 \mathcal F'=-r f_1'(u)+\frac{z}{qw}K,
 \qquad K=K_0-\frac{r^2z^2}{q(q-z^2)}.
\]

By (2) and the global bounds already proved,

\[
 K>-.002-\frac{.16}{1.0856(.9256)}>-.162,
 \qquad 0<\frac z{qw}<\frac{.4}{1.0856(.962)}<.384.
\]

As \(R''\) decreases and \(R''(0)<-.325\), it follows that

\[
 \mathcal F'-R''>-.25-.384(.162)+.325>.012.                     \tag{11}
\]

Thus \(\mathcal F-R'\) increases strictly from its positive initial
value. This replaces all five derivative rows in that lemma and
establishes the strict target-ratio bound on every active contact.

## 6. Assembly and exact arithmetic

Sections 2, 3, 4, and 5 replace, respectively, the parent's axial
curvature table, source-ratio table, support-concavity table, and
target-ratio table. All other reductions there consist of explicit
monotone motions, single uniform derivative estimates, the two aligned
convex contact bounds, and the enumerated boundaries of a compact
minimum. They apply on the closed domains and preserve each stated
original separating axis. Their resulting bounds are strictly greater
than \(.89777\), as are (7) and the support endpoints above. Hence (1)
holds on all eight axis/angle halves, including every boundary tie.

The finite point comparisons in this note have explicit inputs:
\(Q\), the stated rational coordinates or angles, the two labels, and
the displayed radicals. For a square root, compare the squares of its
two proposed rational bounds. For sine and cosine on \([0,.7]\), use
the adjacent alternating sums through degrees 11/13 and 12/14,
respectively. A sufficient rational enclosure for \(\pi/2\) is
\(1.57079632679489661923<\pi/2<1.57079632679489661924\), obtainable
from the alternating arctangent sums in Machin's identity. These
elementary point enclosures are the only numerical evaluations used.

This is a complete pair-component theorem. The exclusion of the full
word additionally requires its other core/core, mixed, and outer/outer
components and the cyclic telescoping sum.
