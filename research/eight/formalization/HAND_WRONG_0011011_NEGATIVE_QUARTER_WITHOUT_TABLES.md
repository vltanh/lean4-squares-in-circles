# The negative outer quarter edge of 0011011 without curvature tables

This note proves the full edge-2 outer/outer negative-sign component of
`../WRONG_0011011_NEGATIVE_OUTER_QUARTER_HAND_PROOF.md` without its two
aligned-curvature intervals, five contact-curvature intervals, or five
endpoint-derivative intervals. Its conclusion, for every original axis
and every \(\pi/2-.7\le\phi\le\pi/2+.7\), is
\[
                       C>.89777>.89765.
\]
Reflected reversal also proves the corresponding edge-6 component.
This is a complete pair-component proof. The other components are still
required for the whole 0011011 word exclusion.

All decimals are exact terminating rationals. Endpoint comparisons below
are ordinary radical and trigonometric inequalities at explicitly given
points. The one degree-seven remainder is proved positive on its whole
domain, without a mesh or a coefficient-table premise.

## 1. Labels and the analytic contact reductions

Write
\[
 Q=9789/2500,\quad d=\sqrt{Q/2}-1/2,\quad
 a(b)=\sqrt{Q-(b+1/2)^2}-1/2,\quad a_0=a(0),
\]
\[
\begin{aligned}
 P(b)&=.02478+.93015b+.02363b^2-.11055a(b)b,\\
 T(B)&=.01670+2.42322B-.91744B^2-.95769a(B)B,\\
 C&=\phi-P(b)+T(B).
\end{aligned}
\]
We retain all four original separating projections in the cited note.
Its Sections 1, 3--5, and 6.1--6.2 are analytic support, monotonicity,
and endpoint arguments. The facts needed for their assembly are:

* Alignment has its minimum at \(b=d,B=1-d\), with cost
  \(\pi/2-P(d)+T(1-d)>.8977827\).
* Axes 1 and 2 have a direct cost bound greater than \(.95\) or \(.9\).
* The upper halves of axes 3 and 4 reduce to alignment.
* The lower half of axis 4 reduces to alignment or its diagonal boundary;
  that boundary is treated by its explicit concavity/monotonicity argument.
* The lower half of axis 3 has the active contact
  \[
   B=\tfrac12-(a(b)-\tfrac12)\cos x+(b+\tfrac12)\sin x,
   \qquad \phi=\pi/2-x.                                  \tag{1}
  \]
  At a fixed target \(B\), strict concavity in \(b\) reduces its minimum
  to \(b=0\), \(b=d\), \(x=0\), or \(x=.7\). The first two
  boundaries have the cited direct and scalar derivative proofs.

We now supply whole-domain proofs of the three facts for which the old
argument used interval rows: aligned curvature, contact concavity, and
the derivative shape on \(x=.7\).

## 2. Aligned curvature from one third-derivative sign

On \(d\le a\le1\), let \(b=\sqrt{Q-(a+1/2)^2}-1/2\) and
\(M(a)=-P(b)\). Put \(u=a+1/2\), \(w=b+1/2\). Directly,
\[
 M'''(a)=\frac{3Q(.961795u-.11055Q)}{w^5}>0.
\]
This expression increases with \(a\): its numerator is positive and
increasing, while \(w\) decreases. The common formula
\[
 T'''(B)=\frac{3Q(.95769)(Q-(B+1/2)/2)}
                  {\bigl(Q-(B+1/2)^2\bigr)^{5/2}}
\]
also increases with \(B\). Consequently, throughout the aligned interval,
\[
 \frac{d^3}{da^3}\{M(a)+T(1-a)\}
 =M'''(a)-T'''(1-a)
 \ge M'''(d)-T'''(1-d)>1.999-1.708>0.                       \tag{2}
\]
Its second derivative therefore increases. Its right endpoint satisfies
\[
                     M''(1)+T''(0)<-.094<0.
\]
Thus the first derivative decreases throughout the interval, and its
right endpoint exceeds \(.0149\). The aligned cost is strictly
increasing with \(a\), which proves the aligned minimum stated in
Section 1. The two former intervals are unnecessary.

## 3. Uniform contact concavity: the exact derivative formula

For the lower-half contact (1), write
\[
 v=b+1/2,\quad u=\sqrt{Q-v^2},\quad r=v/u,\quad
 q=Q+1-2u,\quad z=B-1/2.
\]
In particular \(u\ge v\), \(r\le1\), \(u>1.399\),
\(-.5\le z<.4\), and \(q>1\).
Solving the contact for \(x=x(b,B)\) gives
\[
 -x_b=f_1(u)+\frac{zr}{q\sqrt{q-z^2}},\qquad
 f_1(u)=\frac{Q-u}{uq}.
\]
For \(F(b,B)=-x(b,B)-P(b)\), differentiation yields
\[
 F_{bb}=-r f_1'(u)+\frac{z}{q\sqrt{q-z^2}}\,K(u,z)-P''(b),  \tag{3}
\]
\[
 K(u,z)=\frac Q{u^3}-\frac{2r^2}{q}-\frac{r^2}{q-z^2}.
\]
The elementary partial fractions
\[
 f_1(u)=\frac{Q}{(Q+1)u}+\frac{Q-1}{(Q+1)q}
\]
show that
\[
 f_1''(u)=\frac{2Q}{(Q+1)u^3}
              +\frac{8(Q-1)}{(Q+1)q^3}>0.                    \tag{4}
\]
We prove (3) negative on the two geometric halves \(b\ge1/2\) and
\(b\le1/2\). They use the same formula on their common boundary.

### 3.1. The half with \(b\ge1/2\)

Now \(1.399<u<1.71\), so \(q>1.4956\). From (4) and the single
endpoint comparison \(f_1'(1.399)>-.144\),
\[
                           -r f_1'(u)<.144.                 \tag{5}
\]
Set
\[
 K_0(u)=\frac Q{u^3}-\frac{3r^2}{q}
       =\frac{3u^3-5Qu+Q(Q+1)}{u^3q}.
\]
We have \(-.002<K_0<.11\) on the whole interval. For the lower bound,
the numerator attains its global positive-\(u\) minimum at
\(u_0=\sqrt{5Q/9}<1.475\); hence it exceeds
\(Q(Q+1-(10/3)(1.475))>-.005\). The denominator exceeds \(4\).
For the upper bound, the partial fractions give
\[
 K_0''(u)=\frac{12Q}{u^5}
  \left(1-\frac{3u}{2(Q+1)}-\frac{u^2}{(Q+1)^2}\right)
       +\frac{24(Q-1)^2}{(Q+1)^2q^3}>0.
\]
The first parenthesis is positive already from \(u/(Q+1)<.35\).
Convexity puts the maximum at an endpoint; both endpoint values at
\(1.399\) and \(1.71\) are less than \(.11\).

Since
\[
 K(u,z)=K_0(u)-\frac{r^2z^2}{q(q-z^2)},
\]
these bounds imply, uniformly in both signs of \(z\),
\[
 -.14<-.002-\frac{.25}{1.4956(1.2456)}<K(u,z)<.11<.14.
\]
Also \(\sqrt{q-z^2}>1.115\). The first two terms of (3) therefore
have sum less than
\[
                    .144+\frac{.07}{1.4956(1.115)}<.187.
\]
But \(P''\) increases, and \(P''(1/2)>.22\). Thus \(F_{bb}<-.033\)
on this entire half.

### 3.2. The half with \(b\le1/2\)

Here \(1.7<u<1.915\). Put
\[
 N=4Qu-2u^2-Q(Q+1),\qquad K_*=Qq-3u(Q-u^2).
\]
Both are positive on this interval. In fact \(N\) increases and is
positive at \(1.7\). To prove the stronger assertion \(K(u,z)>0\),
it suffices to use \(z^2\le.25\) and prove
\[
 R(u)=Qq(q-.25)-u(Q-u^2)(3q-.5)>0.
\]
For \(y=u-1.7\), direct expansion gives
\[
 R(1.7+y)=.455005404416+7.92109248y
                       +y^2(7.77468-26.5532y-6y^2)>0,         \tag{6}
\]
since \(0\le y\le.215\) and the last parenthesis is positive even
at its right endpoint. This also proves \(K_*>0\).

If \(z\le0\), the middle term of (3) is nonpositive, while
\(-r f_1'(u)<0\). Suppose therefore that \(z\ge0\). Since
\(z<.4\) and \(K(u,z)\le K_*/(u^3q)\), the first two terms of
(3) are at most
\[
 \frac1{u^3q^2}
 \left(-vN+\frac{.4K_*}{\sqrt{q-.16}}\right).                 \tag{7}
\]
The parenthesis is strictly negative. Squaring its positive sides is
legitimate and reduces this assertion to
\[
 \mathcal A(u)=(Q-u^2)N^2(q-.16)-.16K_*^2>0.                  \tag{8}
\]
Here is its whole-interval polynomial proof. For \(y=u-1.7\),
\(0\le y\le.215\), expansion of (8) gives
\[
 \mathcal A(1.7+y)
 >3.47+20.92y+y^2\left(-84.56-402.61y+647.5y^2
                                     -90.04y^3-50.57y^4\right).
\]
The exact constant and linear coefficients exceed \(3.47,20.92\);
the remaining degree-two through degree-six coefficients are bounded
in the indicated directions, and the omitted seventh coefficient is
\(8>0\). These comparisons follow by multiplying the two expressions
in (8), whose inputs are the displayed rational \(Q\).

The quadratic \(-402.61y+647.5y^2\) decreases on this interval.
Thus the parenthesis exceeds its lower bound obtained at \(.215\),
which is greater than \(-143\). It follows that
\[
 \mathcal A(1.7+y)>3.47+20.92y-143y^2>1.
\]
The last polynomial is concave, and both of its endpoint values exceed
\(1\). This proves (8), then (7), and finally \(F_{bb}<0\).

Both geometric halves have now been proved. The five former contact
curvature rows are replaced by (3)--(8) on the entire contact domain.
Thus the contact minimum has one of the four boundary types in Section 1.

## 4. The endpoint-angle curve has a positive fourth derivative

It remains to replace the derivative rows on \(x=.7\). Put
\(c=\cos(.7)\), \(s=\sin(.7)\), and let \(B(b)\) be (1) at
that fixed angle. Feasibility \(B\le d\) implies \(b<.76\).
Write
\[
 k=B'=cr+s,\quad k_1=B''=\frac{cQ}{u^3},\quad
 k_2=B'''=\frac{3cQv}{u^5},\quad
 k_3=B''''=\frac{3cQ(Q+4v^2)}{u^7}>0.
\]
All are positive. For
\(J(b)=\pi/2-.7-P(b)+T(B(b))\), the chain rule gives
\[
 J''''=-P''''+T''''k^4+6T'''k^2k_1
                +T''(3k_1^2+4kk_2)+T'k_3.                  \tag{9}
\]
We show that its right side is positive on the whole feasible interval.

First, \(B(b)>b\). Indeed the source circle and Cauchy--Schwarz give
\[
 B-b=1+c-cu-(1-s)v
 \ge1+c-\sqrt{2Q(1-s)}>0.                                   \tag{10}
\]
For either label \(P,T\), its fourth derivative is the same increasing
positive function of its argument, multiplied respectively by
\(.11055\) or \(.95769\):
\[
 P''''(b)=\frac{3Q(.11055)(5Qv-Q/2-2v^2)}{u^7}.
\]
The positivity of its next derivative follows from
\(5Q(Q-3v/2)+10v^2(3Q-v)>0\), as in
`HAND_WRONG_0011011_SAME_SIGN_OUTER_WITHOUT_TABLES.md`.
Consequently (10) implies \(T''''(B)>8P''''(b)\).
Also \(k>.84\), so
\[
                         T''''k^4>P''''.                    \tag{11}
\]

For the middle terms of (9), define
\[
 R_1=\frac{3k_1^2+4kk_2}{6k^2k_1}
     =\frac{k_1}{2k^2}+\frac{2k_2}{3kk_1}.
\]
We have the single global bound \(R_1<1.2\). To see it, set
\(K=cv+su\), so
\[
                    R_1=\frac{cQ}{2uK^2}+\frac{2v}{uK}.
\]
On \(.5\le v\le1.26\), \(K\) increases because
\(c-sv/u>0\); its left endpoint exceeds \(1.615\).
The function \(uK=cuv+s(Q-v^2)\) is concave in \(v\).
Its two endpoint values exceed \(2.96\), so it exceeds \(2.96\)
throughout. Therefore
\[
 R_1<\frac{.765Q}{2(2.96)(1.615)}+\frac{2(1.26)}{2.96}<1.2.    \tag{12}
\]
There is no domain partition in this estimate.

The increasing target coordinate begins at \(B(0)>.122\).
The scalar derivative formulas give on its whole range
\(T''> -1.14\) and \(T'''>1.73\). If \(T''\ge0\), the middle
terms of (9) are positive immediately. If \(T''<0\), (12) gives
\[
 6T'''k^2k_1+T''(3k_1^2+4kk_2)
 =6k^2k_1(T'''+T''R_1)
 >6k^2k_1(1.73-1.14(1.2))>0.                                \tag{13}
\]
Equations (9), (11), (13), and \(T'k_3>0\) prove
\[
                             J''''>0                        \tag{14}
\]
over the full feasible endpoint-angle curve.

## 5. The entire endpoint-angle minimum

Equation (14) makes \(J''\) convex. Its two endpoint values on
\([0,.2]\) satisfy \(J''(0)<-.51\), \(J''(.2)<-.48\); hence
\(J''<0\) throughout that interval. It also makes \(J'''\)
increasing. Since \(J'''(.2)>.60\), \(J''\) increases over the
feasible part of \([.2,.76]\). These conclusions replace all five endpoint-derivative
rows in the old proof.

The endpoint comparison \(J'(.6)<0\) now excludes an interior minimum
on \([0,.6]\): on its initial concave part a critical point is not a
minimum, and a later critical point with nonnegative second derivative
would force \(J'(.6)>0\). The endpoint costs exceed \(.9\) at
\(b=0\) and \(.906\) at \(b=.6\).

On the remaining feasible interval, \(J''\ge J''(.6)>.65\).
The single reference \(b=.72365\) lies on this interval and satisfies
\[
 J(.72365)>.89778507,\qquad |J'(.72365)|<10^{-6}.
\]
The integrated tangent bound gives on the whole interval
\[
 J>.89778507-\frac{10^{-12}}{1.3}>.89778.                      \tag{15}
\]

## 6. Complete scope

The aligned minimum is proved by Section 2. Sections 3--5 supply the
entire contact concavity and endpoint-angle shape needed for the final
lower-half axis. The other original axes and contact boundaries retain
the explicit analytic arguments listed in Section 1. These exhaust the
four original axes and their full closed angle intervals, including
possible ties. The common pair bound is strictly greater than
\(.89777\), as required.

Every uniform inequality above is derived by calculus, circle identities,
or the explicit polynomials (6) and (8), with visible whole-domain bounds.
None uses an interval row or an asserted verifier result. The inherited
endpoint comparisons can be checked by rational squaring and alternating
Taylor bounds. No Lean source or generated certificate has been changed
or run.
