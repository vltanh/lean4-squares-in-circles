# Negative-core quarter contacts and the complete mixed-quarter assembly

This note replaces Sections 7--9 and both polynomial appendices of
../SHORT_WRONG_WORD_ALL_MIXED_ONE_HAND_PROOF.md. Together with
HAND_SHORT_WORD_MIXED_QUARTER_CIRCLE_AND_SIDE_CONTACTS_WITHOUT_TABLES.md
and the precisely identified analytic parts of the parent, it proves all
96 original mixed quarter-one owner families of 0010111, on their whole
closed angle domains, with corrected cost greater than .898.

Every terminating decimal denotes an exact rational. No angle partition,
Bernstein coefficient row, numerical minimum, or checker result is a
premise. The finitely many coefficient tuples are the intrinsic signed
role cases; every estimate below covers its entire continuous domain.

## 1. The six exact remaining rows

Put
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad
 a(y)=\sqrt{Q-(y+1/2)^2}-1/2,\quad d=\sqrt{Q/2}-1/2,
 \quad a_0=a(0),
\]
\[
 a_c=7/12,\quad d_c=1/2+\sqrt2/24,\quad \ell=\pi/2-.7.
\]
The source is outer. The target is on the core side
\(A=a_c,0\le B\le1/2\), or corner
\((A-1/2)^2+(B-1/2)^2=1/144\), \(A\ge B\ge1/2\).
The original source-primary separator and corrected cost are
\[
 a-A\cos\phi+B\sin\phi\ge W,\qquad
 C=\phi+c+pa-qb+gB,
 \quad W=\frac{1+\sin\phi+|\cos\phi|}{2}.                 \tag{1}
\]
After the parent's pointwise source-sign dominance, the exact remaining
indices and tuples \((c,p,q,g)\) are
\[
\begin{aligned}
0 &: (.12917,.09133,.88074,.62750),\\
4 &: (-.24510,.19335,.76744,.95269),\\
11&: (.23364,0,.86884,.58829),\\
12&: (.21928,-.20967,.83048,.99173),\\
19&: (.23152,-.21826,.83472,.99195),\\
23&: (.09072,0,.94766,.95324).
\end{aligned}                                             \tag{2}
\]
All have \(q>.767\) and \(-.263<p/q<.253\).
Regard the source label as a function of its primary coordinate:
\[
 M(a)=pa-q\left(\sqrt{Q-(a+1/2)^2}-1/2\right).
\]
If \(u=a+1/2\), \(v=\sqrt{Q-u^2}\), then
\[
 M'=p+qu/v>0,\qquad M''=qQ/v^3>0                            \tag{3}
\]
on the whole continued height range \(u\ge1.32\) used below, up to
the actual outer axial endpoint. Positivity follows already from
\(u/v>.89>.263\).

## 2. One curvature proof for every core endpoint

The target side join and core diagonal have the respective data
\[
 (A_*,B_*,b_C)=(13/12,0,1/2),
 \qquad(d_c+1/2,d_c-1/2,d_c).
\]
Their continued source-contact height and cost are
\[
 u=1+A_*\cos\phi-B_*\sin\phi,
\]
\[
 H(\phi)=\phi+c+p(u-1/2)-q(\sqrt{Q-u^2}-1/2)+g b_C.       \tag{4}
\]
For both endpoints \(K=A_*^2+B_*^2>K_0=1.12479\).
On the whole height range \(1.32\le u\le1.7\), differentiation gives
\[
 \frac{v^3}{q}H''
 =Q\{K-(u-1)^2\}-u(u-1)v^2-(p/q)(u-1)v^3.                \tag{5}
\]
Define the following explicit polynomials:
\[
\begin{aligned}
 E(u)&=Q\{K_0-(u-1)^2\}-u(u-1)(Q-u^2),\\
 A(u)&=.65/.767+.253(u-1),\\
 P(u)&=E(u)^2-A(u)^2(Q-u^2)^3.
\end{aligned}                                             \tag{6}
\]
The cubic derivative of the quartic \(E\) is \(E'''=24u-6>0\).
Thus \(E'\) is convex. Its two endpoint values are negative:
\(E'(1.32)<-4.95\), \(E'(1.7)<-3.89\). Hence \(E\) decreases
and \(E(u)\ge E(1.7)>1.265>0\). Also \(A>0\).

Here is a single square-completion proof of \(P>0\), instead of the
old coefficient table. Set \(t=u-1.5\), so \(|t|\le.2\).
Ordinary rational expansion of the expression (6) gives
\[
\begin{aligned}
P(1.5+t)>{}&.3523-.3401|t|\
 &+t^2\{7.2993-9.210|t|-27.193t^2
                    -20.885|t|^3-11.069|t|^5\}.           \tag{7}
\end{aligned}
\]
For direct checking, the coefficients at degrees 0 through 5 are,
respectively, greater than .3523, greater than -.3401, greater than
7.2993, greater than -9.210, greater than -27.193, and between 0 and
20.885. The coefficient of degree 6 is positive, that of degree 7
is between 0 and 11.069, and that of degree 8 is positive. These
statements are direct multiplications in (6), not values at state
points. Bounding the odd powers by their absolute values proves (7).
The brace in (7) exceeds 4.19 throughout \(|t|\le.2\). Consequently
\[
 P>.3523-.3401|t|+4.19t^2
       \ge .3523-\frac{.3401^2}{4(4.19)}>.345>0.             \tag{8}
\]
Since both sides are positive, (6)--(8) imply \(E>A v^3\).
Substitution in (5), with \(q>.767\), proves uniformly
\[
                              H''>.65.                    \tag{9}
\]

This one estimate controls all twelve intrinsic endpoint curves.
The reference pairs (join, diagonal) for indices 0,4,11,23 are
\[
 (1.17,1.075),\quad(1.149,1.047),\quad(1.061,.962),
                  \quad(1.148,1.056),                     \tag{10}
\]
respectively. Literal evaluation of (4) and its derivative gives
\[
                        H(r)-H'(r)^2/1.3>.89809            \tag{11}
\]
for each of these eight references. For indices 12 and 19, both
curves instead satisfy \(H(\ell)>.89809\) and \(H'(\ell)>0\).
Integrating (9) and completing a square, or integrating the positive
initial derivative in the latter cases, proves every curve strictly
above .89809 on its whole relevant domain. The comparisons (11)
concern one point of each genuinely different endpoint curve, not a
partition of a moving angle or state.

## 3. Every lower-half corner contact

If \(\phi\ge1.2\), the direct actual-coordinate bound is enough:
\[
 C\ge\phi+c+(p-q)d+g/2>.915                                \tag{12}
\]
for every tuple (2). This uses \(a\ge d\), \(b\le d\), monotonicity
of \(M\), and \(B\ge1/2\). At \(\phi=1.2\), the six expressions
on the right exceed .9330, .9150, .9465, .9798, .9806, and .9151.
Thus any possible cost at most .898 must have \(\phi<1.2\).

On \(\ell\le\phi\le1.2\), the original separator requires
\[
 a\ge h(B):=W+A(B)\cos\phi-B\sin\phi.
\]
The height \(u=h(B)+1/2\) decreases in \(B\) and \(\phi\).
Its two extreme endpoint comparisons give \(1.32<u<1.7\).
By (3), the original cost is bounded below by
\(\phi+c+M(h(B))+gB\), even when the continued source coordinate
\(h(B)\) lies below \(d\).

We prove this lower contact cost strictly concave in the core
coordinate on the **whole** early domain. Set
\[
 D(u)=(Q-u^2)\{u-.263\sqrt{Q-u^2}\}.
\]
Then
\[
 \frac{M''}{M'}\le\frac Q{D(u)},\qquad
 D''=-6u+.789\frac{Q-2u^2}{\sqrt{Q-u^2}}<0.
\]
The last sign follows from \(u\ge1.32\), \(\sqrt{Q-u^2}>1.01\),
and the upper bound \(Q-2u^2\le Q-2(1.32)^2\).
The endpoint comparisons \(2.8D(1.32)>Q\), \(2.8D(1.7)>Q\)
and concavity give
\[
                              M''/M'<2.8.                 \tag{13}
\]
On the core corner write \(w=(B-1/2)/(A-1/2)\in[0,1]\).
Then
\[
 A'=-w,\quad -A''=12(1+w^2)^{3/2},\quad
 |h_B|^2=(\sin\phi+w\cos\phi)^2\le1+w^2.
\]
Cauchy's inequality is essential here: it retains the same \(w\)
in the first and second derivative terms. Since \(\cos\phi>.362\),
(13) yields
\[
\begin{aligned}
 [M(h(B))+gB]''
 &<M'(h)(1+w^2)\{2.8-12\cos\phi\sqrt{1+w^2}\}\\
 &<M'(h)(1+w^2)\{2.8-12(.362)\}<0.                        \tag{14}
\end{aligned}
\]
Every early corner therefore reduces to its join or diagonal, whose
whole costs were proved above .89809 in Section 2. Together with
(12), this proves all six complete lower-half corner families.
Neither of the two old ratio ranges, the late-corner support table,
nor Appendix B remains a premise.

## 4. The two straight-side families with small target slope

Take indices 0 and 11, and write \(x=\pi/2-\phi\), \(s=\sin x\),
\(k=\cos x\), \(c_0=13/12\). On the core side the least source
coordinate is the maximum of \(d\) and
\[
 a_c(x,B)=1/2+c_0s+(1/2-B)k.                               \tag{15}
\]
On a source-diagonal slack portion the cost increases with \(B\),
so reducing \(B\) reaches contact. At \(B=0\), (15) is at least 1,
so that contact is reached before the target becomes axial.
On an active contact,
\[
 C_B=-M'(a)k+g\le-(p+q)(.764)+g<0                          \tag{16}
\]
for both tuples. Hence increasing \(B\) decreases cost until the
target side join \(B=1/2\) or source diagonal \(a=d\).
There are exactly these two lower boundary alternatives.

Their common event is defined by
\(\sin x_j=(d-1/2)/c_0<.37\).
Before that event the source is diagonal and the target coordinate is
\[
 B=1/2-(d-1/2)\sec x+c_0\tan x.
\]
Its cost
\[
 D_0(x)=\pi/2-x+c+(p-q)d
          +g\{1/2-(d-1/2)\sec x+c_0\tan x\}
\]
is strictly decreasing. Indeed
\[
 k^2D_0'=s^2-g(d-1/2)s+gc_0-1
          <.37^2+.6275(13/12)-1<0.                        \tag{17}
\]
It therefore reduces to its join with \(B=1/2\).
After that event the endpoint cost is exactly the side-join curve
(4), throughout its physical height interval. Section 2 proves this
entire curve above .89809. Thus (16)--(17) prove both complete side
families, without the old four angle/multiplier rows.

## 5. The other four straight-side families: a single norm chord

For indices 4,12,19,23, subtract the nonnegative multiplier
\(\lambda=g/\sin\phi\) times (1). The target coefficient of \(B\)
cancels. The exact whole-circle source support gives
\[
 F(\phi)=\phi+c+\frac g{\sin\phi}+\frac{-p+q+g}{2}
       +\frac{13g}{12}\cot\phi
       -R\sqrt{(g/\sin\phi-p)^2+q^2}\le C.                \tag{18}
\]
We prove \(F>.898\) on the entire lower half, without squaring a
Taylor polynomial.

Again set \(x=\pi/2-\phi\), \(s=\sin x\), \(k=\cos x\), and let
\[
 K=\pi/2+c+(-p+q+g)/2-.898,
 \qquad N(k)=\sqrt{(g-pk)^2+q^2k^2}.
\]
The exact expression is
\[
 (F-.898)k=(K-x)k+g+(13g/12)s-RN(k).                       \tag{19}
\]
The norm is strictly convex in its scalar argument:
\(N_{kk}=g^2q^2/N^3>0\).
Let \(k_0=\cos(.7)\) and define its endpoint chord by
\[
 \beta=\frac{N(1)-N(k_0)}{1-k_0},\qquad
 \alpha=N(1)-\beta.
\]
Then \(N(k)\le\alpha+\beta k\) on the whole interval
\([k_0,1]\). Therefore (19) is bounded below by the single elementary
function
\[
 J(x)=(A-x)\cos x+B+C_0\sin x,
 \quad A=K-R\beta,\quad B=g-R\alpha,\quad C_0=13g/12.       \tag{20}
\]
For all four exact tuples,
\[
 .479<A<.691,\qquad1.032<C_0<1.075.
\]
Consequently
\[
\begin{aligned}
 J'&=(C_0-1)\cos x-(A-x)\sin x,\\
 J''&=(2-C_0)\sin x-(A-x)\cos x,\\
 J'''&=(3-C_0)\cos x+(A-x)\sin x\\
     &>(3-1.075)(.764)-(.7-.479)(.645)>1.3.                \tag{21}
\end{aligned}
\]
Thus \(J'\) is strictly convex and \(J''\) increases over the whole
angle domain. The common fixed comparisons are
\[
 J(0)>.0074,\qquad J'(.4)<-.001,\qquad J''(.4)>.09.         \tag{22}
\]
The four reference points, in the same index order 4,12,19,23, are
\(.416,.5735,.574,.4035\). At each corresponding reference \(r\),
\[
                        J(r)>.00062,\qquad |J'(r)|<.00005.
\]
On \([.4,.7]\), (21)--(22) give \(J''>.09\), and one square
completion gives
\[
                       J>.00062-\frac{.00005^2}{.18}>0.    \tag{23}
\]
On \([0,.4]\), the convex derivative ends negative. It cannot cross
from negative to positive before that endpoint, so \(J\) has no
interior minimum there. Its values at 0 and .4 are positive by (22)
and (23). Thus \(J>0\) everywhere; (19)--(20) prove (18) strictly
above .898 on the entire lower half for all four families.
This replaces all four degree-20 inequalities and every coefficient
in the old Appendix A by a norm chord and one derivative shape.

## 6. The whole upper half

For every tuple (2), put
\[
 S(g)=(g-p+q)/2-R\sqrt{(g-p)^2+q^2}.
\]
On \(\phi=\pi/2+x\), subtract \(g\) times the original separator.
The target coefficients are \(g\cos\phi\le0\) and
\(g(1-\sin\phi)\ge0\), so its exact core minimum is axial,
including both the side and corner. Hence
\[
 C\ge F_+(x)=\pi/2+x+c+S(g)+g/2+(g/2)\cos x-(g/12)\sin x.
\]
The initial values exceed .905 for every tuple, and
\[
 F_+'\ge1-1.139(.645/2+1/12)>0.
\]
This proves all six upper halves directly, including every core join
and simultaneous feasible owner.

## 7. The complete mixed-quarter theorem

The original parent note gives the exact finite normalization: 24
core-to-outer and 24 outer-to-core signed rows, each on two source
axes. Reflection/reversal restores the corresponding target axes,
with unchanged angle and corrected cost. Its source-sign comparison
for primary axes is pointwise dominance of the actual labels. Thus
its 48 primary rows reduce to 14 rows in each radial order, not to
an assumption about a vertex's sign in the cycle sum.

The complete analytic dependency substitution is as follows.

* Core-to-outer secondary, negative target: parent Section 3.1.
  Its explicit axial support has a whole-half derivative bound;
  the finite alternatives refer only to fixed role coefficients.
* Core-to-outer secondary, positive target: Section 1 of
  HAND_SHORT_WORD_MIXED_QUARTER_CIRCLE_AND_SIDE_CONTACTS_WITHOUT_TABLES.
  One norm comparison proves each entire half concave.
* Outer-to-core secondary, both target signs: parent Section 4.
  Its axial/core-circle supports and whole-half derivative estimates
  have no moving-domain table.
* Core-to-outer primary, both target signs: parent Section 5.
  Its impossible branches, full-angle monotonicity, and one concave
  loss function cover all side, corner, and angle endpoints.
* Outer-to-core primary, positive target: Section 2 of
  HAND_SHORT_WORD_MIXED_QUARTER_CIRCLE_AND_SIDE_CONTACTS_WITHOUT_TABLES.
  Exact state convexity and its one axial/interior contact event
  replace every old multiplier interval.
* Outer-to-core primary, negative target: Sections 2--6 above.
  The two side mechanisms, whole corner curvature, and increasing
  upper support cover every original case.

These are all normalized rows and original owners in the parent's
explicit inventory. It follows that **every one of the 96 original
mixed quarter-one owner families has corrected cost greater than
.898 on its entire angle range**, including weak contacts, both core
pieces, all state endpoints, and every reflection.
Only the stated table-free sections of the parent are used; neither
of its appendices nor a multiplier/angle subdivision is a premise.

## 8. Reproducible exact arithmetic and scope

All fixed comparisons have explicit inputs in (2), (4), (6), and
(18)--(22). Positive rational square brackets bound the radicals.
For the norm chord use the adjacent alternating series at .7 to bound
\(k_0\), and ordinary interval arithmetic on these fixed constants.
For the reference angles, alternating sine/cosine sums through degrees
19/21 and 18/20, respectively, suffice. The Machin bound
\(1.57079632679489<\pi/2<1.57079632679490\) is more than sufficient.
In particular the smallest reference in (23) is genuinely positive;
no rounding of a minimizing contact is assumed.

The variable-domain proofs are the exact polynomial bound (7)--(9),
the Cauchy curvature estimate (13)--(14), the side monotonicity
(16)--(17), the norm-chord derivative shape (21)--(23), and the upper
support derivative. The displayed fixed references serve only those
already proved global derivative statements.

This is the complete mixed **quarter-one** component. The full
0010111 contradiction additionally uses its mixed zero-quarter,
core/core, and outer/outer components and their cyclic cancellation.
