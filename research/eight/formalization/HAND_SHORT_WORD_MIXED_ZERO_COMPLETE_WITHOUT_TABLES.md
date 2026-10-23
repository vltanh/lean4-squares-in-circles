# Complete mixed zero-quarter component of 0010111 without angle tables

This note supplies the table-free successors to
../SHORT_WRONG_WORD_ALL_MIXED_ZERO_HAND_PROOF.md and
../SHORT_WRONG_WORD_MIXED_ZERO_FAMILIES_HAND_PROOF.md. Its theorem concerns
an actual seven-cycle after frame concentration and the independent
zero-primary cyclic exclusion. Every possible mixed zero-quarter edge
then has corrected cost greater than .898.

Both radial orders, original signed axes, weak contacts, zero coordinates,
and core joins are retained. The primary zero branches are absent by the
prior cycle theorem, not by a claim about unrelated isolated pairs.
No candidate tangent cut or mismatch threshold is assumed. Every decimal
is an exact rational; no angle table, coefficient row, or checker status
is a premise.

## 1. Geometry and the zero-primary input

Put
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad
 a(y)=\sqrt{Q-(y+1/2)^2}-1/2,\quad
 d=\sqrt{Q/2}-1/2,\quad a_0=a(0),\quad d_c=1/2+\sqrt2/24.
\]
The outer arc has \(a=a(b),0\le b\le d\). The core consists of the
side \(a=7/12,0\le b\le1/2\) and corner
\((a-1/2)^2+(b-1/2)^2=1/144\), \(a\ge b\ge1/2\).
Use the parents' exact signed affine role labels and original axes.
A zero edge has \(|\phi|\le.7\), physical center gap greater than .76,
and width \(W=(1+|\sin\phi|+\cos\phi)/2\).

HAND_ZERO_PRIMARY_CYCLIC_EXCLUSION applies to this same closed seven-cycle
using G1 and the closed frame tour only. It excludes every feasible
original primary zero axis, including primary axes tied with transverse
ones. Reflection/reversal interchanges the two remaining transverse
axes, reverses both signs, and preserves angle and corrected cost by
negating the reversed labels.

The exact inventory in Section 1 of ALL_MIXED_ZERO has 28 transverse and
28 primary directed branches. Four transverse negative-outer to
negative-core branches are impossible because the target core has norm
less than .8. The remaining transverse inventory has four negative-core
to negative-outer, four positive-outer to positive-core, four positive-core
to positive-outer, and twelve opposite-sign branches. These counts already
include the reflected radial orders.

## 2. Four negative-core to negative-outer transverse families

After the stipulated reflection/reversal their costs and separators are
\[
 C=\phi+c-gb-pA+qB,\qquad -b+A\sin\phi+B\cos\phi\ge W.
\tag{1}
\]
The exact tuples \((c,p,q,g)\) are
\[
\begin{aligned}
 &(-.11418,.09133,.88074,.62095),\\
 &(.07943,.19335,.76744,.62750),\\
 &(-.25648,0,.94766,.62095),\\
 &(-.94615,-.51554,1.19909,.58829).
\end{aligned}
\tag{2}
\]
Nonpositive \(\phi\) is infeasible since its projection is at most
\(B<1\). For positive \(\phi\), the outer projection increases with
\(B\), so its largest value is \(d(\sin\phi+\cos\phi)\).
Let \(\phi_0\) be the unique event
\[
 (d-1/2)(\sin\phi_0+\cos\phi_0)=1/2,\qquad
 .30243<\phi_0<.30244.
\tag{3}
\]
The left side increases on \([0,.7]\), and the two point signs prove the
bracket. Feasibility requires \(\phi\ge\phi_0\).

The largest permitted source coordinate is
\[
 b_*:=A\sin\phi+B\cos\phi-W
 \le(d-1/2)(\sin\phi+\cos\phi)-1/2<.064<1/2.
\]
The cost decreases with \(b\), so use \(b=b_*\). This is an actual
core-side state, and proves that no core-corner source has been omitted.
The feasible target interval begins at the unique zero-source point
\(B=B_z(\phi)\) and ends at \(B=d\).
The reduced target derivative is
\[
 q-g\cos\phi+(p+g\sin\phi)r(B),\qquad
 r(B)=(B+1/2)/(a(B)+1/2).
\tag{4}
\]
It is positive for the first three tuples, since \(p\ge0,q>g\).
For the fourth, \(p+g\sin\phi<0\), so the reduced target functional
is concave. Hence only \(B_z\), and in the fourth case also \(d\),
can minimize the cost.

### 2.1. Geometric curvature of the entire zero-source arc

Set \(s=\sin\phi,k=\cos\phi,m=s+k,n=k-s\), and
\[
 Z=1/2+m,\quad Y=\sqrt{Q-Z^2},\quad
 U=Zs+Yk,\quad V=Zk-Ys,\quad B_z=V-1/2.
\]
This is exactly the contact \(A\sin\phi+B\cos\phi=W\).
With \(f=1-n/Y\), direct differentiation gives
\[
 U'=Vf,\quad V'=-Uf,\quad
 f'=\frac{m(Q-9/4)-m^2/2-1}{Y^3}>0.
\tag{5}
\]
Indeed \(1.252<m<1.41\), and its numerator is positive at 1.252 and
increases on this range. Also \(Y^2-n^2=Q-9/4-m>0\), hence \(f>0\).
The endpoint comparisons and these monotonicities give throughout
\(1.399<U<1.629\), \(V>1.124\). Therefore the purely geometric bound is
\[
 B_z'<0,\qquad
 -\frac{B_z''}{(B_z')^2}
 =\frac V{U^2}+\frac{f'}{Uf^2}
                  >\frac{1.124}{1.629^2}>.423.
\tag{6}
\]
This bound is independent of the choice of cost coefficients and can
also be used for other labels on this same actual contact arc.

The target label \(L(B)=-pa(B)+qB\) increases. It is concave if \(p<0\);
otherwise \(L''/L'\le.19335(1.431)/.76744<.361\).
Thus (6) proves that \(\phi+c+L(B_z(\phi))\) is strictly concave on
the entire interval \([\phi_0,.7]\). Its initial value is
\(\phi_0+c+(q-p)d>.89808\), and all four final values exceed 1.032.
The whole zero-source boundary is therefore above .89808.

For the fourth tuple, the target-diagonal cost is
\[
 \phi+c+(q-p)d+g/2-g(d-1/2)(\sin\phi+\cos\phi).
\]
It increases strictly, since its derivative exceeds \(1-.6275(.4)>0\).
Its initial value is the same zero-source contact. This completes all
four families (1), without the historical multiplier/angle rows.

## 3. Opposite-sign core-source positive-angle families

This replaces Section 4.2 of ALL_MIXED_ZERO. Its six normalized costs
and original transverse separators are
\[
 C=\phi+c+gb-pA+qB,\qquad
 b+A\sin\phi+B\cos\phi\ge W,\quad0\le\phi\le.7.
\tag{7}
\]
The exact tuples \((c,p,q,g)\) are
\[
\begin{aligned}
0&:(.14041,0,.94766,.62095),\\
1&:(-.21286,-.13422,1.03828,1.08816),\\
2&:(-.05550,0,.99940,1.13855),\\
3&:(.28271,.09133,.88074,.62095),\\
4&:(-.72700,-.51554,1.19909,1.04073),\\
5&:(.27632,.19335,.76744,1.04729).
\end{aligned}
\tag{8}
\]
Choose \(\lambda=q\) in row 0, \(\lambda=.93\) in row 3, and
\(\lambda=g\) otherwise. Every multiplier is constant on its entire
family and satisfies \(\lambda\ge g\).
After subtracting its separator margin, the core term is at least
\((g-\lambda)d_c\), and the outer functional has coefficients
\[
 X=-p-\lambda\sin\phi,\qquad Y=q-\lambda\cos\phi.
\tag{9}
\]
Its axial, diagonal, and whole-circle lower envelopes are
\[
\begin{aligned}
 F_A={}&\phi+c+(g-\lambda)d_c-pa_0+\lambda/2
       +(\lambda/2)\cos\phi-\lambda(a_0-1/2)\sin\phi,\\
 F_D={}&\phi+c+(g-\lambda)d_c+(q-p)d+\lambda/2
       -\lambda(d-1/2)(\sin\phi+\cos\phi),\\
 F_N={}&\phi+c+(g-\lambda)d_c+(\lambda+p-q)/2
       +\lambda(\sin\phi+\cos\phi)-R\sqrt{X^2+Y^2}.
\end{aligned}
\tag{10}
\]

### 3.1. Endpoint envelopes on the whole angle interval

Every \(F_D\) increases, since \(F_D'>1-.4\lambda>0\).
Its value at zero exceeds .89810 for rows 1,2,4,5, the cases in which
that endpoint will be used. The smallest is row 5's exact value
\(c+(q-p)d+g(1-d)>.8981019\).
For rows 0 and 3,
\[
 F_A'\ge1-\lambda\sqrt{1/4+(a_0-1/2)^2}
                   >1-.948(1.043)>0.
\]
Their initial values exceed .90546 and .91078. For rows 1,2,4,5, use
\(\lambda<1.139\), so \(F_A'>-.19\), while \(F_A(0)>1.04\).
Thus these entire axial envelopes satisfy
\[
                       F_A>1.04-.7(.19)=.907>.898.
\tag{11}
\]

### 3.2. Intrinsic support transitions

Row 0 has \(X\le0,Y\ge0\), so its minimum is always axial.
Row 4 has \(Y>0\); if \(X\ge0\), its outer functional is concave,
and if \(X<0\), it increases. Thus its minimum is always an endpoint.
These two rows are already covered by Section 3.1.

For rows 1,2,5, the diagonal derivative
\(Y-X=p+q+\lambda(\sin\phi-\cos\phi)\) increases strictly from a
negative value at zero to a positive value at .7. It has exactly one
zero \(\phi_d\). At that zero \(X=Y<0\): otherwise one would have
\(p^2+q^2\ge\lambda^2\), contrary to their exact coefficients.
Before \(\phi_d\), the target functional decreases up to the diagonal,
so its minimum is \(F_D\). Afterwards \(X<0\), making it strictly
convex in the target coordinate.

Let \(\rho=1/[2(a_0+1/2)]\). The axial derivative
\[
 Y-\rho X=q+\rho p+\lambda(\rho\sin\phi-\cos\phi)
\]
also increases strictly. At \(\phi_d\) it is \((1-\rho)X<0\), and
at .7 it exceeds .19 for all three tuples. Hence it has exactly one
zero \(\phi_a\in(\phi_d,.7)\). Between the events, the unique
whole-circle minimizing point lies on the actual outer arc, because
its slope ratio lies between \(\rho\) and 1. Its cost is exactly
\(F_N\), and the supports agree at the events:
\[
 F_N(\phi_d)=F_D(\phi_d),\qquad F_N(\phi_a)=F_A(\phi_a).
\tag{12}
\]
After \(\phi_a\), the minimum is axial.

Row 3 has \(X<0\) throughout, with positive diagonal and negative
axial derivatives at zero. Its minimum initially is interior; the
strictly increasing axial derivative has one zero before .7. Its
support is \(F_N\) up to that event and \(F_A\) afterwards, with
\(F_N(0)>.904935\).

All four norm-using tuples have \(\lambda>\sqrt{p^2+q^2}\). Their
norms are nonzero and obey
\[
 N''+N/4\ge0,\qquad N\le\lambda+\sqrt{p^2+q^2}.
\]
As \(R<2\) and \(\sin\phi+\cos\phi\ge1\),
\[
 F_N''< -\lambda+
           (\lambda+\sqrt{p^2+q^2})/2<0
\tag{13}
\]
on the whole angle interval. Thus every intrinsic interior-support
branch has its minimum at the two event endpoints, or at zero for
row 3. Those values are bounded by (11)--(12), the diagonal bounds,
and row 3's initial norm value. This proves all six whole families
(7), without prescribing any numerical support-transition intervals.

## 4. Precisely retained full-domain transverse proofs

Only the following analytic portions of the parents are imported.

The six opposite-sign outer-source negative-angle families are Section 3
of MIXED_ZERO_FAMILIES. Their original separator forces the whole feasible
range \(0\le x<.44152\). Four rows have one increasing secant/tangent
envelope. Of the other two, one has a concave first derivative starting
positive and hence an endpoint minimum; the other has a uniformly negative
third derivative and one strongly concave derivative reference. These
are complete-domain arguments, not multiplier/angle rows. Their least
reserve is greater than .8981083.

The six complementary core-source negative-angle families are Section 4.1
of ALL_MIXED_ZERO. Its actual contact is monotone or concave in the target.
The two endpoint curves are strictly concave or have a fixed derivative
sign throughout their feasible range \(0\le x<.32\). Its finite list
only evaluates endpoints of six different role functions; the least
reserve exceeds .8981019.

The six outer-source opposite-sign positive-angle families are Section 5
of ALL_MIXED_ZERO. Two constant supports are increasing over the whole
positive half. The other four use one smooth multiplier \(g/\cos\phi\)
and an increasing whole-half secant/tangent envelope. There is no change
of multiplier on angle cells.

The four positive-outer/positive-core transverse families are Section 6
of ALL_MIXED_ZERO. Feasibility forces \(\phi>.4\) and excludes the core
corner. Actual source-coordinate monotonicity or concavity reduces every
state to its side endpoints, with strict lower bounds above .898 on
the whole feasible interval.

The four positive-core/positive-outer transverse families are Section 7
of ALL_MIXED_ZERO. Feasibility again forces \(\phi>.4\). Three whole-circle
supports have initial value greater than .98 and derivative greater than
-.27, yielding .899 over the entire remaining length .3. The fourth has
an axial support with the stronger bound .98. No continuous-domain table
occurs in these arguments.

The four impossible negative-outer/negative-core transverse branches
follow from the core norm bound in Section 1. Section 2 above supplies
the missing same-sign families and Section 3 supplies the missing
opposite-sign positive-angle supports. This exhausts the exact transverse
inventory, with the reflected radial orders as stated in the parents.

## 5. Complete actual-cycle assembly

Fix a radial and signed representation for each vertex once and use it
at both incident edges. The original reflection/reversal identities
restore the second transverse owner while preserving each corrected cost.
All 28 original transverse branches are impossible or have cost greater
than .898 by Sections 2--4. The other 28 mixed branches are primary zero
separators and are absent by the independent actual-cycle theorem.
Therefore every mixed zero-quarter edge of the actual 0010111 cycle has
\[
                        \phi+\ell_s-\ell_t>.898.
\]
Both angle signs, both full core pieces, weak original owners, coordinate
endpoints, and all ties are included. This is deliberately a cycle-scoped
theorem: it does not assert the same label inequality for an omitted
isolated primary pair.

The fixed comparisons in Sections 2--3 are substitutions of the printed
tuples into endpoint formulas or monotone event equations. Positive rational
squaring bounds the roots; adjacent alternating sine/cosine sums at .30243,
.30244, and .7 give the required point bounds. The continuous arguments
are contact curvature (5)--(6), monotone endpoint supports (11), and the
whole norm curvature (13). The intrinsic events are proved to exist and
be unique, and their costs are bounded by matching supports. No numerical
location or bracket sequence for those events is assumed.
