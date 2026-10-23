# Four unfavorable same-sign zero owners: one support and one intrinsic event

This note completes the table-free zero-quarter outer/outer dependency
for the original owners
\[
 (0,++,3),\quad(1,--,1),\quad(3,++,3),\quad(3,--,1)
\]
of the word 0010111. Each has corrected cost greater than 1.03 on its
whole feasible angle domain. Every decimal is an exact rational.

The first five sections of
../SHORT_WRONG_WORD_OUTER_ZERO_PRIMARY_HAND_PROOF.md are not needed for
primary owners in the present actual-cycle assembly: those owners are
already absent by HAND_ZERO_PRIMARY_CYCLIC_EXCLUSION. Its last four
secondary families, however, are genuinely separate obligations. The
argument below proves all four without that note's prescribed .5 split.

## 1. Exact coefficients and feasible domain

Set
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad
 a(B)=\sqrt{Q-(B+1/2)^2}-1/2,\quad
 d=\sqrt{Q/2}-1/2,\quad a_0=a(0).
\]
Reflection and reversal normalize every stated original owner to
\[
 C=\phi+c+pa-qb-PA+tB,
 \qquad -b+A\sin\phi+B\cos\phi\ge W,
\]
\[
 W=(1+|\sin\phi|+\cos\phi)/2,\qquad A=a(B),\ a=a(b),
 \quad0\le b,B\le d.
\tag{1}
\]
The exact tuples \((c,p,q,P,t)\), in the same order, are
\[
\begin{aligned}
 &(-.06130,0,.99940,0,.94766),\\
 &(.27086,-.13422,1.03828,.09133,.88074),\\
 &(-.75097,0,.71553,-.51554,1.19909),\\
 &(.74349,-.33147,1.13360,.19335,.76744).
\end{aligned}                                               \tag{2}
\]
The reflection preserves the original corrected cost and angle; it
merely exchanges the original secondary owners and their stated labels.

Nonpositive \(\phi\) is impossible: its projection is at most \(B<1\).
For \(0<\phi\le.7\), the target projection increases with \(B\), since
\(\cos\phi-r(B)\sin\phi>0\). Consequently feasibility requires
\[
 (d-1/2)(\sin\phi+\cos\phi)\ge1/2.
\]
The left side increases and is still smaller than 1/2 at .3.
Thus every possible state has \(.3<\phi\le.7\).

## 2. One multiplier on the whole domain

Subtract twice the nonnegative separator margin in (1).
The source functional is \(pa+(2-q)b\), whose exact arc minimum is
\(pa_0\), because \(p\le0\) and \(2-q>0\).
The remaining target coefficients are
\[
 X=-P-2\sin\phi,\qquad Y=t-2\cos\phi.
\]
Full-circle support gives
\[
 C\ge F(\phi):=\phi+c+pa_0+(2+P-t)/2
             +2(\sin\phi+\cos\phi)-RN,
\]
\[
 N^2=P^2+t^2+4+4(P\sin\phi-t\cos\phi).
\tag{3}
\]
Every tuple satisfies \(\sqrt{P^2+t^2}<1.31<2\), so \(N>0\).
The exact norm identity and triangle inequality imply
\[
 N''+N/4=\frac{(P^2+t^2-4)^2}{4N^3}\ge0,\qquad N<3.31.
\]
Since \(R<2\) and \(\sin\phi+\cos\phi\ge1\),
\[
 F''\le-2(\sin\phi+\cos\phi)+RN/4
                  <-2+2(3.31)/4<0.                        \tag{4}
\]
Thus the scalar is strictly concave on its whole angle domain.
For the first, second, and fourth tuples, its two endpoint values at
.3 and .7 are greater than 1.03. They are direct substitutions into
(3), using positive square-root brackets and alternating trigonometric
series at these two rational angles. Concavity proves all three complete
families.

## 3. The third tuple: the actual diagonal-to-circle transition

For the third tuple,
\[
 X=.51554-2\sin\phi<0\quad(.3\le\phi\le.7),\qquad
 Y-X=.68355+2(\sin\phi-\cos\phi).
\]
The second expression is strictly increasing; it is negative at .3 and
positive at .7. Let \(\phi_d\in(.3,.7)\) be its unique zero.
This is the intrinsic angle at which the target support leaves its
outer diagonal, not a chosen endpoint of an angle table.

For \(.3\le\phi\le\phi_d\), the target functional decreases with
\(B\): its derivative is \(-Xr(B)+Y\le Y-X\le0\).
The exact diagonal support therefore gives
\[
 C\ge D(\phi):=\phi+c+pa_0+1+(\sin\phi+\cos\phi)
                 +d\{-P+t-2(\sin\phi+\cos\phi)\}.
\tag{5}
\]
It increases throughout, because
\(D'=1-2(d-1/2)(\cos\phi-\sin\phi)>1-2(.4)>0\).
Its initial value satisfies \(D(.3)>1.09\).

At \(\phi_d\), the two target coefficients are equal and negative.
The full-circle minimizer is exactly \(A=B=d\), so
\[
                            F(\phi_d)=D(\phi_d)>1.09.
\]
On \([\phi_d,.7]\), the full-circle support (3) remains a valid lower
bound whether its minimizing point is on the outer arc or not.
Its whole-domain concavity (4) and its right endpoint value
\(F(.7)>1.19\) prove \(F>1.09\) throughout that interval.
This completes the third family, including its transition and all
state endpoints.

## 4. Exact scope

The four stated original secondary owners are now proved on their full
continuous domains. The only nonconstant event was defined by the
strictly increasing expression \(Y-X\), and the two exact supports agree
there. No numerical location of that event is used. The other fixed
comparisons evaluate only the endpoints of globally concave or monotone
functions. The proof uses no continuous-state table, coefficient-sign
appendix, or checker status.

Together with HAND_SHORT_WORD_OUTER_ZERO_SAME_WITHOUT_TABLES,
HAND_SHORT_WORD_OUTER_ZERO_OPPOSITE_WITHOUT_TABLES, and the independent
actual-cycle zero-primary exclusion, this exhausts all 28 original
outer/outer zero-quarter branches of 0010111.
