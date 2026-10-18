# Negative tangents on the source primary axis near a quarter turn

This corollary supplies an axis regime that is distinct from the
same-sign source-secondary theorem. It follows directly from the outer
endpoint and trigonometric inequalities in Sections 2.5 and 2.9 of
QUARTER_ZERO_ALL_BOUNDARY_STATES_HAND_PROOF.md.

Use \(Q=9789/2500,\ R=\sqrt Q,\ p=13/200,\ q=203/200\), and the
positive outer marker \(L(a,b)=-9/100+pa+qb\). Both positive states
\((a,b),(A,B)\) lie on the complete outer arc. Give both their negative
tangent signs and write \(\phi=\pi/2+x\), \(|x|\le7/10\).

The source negative-primary separator is
\[
 a+A\sin x+B\cos x\ge
 W=\frac{1+\cos x+|\sin x|}{2}.                           \tag{1}
\]
The cost to bound is
\[
 {\cal C}=\frac\pi2+x-L(a,b)+L(A,B).                      \tag{2}
\]
Then
\[
 \boxed{{\cal C}>\frac{39463631}{50000000}
                    >\frac{157}{200}.}                 \tag{3}
\]

To prove this, subtract \(\lambda=39/40\) times the nonnegative margin
in (1). The source circle support is
\[
 \frac{p+q+\lambda}{2}-R N_1,\qquad
 N_1=\sqrt{(p+\lambda)^2+q^2}.
\]
The target coefficients are \(p-\lambda\sin x\) and
\(q-\lambda\cos x>0\). The outer endpoint rule gives
\[
\begin{split}
 {\cal C}\ge\min\{F_a(x),F_d(x)\},\qquad
 F_a(x)&=\frac\pi2+x+\lambda W+\frac{p+q+\lambda}{2}
               -RN_1+(p-\lambda\sin x)a_0,\\
 F_d(x)&=\frac\pi2+x+\lambda W+\frac{p+q+\lambda}{2}
               -RN_1+(p+q-\lambda(\sin x+\cos x))d,
\end{split}                                             \tag{4}
\]
where \(a_0=\sqrt{Q-1/4}-1/2\), \(d=\sqrt{Q/2}-1/2\).

The differences \(F_a(x)-F_a(0)\) and \(F_d(x)-F_d(0)\)
are exactly the two differences proved nonnegative in Section 2.9
of the zero-quarter theorem, for the same \(\lambda=39/40\) and
the same \(a_0,d\). That proof treats both signs of \(x\) on the
entire interval. It also shows
\((p+q-\lambda)d\ge pa_0\), hence \(F_d(0)\ge F_a(0)\).
Thus (4) is at least
\[
 F_a(0)=\frac\pi2+\lambda+\frac{p+q+\lambda}{2}
                           +pa_0-RN_1.                 \tag{5}
\]

The root bounds already used in the neighboring quarter-turn notes are
\[
 \pi>3.14159,\quad pa_0>.0919,\quad
 R<1.979,\quad N_1<1.45322.
\]
Substitution into (5) gives the first value in (3), by rational
multiplication:
\[
 \frac{314159}{200000}+\frac{39}{40}+\frac{411}{400}
 +\frac{919}{10000}
 -\frac{1979}{1000}\frac{145322}{100000}
 =\frac{39463631}{50000000}.
\]
All root bounds are verified by squaring; the lower bound on \(\pi\)
has the shared alternating Machin-series proof. No additional
geometric or numerical case split is used.
