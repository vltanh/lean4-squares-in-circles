# Three polynomial inequalities for the nonaligned high/low pair

This is a hand proof of the scalar premise in
`HIGH_LOW_NONALIGNED_SUPPORT_FORMULA.md`. It replaces the longer curvature
argument by three explicit positive polynomials on one interval. All
terminating decimals below denote exact rational numbers.

Put

\[
 Q=9789/2500,\quad R=\sqrt Q,\quad
 \mu=.403875,\quad q=1.089065,\quad k=.569472,
 \quad v=.390886,\quad\beta=.18,
\]

\[
 c=\sqrt{Q/2}-1/2,\qquad a_0=\sqrt{Q-1/4}-1/2,
 \qquad c_L=-\mu a_0,\quad c_H=\pi/4+(k-v)c.
\]

For \(2/25\le x\le3/10\), define

\[
 l=.990906-.28x,\qquad
 n_1=\sqrt{k^2+(l-v)^2},
\]

\[
 n_2=\sqrt{\mu^2+q^2+l^2+2\mu l\sin x-2ql\cos x},
\]

\[
\begin{split}
 F(x)={}&x-\frac\beta2\cos x+\left(l-\frac\beta2\right)\sin x+l
 +c_H-c_L\\
 &+\frac{k-v+\mu+q+\beta}{2}-R(n_1+n_2).
\end{split}                                                   \tag{1}
\]

**Theorem.** Throughout this whole closed interval,

\[
 \boxed{F(x)>.8833.}                                           \tag{2}
\]

The cited separating-axis support reduction therefore proves the same
strict lower bound for the corrected high-positive to low-positive pair
cost on the source \(+f\) axis. Its state arcs were enlarged to their
full circles, so the implication uses no conjectured location of the
support minimizers.

## 1. Elementary trigonometric and constant bounds

Use the explicit polynomials

\[
 S=x-x^3/6+x^5/120-x^7/5040+x^9/362880,
\]

\[
 C=1-x^2/2+x^4/24-x^6/720+x^8/40320,\qquad e=10^{-11}.
\]

The alternating Taylor remainder and
\((3/10)^{10}/10!<e\), \((3/10)^{11}/11!<e\) give

\[
 S-e<\sin x<S,\qquad C-e<\cos x<C.                             \tag{3}
\]

Define

\[
 X_1=k^2+(l-v)^2,\qquad
 X_2=\mu^2+q^2+l^2+2l(\mu S-qC).
\]

Since \(0<l<1\) and \(\mu+q<3/2\),

\[
 n_1^2=X_1,\qquad |n_2^2-X_2|<3e.                             \tag{4}
\]

Squaring the positive proposed bounds gives

\[
 R<1.978788,\qquad c>.899214,\qquad a_0>1.414575.               \tag{5}
\]

We also use \(\pi>3.14159\), for which the short alternating-series
proof from Machin's identity is given in
`LOW_HIGH_ALIGNED_CONTACT_HAND_PROOF.md`.

## 2. Explicit upper bounds for both square roots

Write \(w=x-19/100\); thus \(|w|\le11/100\). Put

\[
\begin{split}
 P_1(w)={}&.7895001401-.1939323304w+.0258329638w^2\\
 &+.0063465589w^3+.0011353387w^4,\\
 P_2(w)={}&.6048369308+.9594403346w-.2050884018w^2\\
 &-.0610720222w^3+.0449392223w^4,
\end{split}
\]

\[
 U_1=P_1+10^{-7},\qquad U_2=P_2+10^{-6}.                        \tag{6}
\]

The triangle inequality applied to the four nonconstant terms gives
\(U_1>.76\) and \(U_2>.49\). The first two rows of the table below
prove

\[
 U_1^2-X_1>0,\qquad U_2^2-X_2-3e>0.
\]

Together with (4) and positivity of the \(U_i\), these imply

\[
 n_1<U_1,\qquad n_2<U_2.                                      \tag{7}
\]

These quartics are explicit proposed bounds, whose validity follows by
squaring. Their discovery requires no premise in the argument.

## 3. The remaining comparison is one positive polynomial

Define the degree-ten polynomial

\[
\begin{split}
 V={}&x-\frac\beta2 C+\left(l-\frac\beta2\right)(S-e)+l
       +\frac{3.14159}{4}\\
    &+(k-v)(.899214)+\mu(1.414575)
       +\frac{k-v+\mu+q+\beta}{2}\\
    &-1.978788(U_1+U_2)-.8833.
\end{split}                                                   \tag{8}
\]

All substitutions have the required direction: the coefficient of
\(\cos x\) in (1) is negative, the coefficient of \(\sin x\)
is positive, and \(k-v,\mu,U_1,U_2\) are positive. Equations
(3), (5), and (7) consequently give

\[
 F(x)-.8833>V(x).                                              \tag{9}
\]

Here is the complete polynomial check. In each row substitute
\(x=2/25+(11/50)y\), \(0\le y\le1\), and express the result
of degree \(n\) in the Bernstein basis
\(\binom nj y^j(1-y)^{n-j}\). The printed integers, divided by
the indicated denominator, are lower bounds for every coefficient in
increasing index order.

| Polynomial | Degree | Denominator | Positive lower coefficient numerators |
|---|---:|---:|---|
| \(U_1^2-X_1\) | 8 | \(10^8\) | 16, 16, 16, 15, 15, 15, 15, 15, 15 |
| \(U_2^2-X_2-3e\) | 10 | \(10^8\) | 85, 135, 111, 90, 96, 122, 147, 150, 126, 104, 157 |
| \(V\) | 10 | \(10^7\) | 4188, 2453, 1181, 382, 63, 225, 863, 1969, 3531, 5530, 7944 |

Every basis term is nonnegative and their sum is one. Every polynomial
in the table is therefore strictly positive. In particular
\(V\ge63/10^7>0\), proving (2).

For a direct rational check of any printed coefficient, if the
substituted power expansion is \(\sum_{j=0}^n a_jy^j\), its
Bernstein coefficient of index \(r\) is

\[
 b_r=\sum_{j=0}^r a_j\frac{\binom rj}{\binom nj}.              \tag{10}
\]

The definitions (6) and (8), followed by (10), specify all 31 finite
comparisons. The optional script
`verify_high_low_nonaligned_short_hand.py` reproduces them using exact
fractions only. The proof has one interval, three rows, and no numerical
minimization or unprinted subdivision calculation. \(\square\)
