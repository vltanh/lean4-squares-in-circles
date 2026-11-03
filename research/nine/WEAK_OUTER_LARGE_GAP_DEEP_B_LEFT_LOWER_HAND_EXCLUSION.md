# A sufficiently low B leaves no further original below it on the left

November 2, 2026. Complete conditional hand lemma, with exact rational
checks. No Lean, Lake, or CI. This is a placement restriction, not a
closure of the weak-outer fixed mask.

## 1. Original caller and the exact conclusion

Retain the original-nine `001/00` predicate at closed
`Q=1105/256`, with main originals A,B,C,D. As in the weak-outer
endpoint localization, put

\[
 \rho=91/60,\qquad r=\sqrt Q<133/64.
\]

Then the following implication holds:

> If `y_B<=-2/3`, there is no other original square I with
> `x_I<=0` and `y_I<=y_B`.

No additional comparison or bit is assigned to I. Its original frame
is arbitrary. The statement also applies to any selected original
distinct from B. The proof needs only physical center separation
and localization from the original main chain; it does not replace
the original predicate by a point-packing predicate.

## 2. Localization of the same original B

The first actual main comparison gives

\[
 x_B\ge x_A+h_A+h_B> -\rho+1=-31/60.
\]

The second actual comparison and the inherited right-edge bound for C
give

\[
 x_B+h_B\le x_C-h_C<r-2<5/64.
\]

Here the bound for C follows directly from the original C/D inset
comparison and containment:

\[
 x_C-h_C
 \le r-(h_D+g_D)-(h_C+g_C)\le r-2,
 \qquad g_i=1/(4h_i),\quad h_i+g_i\ge1.
\]

Since `h_B>=1/2`, these inequalities imply

\[
             -31/60<x_B<-27/64.                         \tag{1}
\]

Every original center has norm less than rho. Also every physical unit
square contains the open disk of radius 1/2 about its own center.
Consequently distinct originals with disjoint interiors have center
distance at least one. These are necessary consequences of the
unchanged physical squares, valid for every orientation.

## 3. The complete two-case contradiction

Suppose a putative I has the stated position. Write

\[
 (p,q)=(-x_B,-y_B),\qquad (u,w)=(-x_I,-y_I).
\]

Equation (1) and the hypotheses give

\[
 27/64\le p\le31/60<2/3\le q\le w,
 \quad u\ge0,\quad u^2+w^2\le\rho^2.                  \tag{2}
\]

All strict inequalities have been harmlessly relaxed in (2).
There are two exhaustive cases.

**Case 1: `u<=p`.** Then `0<=p-u<=31/60` and
`0<=w-q<=rho-2/3`. Thus

\[
 |c_I-c_B|^2=(p-u)^2+(w-q)^2
 \le(31/60)^2+(\rho-2/3)^2
 =\frac{1781}{1800}<1.                                \tag{3}
\]

This contradicts the original physical center separation.

**Case 2: `u>=p`.** Put `z=u-p>=0` and `t=w-q>=0`.
Physical center separation gives `z^2+t^2>=1`, hence `z+t>=1`.
Since `q>=p`,

\[
\begin{aligned}
 u^2+w^2
 &=p^2+q^2+z^2+t^2+2pz+2qt\\
 &\ge p^2+q^2+1+2p(z+t)\\
 &\ge(p+1)^2+q^2\\
 &\ge(91/64)^2+(2/3)^2
   =\rho^2+\frac{50963}{307200}>\rho^2.
\end{aligned}                                         \tag{4}
\]

This contradicts the original center-radius bound. Equations (3)--(4)
cover every allowed I, proving the conditional assertion.

## 4. Computer discovery and exact checks

A small numerical maximization over (2) returned the candidate that the
largest squared center separation is `1781/1800`, attained in the
closed relaxation at

\[
 p=31/60,\quad q=2/3,\quad u=0,\quad w=91/60.
\]

The numerical maximum is not used in the proof. The exact two-case
argument above proves the needed strict contradiction directly.
`computer_assisted/weak_outer_hand_deep_B_left_lower.py` reconstructs
the rational coordinate endpoints and the two positive reserves with
`Fraction` arithmetic; it contains no optimizer or floating point.

## 5. Scope in the remaining large-gap argument

The lemma does not claim that B must satisfy `y_B<=-2/3`, or that an
unselected original must lie below B on the left. Those routing
conditions must be proved from the remaining original-nine domain
before invoking it. It neither excludes a whole fixed mask nor
changes the fixed-mask ledger. In particular, it is compatible with
the existing subcritical seven- and eight-original controls.
