# The aligned four-square path forces both endpoint signs at S <= 13/50

## 1. The theorem and its global use

Assume the G0--G2 candidate geometry, with signed own-frame centers
\((a_i,-y_i)\), \(a_i\ge |y_i|\), at squared radius
\(q\le Q=9789/2500\). Consider the actual path
\[
                         A\longrightarrow B\longrightarrow T
                           \longrightarrow D
\]
whose quarter increments are \((0,1,0)\). If
\[
                 s_0:=|d_A|+|d_B|+|d_T|\le13/50,
\tag{1}
\]
then
\[
                         \boxed{y_A>0,\qquad y_D<0.}
\tag{2}
\]

In particular, the global mismatch hypothesis \(S\le13/50\) implies
(1). This theorem assumes **no candidate tangent cuts at all**. It also
assumes no quarter or mixed owner, no tilt window, no radial kind, no
sign of B or T, and no contraction to \(S\le1/10\).

The previously established global zero-primary theorem supplies just
one owner fact: every feasible original witness on AB and TD is axis
0 or 2. This fact is available from G0--G2, before all candidate cuts
and mismatch contractions; see `HAND_ZERO_PRIMARY_CYCLIC_EXCLUSION.md`.
All four original BT axes remain available at the start of this proof.
The two zero-edge physical gaps exceed \(19/25\).

The conclusion is an earlier endpoint-sign subgate, not a proof of the
global bound (1), a magnitude cut, or a complete G3--G5 contraction.
It strengthens `HAND_COARSE_TD_SIGN_EXCLUSION.md` by removing its T-cone
hypothesis and proving both endpoint signs with one polynomial identity.

## 2. Uniform bounds and an owner-independent nominal estimate

Containment of the farthest corner gives
\[
           (a_i+1/2)^2+(|y_i|+1/2)^2\le Q.
\tag{3}
\]
Consequently
\[
 a_i<U:=283/200,\quad |y_i|<9/10,\quad
 a_i+|y_i|<9/5,\quad |p_i|<3/2.                     \tag{4}
\]
The first comparison follows by substituting U in
\((a+1/2)^2+1/4\). The second follows from \(a_i\ge|y_i|\) and
\(2(7/5)^2>Q\); the third follows from Cauchy and
\(2Q<(14/5)^2\). The center-norm bound follows because the square's
radius-1/2 inscribed disk lies in a containing disk of radius less than 2.

Let
\[
                   K=15/14,\qquad \rho=13/50.
\]
For any original axis on an aligned edge with absolute frame error
\(e\le\rho\), its projection differs from its nominal quarter-angle
projection by at most \(3e/2\), using (4). Its actual support width is
at least \(1+e/2-e^2/4-e^3/12\). Thus every feasible original witness
satisfies
\[
                P^{\rm nominal}\ge1-Ke.             \tag{5}
\]
The coefficient comparison holds on the whole interval because
\[
 K-1-e/4-e^2/12\ge K-1-\rho/4-\rho^2/12
                         =167/210000>0.
\]

In signed coordinates, the two zero-owner nominal projections both
are \(y_i-y_{i+1}\). On a quarter edge, axes 0 and 1 have nominal
projection \(a_{i+1}+y_i\), and axes 2 and 3 have nominal projection
\(a_i-y_{i+1}\). These identities hold before any sign assumption.

## 3. A same-side zero edge has only its far-end transverse owner

For \(0\le\delta\le\rho\), write
\[
 c=\cos\delta,\quad s=\sin\delta,\quad W=(1+c+s)/2.
\]
If \(a\ge b\ge0\), \(a+b<9/5\), then c>=s gives
\[
 as+bc\le\frac{a+b}{2}(s+c)<\frac9{10}(s+c).
\]
Therefore
\[
 as+bc-W<\frac25(s+c)-\frac12
          \le\frac25(1+\rho-\rho^2/3)-\frac12
          =-47/9375<0.                              \tag{6}
\]
Here \(\sin\delta\le\delta\) and
\(\cos\delta\le1-\delta^2/3\) on this interval. The latter follows,
for example, from \(\cos x\le1-x^2/2+x^4/24\) for \(0\le x\le1\).
The polynomial \(1+x-x^2/3\) increases on \([0,\rho]\).

Also, any inequality of the form
\[
                   B+a s-b c\ge W,
 \qquad a<U,\quad b\ge0,
\]
forces
\[
 \begin{split}
 B&>W-U s\\
  &\ge m(\delta):=1-\frac{183}{200}\delta-\frac14\delta^2
   \ge m(\rho)=\frac{1863}{2500}.
 \end{split}                                        \tag{7}
\]
This uses only \(s\le\delta\), \(c\ge1-\delta^2/2\), and
monotonicity of m. The application has \(\delta>0\), so the first
inequality is strict.

## 4. Exclude a nonpositive A

Suppose \(y_A\le0\). The AB physical gap is
\[
 d_A+\arctan(y_A/a_A)-\arctan(y_B/a_B)>19/25.
\]
If \(y_B\ge0\), its left side is at most \(d_A\le\rho<19/25\).
Hence \(y_B<0\). Write
\[
 b=-y_A\ge0,\quad B=-y_B>0,\quad a=a_A,\quad A=a_B,
 \quad\delta=d_A.
\]
The two possible original AB projections are
\[
                  P_0=-b+A\sin\delta+B\cos\delta,
 \qquad P_2=a\sin\delta-b\cos\delta+B.               \tag{8}
\]
If \(\delta\le0\), both are at most B<9/10, whereas the support width
is at least one. Thus \(0<\delta\le\rho\). Equation (6), applied to
\((A,B)\), excludes P0 throughout this interval. Therefore P2 is an
actually feasible witness, and (7) gives \(B>m(\delta)\).

Put \(e_B=|d_B|\) and \(e_T=|d_T|\). Their **shared** total satisfies
\[
                        e_B+e_T\le\rho-\delta.       \tag{9}
\]
BT axes 0 and 1 would have nominal projection \(a_T-B\). They are
impossible by (4), (5), (7), because
\[
 1-K\rho-(U-m(\rho))=1807/35000>0.
\tag{10}
\]
Thus any actual BT witness belongs to axes 2 or 3 and obeys
\(a_B-y_T\ge1-Ke_B\). The actual TD zero witness obeys
\(y_T-y_D\ge1-Ke_T\), with **no sign assumption** on T or D.
Adding these two inequalities, and using (9), gives
\[
 a_B-y_D\ge2-K(\rho-\delta).
\]
Since \(-y_D\le|y_D|<9/10\),
\[
                       a_B+1/2>37/28+(15/14)\delta.
\tag{11}
\]
The same B center has, from (7),
\[
                  B+1/2>3/2-(183/200)\delta-\delta^2/4.
\tag{12}
\]
Both right sides are positive. Equations (11)--(12) contradict its
corner containment (3), by the following exact identity:
\[
\begin{split}
&\left(\frac{37}{28}+\frac{15}{14}\delta\right)^2
 +\left(\frac32-\frac{183}{200}\delta-\frac14\delta^2\right)^2-Q\\
&\quad=\frac{39481}{490000}+\frac{849}{9800}\delta
       +\frac{2420961}{1960000}\delta^2
       +\frac{183}{400}\delta^3+\frac1{16}\delta^4>0.
\end{split}                                         \tag{13}
\]
Every coefficient is positive, and \(\delta\ge0\). This proves
\(y_A>0\) on the complete domain (1).

## 5. Exclude a nonnegative D with the same polynomial

For completeness, the reverse endpoint argument is given directly;
it requires no reflection of the entire seven-cycle or its mismatch
index set. Suppose \(y_D\ge0\). The TD physical gap forces
\(y_T>0\), since otherwise that gap is at most \(d_T\le\rho\).
Write \(b=y_T>0\), \(B=y_D\ge0\), \(a=a_T\), \(A=a_D\),
and \(\delta=d_T\). The two possible TD projections are
\[
                 P_0=b+A\sin\delta-B\cos\delta,
 \qquad P_2=a\sin\delta+b\cos\delta-B.               \tag{14}
\]
For \(\delta\le0\), both are at most b<9/10, so \(\delta>0\).
Equation (6) excludes P2. Feasible P0 and the derivation of (7) imply
\(b>m(\delta)\).

Now set \(e_A=|d_A|\), \(e_B=|d_B|\). Their shared sum is at most
\(\rho-\delta\). BT axes 2 and 3, with nominal projection \(a_B-b\),
are impossible by exactly (10). Thus a feasible BT witness has nominal
projection \(a_T+y_B\), and the AB zero projection is \(y_A-y_B\).
Adding (5) on these two actual edges yields
\[
 a_T+y_A\ge2-K(e_A+e_B)\ge2-K(\rho-\delta).
\]
Using \(y_A\le|y_A|<9/10\), we get
\[
 a_T+1/2>37/28+(15/14)\delta,
 \qquad b+1/2>3/2-(183/200)\delta-\delta^2/4.
\]
Identity (13) now contradicts the T corner disk. Hence \(y_D<0\).

## 6. Coverage and the unresolved global implications

The proof includes both original zero axes and all four original BT
axes. An axis feasible at a tie is subject to the same strict exclusions.
It uses original centers, not independent pair representatives, and
spends the same total \(\rho-\delta\) on the two remaining path edges.
Both sign-zero boundaries are explicitly excluded. No radial chart,
chart label, mixed witness or sign outside the path was altered.

The mathematical content is one three-edge cancellation and the
positive-coefficient identity (13). Rational calculations checked the
printed coefficients and reserves; no numerical state/angle cover or
external success assertion is a proof premise. No Lean source or
historical table was changed, and no compilation or CI was run.

This allows G3--G5 work to use A positive and D negative as soon as
S<=13/50 is established, even before any candidate tangent cut. It does
not establish that coarse mismatch bound, the G/T cuts, H positive,
B negative, T positive, the magnitude cuts on H/D, or either remaining
mismatch contraction. Those universal obligations remain open.
