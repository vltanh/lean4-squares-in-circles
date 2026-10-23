# Positive T at an arbitrary exact EH0 contact

## 1. The missing signed-E contact theorem

Put
\[
 q_L=19577/5000,\qquad Q_1=1957767069/500000000,\qquad
 h=7/10,\qquad q_L<q_*<Q_1.
\tag{1}
\]
All terminating decimals denote exact rational numbers.
Consider sorted states contained at a common ceiling \(q\le q_*\),
with H,A positive and B,D negative. G,T may have either tangent
sign. Retain actual HG2, GA1 at \(x\ge0\), either AB owner,
DE3 at \(e\ge0\), and EH0 at an arbitrary signed error rho.
E has \(y_E\ge0\) and the exact actual contact
\[
 a_H\cos\rho+b_H\sin\rho+y_E=W(\rho),\qquad
 W(v)=(1+\cos v+|\sin v|)/2.
\tag{2}
\]
Retain either positive-T regime
\[
\begin{array}{c|cc|c}
 &BT&TD&\text{nonnegative primary error}\\ \hline
 \mathrm{TD}&2&2&z=d_{TD}\ge0\\
 \mathrm{BT}&3&0&z=d_{BT}\ge0.
\end{array}
\tag{3}
\]
All other errors, including rho and the surviving secondary
T error, are arbitrary. The seven errors sum to zero and both
variations are at most h. Thus
\[
                         t=x+e+z\le h.
\tag{4}
\]

**Contact theorem.** Every system (1)--(4) has \(x=z=0\).
Outside the critical strip \(.1\le t\le.16\), it is strictly
impossible even at \(q\le Q_1\). All weak ties are included.
No radial-boundary condition is used in this contact stress.

The corresponding aligned-contact theorems are
[the sharp positive-T comparison](HAND_G5_EXCEPTIONAL_E_ALIGNED_POSITIVE_T_CRITICAL_STRIP.md)
and [the outside-strip comparison](HAND_G5_EXCEPTIONAL_E_ALIGNED_POSITIVE_T_OUTSIDE_CRITICAL_STRIP.md).
This note retains the extra EH0 angle in the actual H block.
The critical scalar is unchanged. Outside the strip, only
sixteen additional H scalar inequalities are needed; Section 5
specifies their exact whole-domain construction.

## 2. The actual contact, forces, and fixed-z primary split

Use the exact same positive weights as the appropriate parent
theorem. In particular,
\[
 k=K+.06z,\qquad l=L-.23z,\qquad c=C-.53z,
\]
\[
 f(v)=\cos v+\eta\sin v,\qquad
 n=kf(x),\quad p=f(e),\quad m=cf(z).
\tag{5}
\]
On the critical strip K,L,C,eta are the exact supporting dual;
outside it they are the four full-interval families (5) of the
outside-strip parent. The weights on HG,GA,AB,DE,EH are
\((n,k,l,1,p)\). The T weights are \((m,c)\) in TD and
\((c,m)\) in BT.

The E force remains exactly
\[
                         \sin e(a_E+\eta y_E).
\tag{6}
\]
The EH0 rotation acts on H, not on the signed E tangent.
At fixed t,z, all coefficients in (5) except n,p are fixed.
When splitting \(x+e=t-z\), the varying p multiplies
\[
 p(e)\{W(\rho)-a_H\cos\rho-b_H\sin\rho-y_E\}=0.
\tag{7}
\]
Thus contact (2) provides the exact cancellation used by the
parents even when rho is nonzero.

The G force, T force, sorted H transverse residual greater
than -.065, and bounds \(a_E-.5<.915\) and \(y_E\ge0\)
are identical to the parent hypotheses. Their strict split
second derivatives therefore apply without change. It is
enough to check the two full faces
\[
 \mathrm{GT}:(x,e)=(t-z,0),\qquad
 \mathrm{ET}:(x,e)=(0,t-z),\qquad0\le z\le t.
\tag{8}
\]
This is concavity of a relaxed weighted expression with actual
coordinates fixed; it asserts no physical motion or feasible
packing at a scalar endpoint.

The baseline pairs remain
\[
\begin{array}{c|cccc}
 &H&A&B&D\\ \hline
 \mathrm{TD}&(p,n)&(k,l)&(l,m)&(1,c)\\
 \mathrm{BT}&(p,n)&(k,l)&(l,c)&(1,m).
\end{array}
\tag{9}
\]
If u is the HG error, the actual H force is
\[
 (p\cos\rho+n\sin u,\ p\sin\rho+n\cos u).
\]
Its squared norm is \(p^2+n^2+2pn\sin(u+\rho)\).
H can therefore have both signs of ordinary angle. Its valid
enlarged negative coefficient is
\[
                           \nu_H=\max(p,n).
\tag{10}
\]
All other ordinary blocks and coefficients stay as in the
parent theorems.

## 3. The additional H mixed block

The ordinary positive and negative totals still satisfy
\[
                       N-P=t,\qquad P\le h-t,\quad N\le h.
\tag{11}
\]
Separate concavity gives pure negative charges, same-block
saturations, and separated saturations as in the parents.
There is just one new possible same-block saturation: H.
For its pair \(a\le b\), the positive coefficient can be
lowered to a and the negative coefficient enlarged to b.
The difference from its pure charge at t is at least
\[
 b\{(a/b)(\cos(h-t)+\sin(h-t)-1)+\cos h-\cos t\}.
\tag{12}
\]

In every family and on both faces, the H ratio exceeds 2/3.
On the critical strip, both coefficients are above .925 and
below 1.04, so the ratio exceeds .88. On the low outside
family, \(f(v)\ge1\) for \(0\le v\le t\le.18\);
the coefficients lie between .862 and 1.05, giving ratio
greater than .82. On the middle and high families, the
parent's exact full-square range certificate gives ratio
greater than .71.

For ratio 2/3, the braces in (12) are nonnegative on [0,h].
Their value is zero at h, their derivative there is
\(\sin h-2/3<0\), and their second derivative is
\[
 (\cos h-2/3)\cos(h-t)+(\sin h-2/3)\sin(h-t)>0.
\tag{13}
\]
For example \(\cos h>.7648\), \(.6442<\sin h<.6443\)
make the last expression positive throughout [0,h].
Thus (12) removes the extra H same-block alternative.
No actual EH error has been dropped.

## 4. The sharp strip needs no new scalar certificate

On \(.1\le t\le.16\), the parent bounds give
\[
 .925<k<.995,\qquad1\le f(v)<1.04,\qquad n,p<1.04.
\tag{14}
\]
At each face, one H coefficient is at least one and both
are at least .925. In particular the weaker rectangle
used by the parent, with lower coefficient .8402, still
applies. Its H estimates used only the upper bound 1.04
on the negative coefficient, not equality to n. They give
\[
 V_H(t)>1.184t>V_B(t),\qquad
 V_H(h)>.777>V_B(h).
\tag{15}
\]
Here \(V_B=V_{l,m}^{m}\) is the same canonical B charge.
The positive H cost is still at least
\(-.545(1.04)P\). All A/B/D comparisons, the B chord,
the BT-to-TD comparison, and the GT-to-ET comparison are
unchanged. Section 3 removes the new H mixed alternative.
The full ordinary envelope is therefore still \(V_B(t)\).

The remaining ET/TD scalar is exactly the parent S(t,z).
Its one whole-triangle derivative certificate proves
\[
 \partial_z S>.0018,\qquad
 S(t,0)=N_0(N_0-\sqrt{q_*})/k_2\ge0.
\tag{16}
\]
The exact hard-chain support identity is retained; no
positive numerical reserve is substituted for its zero.
The unchanged strict G/E split and endpoint comparison
then imply \(x=z=0\), as in the aligned parent.

## 5. Outside the strip: the sole new scalar coefficient

Use the four complete intervals
\[
 [0,.1],\quad[.16,.18],\quad[.18,.35],\quad[.35,.7].
\tag{17}
\]
The parent's separated-angle arguments use the same pair
ratios and the bound \(\nu_i\le\max(a_i,b_i)\). They
therefore remain valid with (10). Its same-block B
argument is unchanged, and Section 3 handles H.
Consequently the full envelope is still the minimum of
the four pure charges, now using \(\max(p,n)\) at H.

For scalar index H, let \(F_H^{(n)}\) and \(F_H^{(p)}\)
be the parent's scalar (32) with negative coefficient n
or p, respectively. The other data, baseline and pair
\((p,n)\) are identical. Since \(\cos t-1\le0\),
\[
                 F_H^{(\max(p,n))}
                       =\min(F_H^{(n)},F_H^{(p)}).
\tag{18}
\]
The parent already proves \(F_H^{(n)}>77/10^6\), together
with the corresponding bounds at A,B,D.

Here is an explicit finite certificate for the new option:
in Section 7 of the outside-strip parent, follow (34)--(38)
with exactly the same degree-14 rational enclosure arithmetic,
degree-13/14 trigonometric polynomials, degree-seven global
square-root upper polynomial, product order, and tensor degree
16. Select index H and replace only its scalar coefficient
in (31), and hence the added term in (36), by p:
\[
                 n\{C(t)-1\}\quad\longmapsto\quad
                 p\{C(t)-1\}.
\tag{19}
\]
Denote the resulting enclosure by \([P_H^{(p)},E_H^{(p)}]\).
Thus all constants and operations are specified by the
parent construction plus the single substitution (19).
The four intervals, two faces and two T owners give sixteen
whole-square rational polynomials. Exact coefficient addition
in the parent's tensor formula gives, in every one of them,
\[
 E_H^{(p)}<53/10^6,\qquad
 \beta_{AB}(P_H^{(p)})-E_H^{(p)}>2/1000
                  \quad(0\le A,B\le16).
\tag{20}
\]
The least full-square margin from that exact construction
is greater than .0033611131972; the greatest error is less
than .000003065411719. These decimal displays locate the
reserves; the rational inequalities (20) are the certificate.
The monomial-to-tensor transformation is algebraic, and all
of its coefficient inequalities hold on one complete square
per interval. There is no angle subdivision or sampled premise.

The same global square-root upper bound and enclosure rule
as in the parent give
\[
                       F_H^{(p)}>2/1000.
\tag{21}
\]
Together with (18), all four pure scalars are still greater
than \(77/10^6\). Their strict contradiction proves the
outside-strip part of the contact theorem.

## 6. Original E normalization and the positive-T sign interface

Assume now the same-radius boundary-neighbor domain with
outer E at q, sole DE3 with \(e\ge0\), arbitrary EH0 error,
and one of (3). If the original E has \(y_E\le0\), the
[sole-E positive-T theorem](HAND_G5_POSITIVE_GA1_SOLE_E_PRIMARY_POSITIVE_T_EXCLUSION.md)
is already strict at Q1.

If \(y_E>0\), apply the fixed-frame outer-circle normalization
in Section 2 of
[the sign-free BT2/TD0 entry theorem](HAND_G5_COUPLED_OUTER_E_SIGN_FREE_BT2_TD0_ENTRY.md).
That construction uses only D,E,H and the two actual E
witnesses, so the present T owners do not affect it. E's
tangent decreases to
\[
 \max\{0,W(\rho)-a_H\cos\rho-b_H\sin\rho\}
\tag{22}
\]
on its original q-circle. DE3 improves, EH0 stays feasible,
the two quarter gaps stay positive, their sum is unchanged,
and every frame and both variations are identical.
All other six states and all their witnesses remain fixed.

At a zero endpoint the sole-E theorem applies. At a positive
endpoint (2) is exact, so Sections 1--5 force \(x=z=0\).
In particular a positive GA error \(x>0\) is impossible.
For two positive E primaries, the same-radius E-only pair
reduction first gives a sole EH or sole DE endpoint. The
former permits either E sign in the sole-E theorem; the
latter has just been treated. No assumed sign invariance
of that paired transport is needed.

These conclusions are strict exclusions or actual necessary
descendants at the original q. At a zero GA error the
original GA0 tie is selected before any E motion. No
equality conclusion is drawn from a transported E.
