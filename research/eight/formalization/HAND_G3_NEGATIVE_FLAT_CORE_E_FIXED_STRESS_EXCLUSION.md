# Negative flat-core E errors paid by a lower charged four-circle stress

## 1. Scope and statement

Put
\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad h=\frac7{10},
 \quad a_0=\sqrt{Q-\frac14}-\frac12,\quad
 c_0=\sqrt{Q/2}-\frac12.
\tag{1}
\]
Retain a necessary G0--G2 boundary system whose sorted outer
states H, G, B and D have tangent signs respectively positive,
negative, negative and negative. The E tangent is nonpositive,
and E is on the flat true core:
\[
                        a_E=\frac7{12},\qquad 0\le b_E\le\frac12.
\tag{2}
\]
A and T may have either sign and either radial kind. Keep BT2
and either HG0 or HG2. Allow simultaneously

* GA2 at any error, or GA3 at a nonpositive error;
* AB0 at any error, or AB2 at a nonpositive error;
* TD0 at any error, or TD2 at a nonpositive error;
* DE2 at any error, or DE3 at a nonpositive error;
* EH0 at any error, or EH1 at a nonpositive error.

Assume the actual errors satisfy
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+\le h.
\tag{3}
\]
**There is no such necessary system.** No frame order is assumed.
In particular, both E primary alternatives may occur at once.
The argument only uses the stated inequalities, sorted circles,
true-core primary bound, and variation domain. It does not require
that a later necessary system be an original packed cycle.

All decimals in this note denote exact rationals. Write
\[
 W(t)=\frac{1+\cos t+|\sin t|}{2},\qquad
 S(f,g)=\max_{0\le b\le c_0}
 \left[f\left(\sqrt{Q-(b+\tfrac12)^2}-\tfrac12\right)+gb\right].
\tag{4}
\]

## 2. The secondary-owner stress with angular charge .946

Use the fixed weights
\[
 k=\frac{39}{50},\qquad l=\frac{63}{50},\qquad c=\frac95,
 \qquad \lambda=\frac{473}{500}=.946.
\tag{5}
\]
Let \(\mathcal C(\mathbf d)\) be the secondary-owner four-circle
demand minus support expression with weights
\((k,l,l,c,c,1,1)\), for either HG owner. Then
\[
             \mathcal C(\mathbf d)+\lambda\sum_i d_i
                         >B:=\frac{13}{400}
\tag{6}
\]
whenever positive and negative variation are each at most h.
The signed sum need not be zero.

Here is a direct verification from Section 3 of
[the low-angle TD0 stress](HAND_G3_POSITIVE_INTERMEDIATE_TD0_FOUR_CIRCLE_EXCLUSION.md).
That proof uses the same weights and a charge \(\lambda_0=1.03\).
Its zero-angle baseline exceeds B, independently of the charge.
The three full-circle pairs are \((k,l),(k,1),(l,c)\). Their
charged two-variable functions are separately concave on
\([0,h]^2\), and this concavity is unaffected by changing a
linear charge. At the four intrinsic rectangle corners, the
zero value stays zero, the opposite-sign corner is unchanged,
and the negative corner improves. The positive corner remains
strictly positive because the cited exact lower bound gives
\[
 .075533-(1.03-.946)h=\frac{16733}{10^6}>0.
\tag{7}
\]
Thus all three full-circle charged blocks stay nonnegative.

For completeness, the only D-block estimate that needs a new
numerical bound is its last positive-angle interior derivative.
The block is
\[
 T(z,d)=cW(z)+W(d)
       -S(\cos d+c\sin z,c\cos z+\sin d)+\lambda(z+d).
\tag{8}
\]
The cited proof rules out an axis maximizer. Its negative-d and
negative-z derivatives remain negative when the charge decreases.
The positive-d derivative is greater than \(\lambda-.4>0\),
and the positive-z diagonal derivative is greater than
\(\lambda-.4c>0\). Thus the same first reduction sends d to zero.

At an interior maximizer for \(T(z,0)\), \(z\ge0\), the exact
condition \(1+c\sin z>c\cos z\) forces \(\sin z>.35\), as in
the cited proof. Set \(A=1+c^2=106/25\). Then
\[
 A+2c\sin z>\frac{11}{2},\qquad
 \frac{R}{\sqrt{A+2c\sin z}}<\frac{211}{250}=.844,
\tag{9}
\]
because
\[
 \left(\frac{211}{250}\right)^2\frac{11}{2}-Q
                         =\frac{281}{125000}>0.
\]
The whole-interval Taylor estimates \(\cos z>.7648\) and
\(\sin z<.6443\) now give
\[
\begin{split}
 \partial_zT
 &=\lambda+c(\cos z-\sin z)
       -\frac{cR\cos z}{\sqrt{A+2c\sin z}}\\
 &>\lambda+c\{.156(.7648)-.6443\}
                         =\frac{6349}{6250000}>0.
\end{split}
\tag{10}
\]
The Taylor reserves at h are, explicitly,
\[
 C_6(h)-.7648=\frac{29351}{720000000}>0,\qquad
 .6443-S_9(h)=\frac{4267067999}{51840000000000}>0.
\tag{11}
\]
All support transitions have matching first derivatives.
Consequently \(T(z,d)\ge T(0,0)\) on its full two-error
hexagon. Combining its minimum with the three nonnegative
full-circle blocks and the unchanged baseline proves (6).

## 3. A uniform secant gain for the negative A and T alternatives

Let
\[
 J(s)=\frac{847}{800}\tan s-\frac{183}{200}(\sec s-1).
\tag{12}
\]
The exact separate secant comparisons in Sections 3--4 of
[the negative-intermediate fixed-stress proof](HAND_G3_NEGATIVE_INTERMEDIATE_ERRORS_FIXED_STRESS_EXCLUSION.md)
apply with the present value of l: a GA3 or AB2 error \(-s\)
receives multiplier \(l\sec s\), and deleting just that argument
from the secondary expression gives gain at least \(lJ(s)\).
The actual signed A tangent cancels. Multiple such gains add.
This uses only \(a_A>447/800\), \(a_G<1.415\), and \(b_B<.9\).

A sharper elementary derivative bound is useful here:
\[
                            J'(s)>\frac{79}{100}.
\tag{13}
\]
Indeed, writing \(x=\sin s\), its numerator after multiplication
by \(\cos^2s\) is
\[
\begin{split}
 \cos^2s\left(J'(s)-\frac{79}{100}\right)
 &=\frac{79}{100}x^2-\frac{183}{200}x
                       +\frac{847}{800}-\frac{79}{100}\\
 &=\frac{79}{100}\left(x-\frac{183}{316}\right)^2
                              +\frac{481}{126400}>0.
\end{split}
\tag{14}
\]
Therefore each such gain pays its whole angular charge with
\[
                       lJ(s)\ge\left(\lambda+\frac{247}{5000}\right)s.
\tag{15}
\]
At zero both sides vanish; the derivative bound is strict.

For TD2 at error \(-w\le0\), retain multiplier c and delete
its argument from the virtual TD0 expression. The signed
comparison in Section 6 of the same proof gives gain at least
\(c(\sin w+\cos w-1)\). Concavity and its exact endpoint
bound \(\sin h+\cos h-1>.409\) show
\[
 c(\sin w+\cos w-1)
       \ge\left(\lambda+\frac{37}{350}\right)w.
\tag{16}
\]
This does not require a sign or radial-kind assumption on T.

## 4. One or two negative flat-core E gains

For DE3 at error \(-s\), use multiplier \(\sec s\). Its
weighted projection and the virtual zero-error DE2 projection
differ by
\[
 \sec s\{a_D-a_E\sin s+b_E\cos s\}-(a_D+b_E)
                    =a_D(\sec s-1)-a_E\tan s.
\tag{17}
\]
For EH1 at error \(-s\), the analogous difference from virtual
zero-error EH0 is
\[
 \sec s\{a_H-a_E\sin s-b_E\cos s\}-(a_H-b_E)
                    =a_H(\sec s-1)-a_E\tan s.
\tag{18}
\]
Since \(a_D,a_H\le a_0<1.415\), the demand minus projection
gain in either case is at least
\[
 g(s):=K\tan s-a(\sec s-1),\qquad
                K=\frac{13}{12},\quad a=\frac{183}{200}.
\tag{19}
\]
Here (2) supplies K exactly. If both alternatives occur,
use their two separate secant multipliers. Equations (17)--(18)
show that their gains add and that the E tangent still cancels.

We need two properties of g on the whole interval \([0,h]\):
\[
 \sum_j g(s_j)\ge g\left(\sum_js_j\right)
       \quad\left(s_j\ge0,\ \sum_js_j\le h\right),
 \qquad
                         B+g(s)-\lambda s>0.
\tag{20}
\]
Both follow from one-dimensional derivatives and intrinsic
endpoint comparisons, as follows.

### 4.1 The ratio g(s)/s decreases

The exact second derivative is
\[
 g''(s)=\frac{2K\sin s-a(1+\sin^2s)}{\cos^3s}.
\tag{21}
\]
Its numerator, as a polynomial in \(x=\sin s\), is strictly
increasing on \([0,h]\), since its derivative is
\(2K-2ax\ge2(K-a)>0\). At zero the numerator is negative.
Thus \(g''\) changes sign at most once, from negative to positive.
The function \(U(s)=sg'(s)-g(s)\) satisfies \(U(0)=0\) and
\(U'(s)=sg''(s)\): it first decreases, and may then increase.
Its final value is still negative. An explicit upper bound is
\[
\begin{split}
 \cos^2h\,U(h)
 &=Kh-ah\sin h-K\sin h\cos h+a\cos h-a\cos^2h\\
 &\le Kh-ahS_7(h)-KS_7(h)C_6(h)+aC_8(h)-aC_6(h)^2\\
 &=-\frac{3654654647214851707}{155520000000000000000}<0.
\end{split}
\tag{22}
\]
Consequently \(U(s)<0\) for \(0<s\le h\), so \(g(s)/s\)
decreases. Multiplying this ratio comparison by each \(s_j\)
proves the first assertion of (20), with zero terms handled
by continuity.

### 4.2 The baseline pays the total E angle

Multiply the second assertion of (20) by the positive cosine,
and write
\[
 F(s)=\cos s\{B+g(s)-\lambda s\}
          =(B+a-\lambda s)\cos s+K\sin s-a.
\tag{23}
\]
The third derivative is
\[
 F'''(s)=(3\lambda-K)\cos s+(B+a-\lambda s)\sin s>0,
\tag{24}
\]
because \(3\lambda-K=658/375>0\) and
\(B+a-\lambda h=2853/10000>0\). Thus \(F'\) is convex.
It starts positive, \(F'(0)=K-\lambda>0\), and ends negative:
\[
\begin{split}
 F'(h)
 &=(K-\lambda)\cos h+(\lambda h-B-a)\sin h\\
 &\le(K-\lambda)C_8(h)+(\lambda h-B-a)S_7(h)\\
 &=-\frac{34023000872689}{432000000000000}<0.
\end{split}
\tag{25}
\]
Convexity makes the set where \(F'\le0\) an interval containing
h. Thus F first increases and then decreases; its minimum is
at an endpoint. Those two values satisfy
\[
\begin{split}
 F(0)&=B>0,\\
 F(h)&\ge(B+a-\lambda h)C_6(h)+KS_7(h)-a\\
     &=\frac{24007209959}{21600000000000}>\frac1{1000}.
\end{split}
\tag{26}
\]
This proves the second assertion of (20), with a uniform
strict reserve. No angular mesh or external numerical premise
is involved.

## 5. The simultaneous-owner contradiction

Let A_- be the sum of the magnitudes of the selected negative
GA3/AB2 arguments. Let w be the magnitude of the selected
negative TD2 argument, or zero for TD0. Let e be the sum of
the magnitudes of the selected negative DE3/EH1 arguments.
Delete just these arguments in the algebraic secondary expression.
Its signed sum becomes \(A_-+w+e\); its positive and negative
variations remain at most h. Thus (6) bounds that reference
expression below by
\[
                         B-\lambda(A_-+w+e).
\tag{27}
\]
Use the positive secant multipliers specified above on all
selected A and E alternatives, and the unchanged multiplier c
for a selected TD2. Pointwise comparison with the reference
expression gives a demand minus projection strictly greater than
\[
 \begin{split}
 &B-\lambda(A_-+w+e)
       +\left(\lambda+\frac{247}{5000}\right)A_-
       +\left(\lambda+\frac{37}{350}\right)w+g(e)\\
 &\hspace{10mm}=B+g(e)-\lambda e
             +\frac{247}{5000}A_-+\frac{37}{350}w>0.
 \end{split}
\tag{28}
\]
The first assertion of (20) combines the one or two E gains,
and the second supplies the final strict inequality. Every
multiplier is positive, whereas feasible separating inequalities
require their total demand minus projection to be nonpositive.
This contradiction proves Section 1.

The result keeps BT2 and the nonpositive A/T-primary regime
explicit. It does not assert an exclusion with positive TD2,
positive A-primary total, or curved-core E at a negative primary
edge without a further reduction.
