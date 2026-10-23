# Every original quarter witness selects an outer endpoint

## 1. The global radial statement

On the actual G0--G2 boundary seven-cycle at
\(Q=9789/2500\), every original quarter witness satisfies
\[
\begin{array}{c|c}
\text{original owner}&\text{forced outer endpoint}\\ \hline
0\text{ or }1&\text{the quarter target}\\
2\text{ or }3&\text{the quarter source}.
\end{array}                                                       \tag{1}
\]
This conclusion has no additional sign, owner, frame-order,
mismatch, or E-normalization assumption. It concerns the actual
boundary representatives supplied by G0, not the original centers
before that radial reduction.

The proof combines the already established
[outer-anchor theorem beside a zero edge](HAND_G3_GLOBAL_LOW_GA_TARGET_IS_OUTER.md)
with the complementary local theorem proved here:

> A zero edge followed by a high-index quarter edge has an outer
> common vertex.

The old theorem treats a low-index quarter following a zero, and
its reflected form treats a high-index quarter preceding a zero.
The reflected form of the new theorem treats a low-index quarter
preceding a zero. Every quarter in the surviving word
\((0,1,0,1,0,1,1)\) has a zero on at least one side, so these
four local statements prove (1).

## 2. The new zero--high-quarter theorem and its known half

Name the local path T--D--E solely for this proof. Its first edge
is zero and its second is quarter. A high DE witness forces
\(y_D=-b_D<0\) by the generic quarter-sign theorem. The T and E
signs remain arbitrary. Write
\[
 v=d_{TD},\qquad d=d_{DE},\qquad
 C=\frac\pi2+v+d+\ell_T-\ell_E.                                  \tag{2}
\]
The five complementary original G1 edges again imply
\(C<2\pi-5(8833/10000)<2\).

Suppose D is core. If \(y_E\le0\), Sections 2--5 of
[the global D-outer proof](HAND_G3_GLOBAL_D_IS_OUTER.md) apply
without change and prove \(C>2\). That proof used the role names
only to specify this zero--quarter path and its five complementary
edges. It covered both T signs, both original zero witnesses,
and both high quarter witnesses.

It remains to treat \(y_E=b_E>0\). Retain the constants
\[
 k=\frac{43}{50},\quad m=\frac{111}{100},\quad
 L=\frac{447}{800},\quad a_0=\sqrt{Q-1/4}-\frac12
\]
and all whole-interval estimates proved in Sections 2--3 of the
D-outer note. In particular, for positive U,V, its actual-core
support is
\[
 Ua_D+Vb_D\le\frac{U+V}{2}+\frac1{12}\sqrt{U^2+V^2},              \tag{3}
\]
and its angle-cost bounds are
\[
\begin{aligned}
 t-k(a_0-\tfrac12)\tan t&\ge0,\\
 t-m(a_0-\tfrac12)\tan t&>-17/100,\\
 \sum_j(-z_j+k\sin z_j)&>-3/20
       \quad\text{if }\sum_jz_j\le7/10,\\
 -z+k(L+\tfrac12)\tan z&\ge-z+k\sin z.
\end{aligned}                                                    \tag{4}
\]
All variables in (4) lie in \([0,7/10]\).

## 3. Positive E forces a single original quarter branch

The original DE projections now are
\[
 P_2=a_D\cos d+b_D\sin d-b_E,\qquad
 P_3=a_D+a_E\sin d-b_E\cos d.                                   \tag{5}
\]
Because D is core,
\(a_D^2+b_D^2\le49/72<1\). Thus \(P_2<1\), excluding
DE2. If \(d\le0\), then \(P_3\le a_D<1\), so the retained
branch is DE3 with \(d>0\).

E must be outer. Otherwise, using \(\sin d<13/20\),
\[
             P_3\le\frac7{12}(1+\tfrac{13}{20})
                          =\frac{77}{80}<1.                    \tag{6}
\]
At this actual outer E the original marker plane gives
\[
       -\ell_E=-F_E\ge-\frac25(a_E-a_0)-mb_E.                   \tag{7}
\]
Give DE3 the multiplier \(m\sec d\). After subtracting its
weighted projection, the b_E coefficient cancels in (7), and
the E-primary contribution is
\[
 -\{\tfrac25+m\tan d\}a_E+\tfrac25a_0
                                      \ge-ma_0\tan d,           \tag{8}
\]
since \(d>0\). This is the same exact cancellation as at the
negative T endpoint in the D-outer proof.

## 4. Both T signs and the cyclic contradiction

If \(y_T=b_T\ge0\), use \(\ell_T\ge kb_T\). Give TD0
multiplier k, or TD2 multiplier \(k\sec v\), exactly as in
the D-outer proof. The D force is
\[
 (U,V)=
 \begin{cases}
 k(\sin v,\cos v)+m\sec d(1,0),&TD0,\\
 k\sec v(0,1)+m\sec d(1,0),&TD2.
 \end{cases}                                                     \tag{9}
\]
Both coefficients are positive; for TD0 the only possibly
negative term is \(k\sin v\), and
\(m-k(13/20)=551/1000>0\). Its norm obeys
\[
 N<\frac{25}{19}(k+m)=\frac{197}{76}<\frac{13}{5}.                \tag{10}
\]
Subtracting the half-force in (3) leaves constant \((k+m)/2\).
The DE cost is the second expression in (4), exceeding
\(-17/100\). The TD cost is nonnegative at positive v and
exceeds \(-3/20\) at negative v. Hence
\[
 C>\frac{157}{100}+\frac{k+m}{2}
              -\frac{17}{100}-\frac3{20}-\frac{13}{60}
                         =\frac{1211}{600}>2.                   \tag{11}
\]

If \(y_T=-b_T<0\), the zero-sign theorem forces TD2, and the
core-D projection argument in Section 5 of the D-outer proof
gives \(v>0\) and T outer. Its upper marker plane, with
multiplier \(m\sec v\), cancels b_T and leaves
\(-ma_0\tan v\), just as (8) does at E.

Now \((U,V)=(m\sec d,m\sec v)\) is positive and
\[
 N<2m\frac{25}{19}=\frac{111}{38}<3,
 \qquad 3-\frac{111}{38}=\frac3{38}>0.                          \tag{12}
\]
The constant is m, and each of the two positive-angle costs
exceeds \(-17/100\). Thus
\[
 C>\frac{157}{100}+m-\frac{34}{100}-\frac14
                              =\frac{209}{100}>2.                \tag{13}
\]
This proves the new local theorem in both E signs and every T
sign. As in the D-outer note, \(C>2\) contradicts the five
unchanged complementary G1 inequalities with exact reserve
\(30129/226000\) against \(2\pi<710/113\).

Under reflected reversal, owner numbers exchange
\(0\leftrightarrow2\), \(1\leftrightarrow3\); the middle
vertex and its radial kind are preserved. The signed markers
and the path direction both reverse, so the local charge (2)
and its cyclic contradiction are unchanged. This gives the
new low-quarter--zero statement and completes (1).

Every step uses original witnesses, actual circle or core
geometry, and the common G1 marker. No frame deformation or
numerical acceptance premise is used.
