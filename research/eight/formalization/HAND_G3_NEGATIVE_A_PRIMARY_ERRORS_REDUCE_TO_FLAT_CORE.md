# Negative primary errors adjacent to A reduce to the flat core

## 1. Original scope

Work on the original G0--G2 boundary cycle at

\[
                  Q=\frac{9789}{2500},\qquad h=\frac7{10}.
\tag{1}
\]

Assume GA has a high original owner and EH has a low
original owner. The global sign and radial theorems then
give sorted outer G and B with strictly negative tangents.
Write their coordinates as
\((a_G,-b_G)\) and \((a_B,-b_B)\). The original A state
may initially have either sign and either radial kind.

[The high-GA target cut](HAND_G3_HIGH_GA_TARGET_HAS_SMALL_TANGENT.md)
gives \(y_A<1/2\). The constants

\[
 a_0=\sqrt{Q-\tfrac14}-\tfrac12<1.415,\qquad
 c_0=\sqrt{Q/2}-\tfrac12<.9
\tag{2}
\]

bound every sorted primary and absolute tangent coordinate.
The global variation theorem gives \(|d_i|<h\).

For an original negative primary error adjacent to A,
one of the following holds:

* GA3 with error \(-s<0\) has the actual GA2 projection
  feasible at the same states and frames; or A is positive
  flat core and
  \[
       a_A=\frac7{12},\qquad 0<y_A<\frac{39}{250},
                         \qquad 0<s<\frac14.
  \tag{3}
  \]
* AB2 with error \(-s<0\) has the actual AB0 projection
  feasible at the same states and frames; or A is positive
  flat core and
  \[
       a_A=\frac7{12},\qquad 0<y_A<\frac12,
                         \qquad 0<s<\frac{19}{50}.
  \tag{4}
  \]

The same-state owner replacements do not change any angle,
radial kind, sign, or neighboring inequality. No frame order
is assumed. The alternatives concern the actual original
projections; no moving-circle or marker substitution is used.

## 2. The negative AB2 alternative

The original AB2 projection is

\[
       P_2=-a_A\sin s+y_A\cos s+b_B\ge W(s),\qquad
       W(s)=\frac{1+\cos s+\sin s}{2}\ge1.
\tag{5}
\]

If \(y_A\le0\), the left side is less than \(b_B<.9\),
which is impossible. Hence

\[
                              0<y_A<\frac12.
\tag{6}
\]

Put \(b_A=y_A\). Suppose first that A is outer. Equation
(5) implies \(b_A+b_B>1\). Consequently \(b_B>b_A\).
Both states are on their original outer Q-circle, so

\[
 \frac{a_A-a_B}{b_B-b_A}
             =\frac{b_A+b_B+1}{a_A+a_B+1}
             >\frac2{2a_0+1}>\frac2{3.83}.
\tag{7}
\]

The actual AB0 projection is

\[
                         P_0=b_A-a_B\sin s+b_B\cos s.
\]

Their difference is therefore

\[
\begin{split}
 P_2-P_0
  &=(a_B-a_A)\sin s+(b_B-b_A)(1-\cos s)\\
  &=(b_B-b_A)\sin s
       \left\{\tan(s/2)-\frac{a_A-a_B}{b_B-b_A}\right\}<0.
\end{split}
\tag{8}
\]

Here the established whole-interval estimate
\(\tan(s/2)<183/500\), together with (7), gives the exact
positive comparison reserve

\[
                       \frac2{3.83}-\frac{183}{500}
                               =\frac{29911}{191500}>0.
\tag{9}
\]

Thus AB0 is feasible whenever A is outer.

Otherwise A is core, and (6) puts it on its actual flat
side: \(a_A=7/12\). Rearranging (5) gives

\[
 b_B-\frac12\ge
       \left(\frac12-b_A\right)\cos s+\frac{13}{12}\sin s.
\tag{10}
\]

Since \(b_B<.9\), this implies \(\sin s<24/65\).
Sine is increasing on \([0,h]\), and its lower Taylor
bound at \(19/50\) has exact reserve

\[
 \frac{19}{50}-\frac16\left(\frac{19}{50}\right)^3
                       -\frac{24}{65}
                           =\frac{15833}{9750000}>0.
\tag{11}
\]

This proves (4).

## 3. The negative GA3 alternative

Write \(a=a_G,\ b=b_G,\ A=a_A,\ Y=y_A\). The original
two high-quarter projections at error \(-s\) are

\[
                 P_3=a-A\sin s-Y\cos s,\qquad
                 P_2=a\cos s-b\sin s-Y.
\tag{12}
\]

If \(Y\le0\), A is outer by
[the nonpositive-zero-source theorem](HAND_G3_NONPOSITIVE_ZERO_SOURCE_IS_OUTER.md).
Write \(Y=-B\) and \(q=\tan(s/2)\). The exact difference is

\[
                     P_3-P_2=\sin s\{qa+b-A-qB\}.
\tag{13}
\]

Sorted containment gives \(qa+b\le c_0(1+q)\).
On the target outer arc, concavity in B gives
\(A+qB\ge c_0(1+q)\): its two endpoint values are
\(a_0\) and \(c_0(1+q)\), and

\[
                    a_0>1.414>.9(1+.366)>c_0(1+q).
\]

Thus \(P_3\le P_2\). This is also the direct original-owner
comparison in Section 5 of
[the high-quarter augmented-charge theorem](HAND_G3_HIGH_QUARTER_AUGMENTED_PRIMARY_CHARGE.md).

It remains to consider \(Y>0\). Suppose the original GA2
projection is not feasible. Since GA3 is feasible, \(P_3>P_2\).
Use the shifted coordinates

\[
 K=A+\frac12,\quad D=Y+\frac12,\quad
 X=a+\frac12,\quad Z=b+\frac12,\quad q=\tan(s/2).
\tag{14}
\]

The original GA3 inequality and the strict projection
difference imply

\[
 X\ge X_*:=1+D\cos s+K\sin s,\qquad
 Z>Z_*-q(X-X_*),\qquad Z_*:=K\cos s-D\sin s>0.
\tag{15}
\]

The last sign follows from sorting \(K\ge D\) and \(s<h<\pi/4\).
Moreover

\[
                         X_*-qZ_*=1+D+Kq>0.
\tag{16}
\]

The dot product of \((X_*,Z_*)\) with
\((X-X_*,Z-Z_*)\) is consequently positive. Expanding
the squared distance proves the exact comparison

\[
\begin{split}
 Q=X^2+Z^2
  &>X_*^2+Z_*^2\\
  &=1+K^2+D^2+2(D\cos s+K\sin s)\\
  &\ge K^2+(D+1)^2.
\end{split}
\tag{17}
\]

In the final line use \(K\ge D\) and \(\cos s+\sin s\ge1\).
If A were outer, then \(K^2+D^2=Q\), contradicting the
middle line. Hence A is core. The final line also implies
\(D<1\), since \(D\ge1\) and \(K\ge D\) would give
\(K^2+(D+1)^2\ge5>Q\). Therefore A is on its flat core:
\(A=7/12\), \(K=13/12\).

The final line of (17) now implies \(D<82/125\), since

\[
       \left(\frac{13}{12}\right)^2
                  +\left(1+\frac{82}{125}\right)^2-Q
                                 =\frac{781}{2250000}>0.
\tag{18}
\]

Thus \(0<Y<39/250\). The middle line of (17), using
\(D\ge1/2\), also gives

\[
       Q>1+\left(\frac{13}{12}\right)^2+\frac14
                   +\cos s+\frac{13}{6}\sin s.
\tag{19}
\]

The right side increases on \([0,h]\), because its derivative
is greater than \(-13/20+(13/6)(3/4)=39/40>0\).
At \(s=1/4\), lower Taylor bounds give the exact reserve

\[
 1+\left(\frac{13}{12}\right)^2+\frac14
    +\left(1-\frac{s^2}{2}\right)
    +\frac{13}{6}\left(s-\frac{s^3}{6}\right)-Q
       \bigg|_{s=1/4}=\frac{6137}{480000}>0.
\tag{20}
\]

This forces \(s<1/4\) and proves (3).

The comparison (15)--(20) is the reflected form of the
negative-primary comparison in Section 4 of
[the low-GA/high-EH theorem](HAND_G3_HIGH_EH_EXCLUSION_UNDER_LOW_GA.md),
with its sharper angle estimate from Section 2 of
[the canceling core companion](HAND_G5_CORE_NEGATIVE_GA1_WITH_CANCELING_HG.md).
It has been written here directly to make the original
states, sign assumptions and same-state owner conclusion
explicit.
