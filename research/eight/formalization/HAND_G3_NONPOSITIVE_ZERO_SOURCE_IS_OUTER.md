# Every nonpositive zero source is outer

## 1. A global statement for one original zero edge

Work on the original G0--G2 boundary cycle at
\(Q=9789/2500\). On any one of its three zero-quarter edges,
write the signed source and target tangents as y and Y.
Then
\[
 \boxed{\quad y\le0\quad\Longrightarrow\quad
             \text{the source boundary state is outer}.\quad}       \tag{1}
\]
This theorem does not assume the signs of the other two zero
sources, any preferred quarter owner, or any frame order. It
also does not require the normalization \(y_E\le0\).

The global zero-owner/sign theorem says that the actual zero
owner must be 2 when y is nonpositive, and its target has
strictly negative tangent. Write \(y=-b\), \(Y=-B\), with
\(b\ge0\) and \(B>0\). Its original feasible projection is
\[
       a\sin d-b\cos d+B\ge W(d),\qquad
       W(d)=\frac{1+\cos d+|\sin d|}{2}.               \tag{2}
\]
The global variation bound and elementary geometry give
\[
 |d|<\frac7{10},\qquad b,B<\frac9{10}.                \tag{3}
\]
For nonpositive d the left side of (2) is at most B<9/10,
whereas its right side is at least 1. Hence d>0.

Suppose, for a contradiction, that this source is core.
Its primary coordinate then satisfies \(a\le7/12\).
The following three coarse bounds already contradict the
unchanged original cyclic marker sum.

## 2. A core source would force a large angle and tiny tangent

For \(0\le d\le7/10\), the whole-interval bounds
\[
              \cos d>\frac{19}{25},\qquad
              \sin d<\frac{13}{20}                   \tag{4}
\]
follow from the alternating Taylor inequalities displayed in
`HAND_G3_GLOBAL_D_IS_OUTER.md`, Section 2. At d=0 the strict
cosine bound is also immediate.

Subtract W in (2) and use \(a\le7/12\):
\[
 P_2-W\le \frac1{12}\sin d+B-\frac12
                     -\frac12\cos d-b\cos d.         \tag{5}
\]
If d were at most 2/5, the right side would be strictly less
than
\[
 \frac25-\frac12\{1-(2/5)^2/2\}+\frac1{12}\frac25
                       =-\frac2{75}<0.
\]
Thus
\[
                           d>\frac25.                \tag{6}
\]
Rearranging (5) and using (4) gives
\[
 B\ge\frac12+\frac12\cos d-\frac1{12}\sin d+b\cos d
       >\frac12+\frac12\frac{19}{25}-\frac1{12}\frac{13}{20}
       =\frac{991}{1200}>\frac{41}{50}.              \tag{7}
\]
Using B<9/10 in the same inequality gives
\[
 b\cos d<\frac25-\frac12\cos d+\frac1{12}\sin d.
\]
The exact positive cross-product reserve
\[
 \frac1{10}\frac{19}{25}
 -\left(\frac25-\frac12\frac{19}{25}
                       +\frac1{12}\frac{13}{20}\right)
                         =\frac{11}{6000}>0          \tag{8}
\]
therefore proves b<1/10.

In particular this core source lies on its flat side, so its
original marker is exactly
\[
 F_{\rm source}=1.077372\,b\le\frac{27}{25}b,
 \qquad \frac{27}{25}-1.077372=\frac{657}{250000}>0.  \tag{9}
\]
The universal original-marker lower plane from
`HAND_G3_BT_PATH_MARKER_AND_NEGATIVE_AB_COMPARISON.md`
applies to every target radial kind:
\[
                    F_{\rm target}\ge\frac{43}{50}B. \tag{10}
\]
No outer substitution for the target is made here.

## 3. Contradiction with the six unchanged complementary edges

The original charge of the zero edge is
\[
 C=d+\ell_{\rm source}-\ell_{\rm target}
       =d-F_{\rm source}+F_{\rm target}.
\]
Equations (6)--(10) imply
\[
 C>\frac25-\frac{27}{25}\frac1{10}
                   +\frac{43}{50}\frac{41}{50}
                      =\frac{2493}{2500}.           \tag{11}
\]
Each of the six other original edges has G1 charge greater
than \(\Gamma=8833/10000\). The seven original charges
sum exactly to \(2\pi\). But
\[
 \frac{2493}{2500}+6\frac{8833}{10000}-\frac{710}{113}
                       =\frac{1561}{113000}>0,
 \qquad 2\pi<\frac{710}{113}.                       \tag{12}
\]
This contradiction proves (1).

Consequently any core H, A, or T in the remaining global
owner branches has strictly positive signed tangent. This
individual conclusion strengthens the earlier simultaneous
radial result in
`HAND_G3_ALL_NONPOSITIVE_ZERO_SOURCES_ARE_OUTER.md`;
that note's stronger angle and chart conclusions still use
its three-sign hypothesis.

The proof uses one original projection, the original core
marker, the universal marker lower plane, and the unchanged
cyclic G1 sum. Its estimates hold on whole intervals, with
the exact rational reserves printed above. No state mesh,
angle subdivision, numerical feasibility result, Lean
compilation or CI is a premise.
