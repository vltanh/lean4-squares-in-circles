# An outer E supplies the secondary witness at every negative primary E edge

## 1. Local same-state comparison

Put
\[
 Q=\frac{9789}{2500},\qquad h=\frac7{10},\qquad
 a_0=\sqrt{Q-\frac14}-\frac12,\qquad
 c_0=\sqrt{Q/2}-\frac12,
\]
and let D, E and H have sorted magnitudes
\(a_i\ge b_i\ge0\), with signed tangents respectively
negative, nonpositive and positive. Assume E is outer at Q,
and D and H are contained at that ceiling:
\[
 (a_E+\tfrac12)^2+(b_E+\tfrac12)^2=Q,
 \qquad
 (a_i+\tfrac12)^2+(b_i+\tfrac12)^2\le Q\quad(i=D,H).
\tag{1}
\]
The following two conclusions concern actual projections at
the unchanged states and frames:

* If DE3 is feasible at an error \(-s\), \(0\le s\le h\),
  then DE2 is feasible there as well.
* If EH1 is feasible at an error \(-s\), \(0\le s\le h\),
  then EH0 is feasible there as well.

The two claims are independent. No assumption on the other
error, their sum, or the order of D and H is needed.
In particular, selecting either resulting actual witness changes
no state, frame, error, or positive/negative variation.

Use the usual threshold
\[
                   W(s)=\frac{1+\cos s+\sin s}{2}.
\tag{2}
\]
At \(s=0\), the respective owner projections coincide, so
we may assume \(s>0\) in the proofs.

## 2. Negative DE3: two elementary outer-arc supports

Write \(q=\tan(s/2)\). On the whole interval,
\[
 q<\frac{183}{500},\qquad a_0>\frac{707}{500},\qquad
 c_0<\frac9{10},\qquad
       a_0>c_0(1+q).
\tag{3}
\]
For the first bound, the exact Taylor reserve is
\[
 \frac{183}{500}C_6(7/20)-S_5(7/20)
                 =\frac{7007815411}{7680000000000}>0.
\]
The two radical comparisons have reserves
\[
 Q-\frac14-\left(\frac{957}{500}\right)^2
       =\frac{551}{250000}>0,
 \qquad
 \left(\frac75\right)^2-\frac Q2=\frac{11}{5000}>0.
\]
The remaining comparison follows from
\[
 \frac{707}{500}-\frac9{10}\left(1+\frac{183}{500}\right)
                         =\frac{923}{5000}>0.
\tag{4}
\]

Let \(a(b)=\sqrt{Q-(b+1/2)^2}-1/2\) denote the sorted
outer arc. Its derivative belongs to \([-1,0]\), so
\(q a(b)+b\) increases on \([0,c_0]\). The actual D
containment and sorting therefore give
\[
                           q a_D+b_D\le(1+q)c_0.
\tag{5}
\]
On the other hand, \(a(b)+qb\) is concave. Its minimum is
at an arc endpoint, whose two values are \(a_0\) and
\((1+q)c_0\). Thus (1), (3) imply
\[
                           a_E+qb_E\ge(1+q)c_0.
\tag{6}
\]

The exact original projections at error \(-s\) are
\[
 P_{DE3}=a_D-a_E\sin s+b_E\cos s,
 \qquad
 P_{DE2}=a_D\cos s-b_D\sin s+b_E.
\]
Their difference is
\[
 P_{DE3}-P_{DE2}
   =\sin s\{q a_D+b_D-a_E-qb_E\}\le0
\tag{7}
\]
by (5)--(6). Feasibility of DE3 therefore gives feasibility
of the actual DE2 projection.

## 3. Negative EH1: its only possible failure of EH0 would exceed the circle

The two projections are
\[
 P_{EH1}=a_H-a_E\sin s-b_E\cos s,
 \qquad
 P_{EH0}=a_H\cos s-b_H\sin s-b_E.
\tag{8}
\]
Suppose EH1 is feasible but EH0 is not. Put
\[
 K=a_E+\frac12,\quad D=b_E+\frac12,\quad
 X=a_H+\frac12,\quad Z=b_H+\frac12,
 \qquad q=\tan(s/2).
\tag{9}
\]
Define the exact contact vector
\[
 X_*=1+D\cos s+K\sin s,
 \qquad Z_*=K\cos s-D\sin s.
\tag{10}
\]
Sorting gives \(K\ge D>0\), and \(s\le h<\pi/4\),
so \(Z_*>0\).

The feasible EH1 inequality is exactly \(X\ge X_*\).
Since \(P_{EH1}\ge W(s)>P_{EH0}\), subtracting the
projections in (8) yields
\[
                         Z>Z_*-q(X-X_*).
\tag{11}
\]
The half-angle identities also give
\[
                         X_*-qZ_*=1+D+Kq>0.
\tag{12}
\]
Consequently the dot product of \((X_*,Z_*)\) with
\((X-X_*,Z-Z_*)\) is strictly positive. Expanding the
squared distance gives
\[
 \begin{split}
 X^2+Z^2
  &>X_*^2+Z_*^2\\
  &=1+K^2+D^2+2(D\cos s+K\sin s)\\
  &>Q,
 \end{split}
\tag{13}
\]
where E's actual outer equality supplies \(K^2+D^2=Q\).
This contradicts H's retained containment. Hence the actual
EH0 witness is feasible whenever EH1 is feasible at a
nonpositive error.

This is the same local shifted-circle comparison used in the
negative-primary entry lemmas, written directly for the E edge.
It requires no preceding zero edge and no marker bound.

## 4. Complete outer-E owner scope in the two fixed-stress regimes

Consider an original high-GA, low-EH G0--G2 boundary cycle
with outer H, G, B and D of signs positive, negative,
negative, negative, and with outer nonpositive E. Retain
BT2 and either HG owner. Allow arbitrary original errors
and both original choices
\[
                            DE\in\{2,3\},\qquad EH\in\{0,1\}.
\tag{14}
\]
Then the cycle is impossible in either of the following
two A/T regimes:

1. GA2 and AB0 may have arbitrary errors; selected GA3
   or AB2 alternatives have nonpositive errors. TD0 has
   arbitrary error, or TD2 has nonpositive error.
2. The A edges have the secondary pair, one nonnegative
   primary error a, or both primary errors with nonnegative
   signed sum a, where \(0\le a\le1/6\). The unselected
   secondary A edge, if any, has arbitrary error. Again TD0
   has arbitrary error, or TD2 has nonpositive error.

To prove this, select the actual secondary witness at every
nonpositive E-primary error, using Sections 2--3. No error
or variation changes. Every retained E primary now has
strictly positive error. If at least one remains, its
single or combined E total is nonnegative, so the corresponding
fixed-stress exclusion in Sections 6--7 of
[the signed E-primary theorem](HAND_G3_COMBINING_THE_TWO_E_PRIMARY_ERRORS.md)
applies. If none remains, the already proved secondary-E
theorems cited in those same sections apply directly.

Thus (14) includes every sign allocation and every original
E-owner choice in either displayed A/T regime. In particular,
any genuinely negative primary E exception in the original
radial-boundary setting must have core E. Positive TD2 and
the other A-primary regimes are not removed by this corollary.
