# Positive GA with both E edges secondary: every required T regime

## 1. Actual domain and conclusion

Put
\[
 q_L=19577/5000,\qquad Q=9789/2500,\qquad
 R=\sqrt Q,\qquad h=7/10.
\tag{1}
\]
All terminating decimals below are exact rationals. Work at one
original common radius \(q_L\le q\le Q\), in the boundary-neighbor
domain of the
[boundary bridge](HAND_G3_BOUNDARY_NEIGHBOR_TRANSPORT_AND_E_ZERO_EXCLUSION.md).
The sorted outer anchors H,A have positive tangents and B,D have
negative tangents. G and T may have either sign and are on their
actual outer circle or true core. Every state is contained at q.
For E there is **no sign or radial-kind hypothesis**: its two
coordinates will cancel from the proof.

Retain actual HG2, GA1 with \(x=d_{GA}\ge0\), either actual AB0
or AB2, and actual DE2 and EH0. Their errors are their actual
frame differences, sum to zero, and have positive and negative
variations at most h. Both E errors and every ordinary error
may have either sign. Retain any one of these T regimes:
\[
\begin{array}{c|c|l}
 BT&TD&\text{condition}\\ \hline
 2&0&\text{both errors arbitrary}\\
 2&2&\text{both errors arbitrary}\\
 3&0&d_{BT}\ge0,\quad d_{TD}\text{ arbitrary}\\
 3&0&d_{BT}<0,\quad d_{TD}=0.
\end{array}
\tag{2}
\]

**Theorem.** No necessary cycle satisfying these hypotheses exists.
The contradiction is strict at Q, and includes every weak
zero-angle witness tie. Consequently it also holds at the smaller
ceiling \(Q_1=1957767069/500000000\) used by the sole-E endpoint
theorems.

This is the zero-primary-charge specialization of the
[complete core-E stress](HAND_G5_POSITIVE_GA_HG2_CORE_E_COMPLETE_EXCLUSION.md).
The specialization removes the core-E and E-sign hypotheses;
it does not reinterpret an outer E as a core state. The proof
below identifies every place where E could otherwise enter.

## 2. The two actual E rotations remain ordinary

Write \(y_E\) for E's signed tangent and use positive magnitudes
\(a_D,b_D,a_H,b_H\) at its normal anchors. With
\[
 W(v)=(1+\cos v+|\sin v|)/2,\qquad
 \delta=d_{DE},\quad\rho=d_{EH},
\]
the retained projections are
\[
 a_D\cos\delta+b_D\sin\delta-y_E\ge W(\delta),
\]
\[
 a_H\cos\rho+b_H\sin\rho+y_E\ge W(\rho).
\tag{3}
\]
Give both inequalities weight 1. Their signed E forces cancel
identically; no radial E force occurs. Hence no support bound,
core coordinate, tangent sign, boundary equality, or motion of E
is required.

The error delta remains the actual radial ordinary rotation at
D, and rho remains the actual radial ordinary rotation at H.
In particular, neither angle has been set to zero. The other
ordinary rotations remain HG2 at H, AB0 at B or AB2 at A, BT2
at B when selected, and TD0 at D when selected. Thus the actual
one-angle and two-angle blocks are exactly those in Sections 2--3
of the
[core-E angular envelope](HAND_G5_POSITIVE_GA_CORE_E_ANGULAR_ENVELOPE.md).
The E-primary total is the empty sum, equal to zero, and its
extra primary charge is exactly zero. This statement places no
condition on the actual value of \(y_E\).

## 3. The positive and secondary T cases

Put \(k=.863\). In the first row of (2), set z=0. For a
nonnegative TD2 or BT3 in the second or third row, let z denote
its nonnegative primary error. Set \(d=x+z\le h\), and use
\[
 l=.5052+.49d-.108d^2,\qquad c=k,\qquad
 \eta=.25+.1645d,\qquad \lambda=1.03,
\]
\[
 f(v)=\cos v+\eta\sin v,\qquad n=kf(x),\qquad m=kf(z).
\tag{4}
\]
Give HG,GA,AB weights n,k,l. For BT2/TD0 give both T edges
weight k. For a positive TD2 give BT2,TD2 weights m,k; for a
positive BT3 give BT3,TD0 weights k,m. The E weights stay 1.
All weights are positive. The G and T forces are exactly the
signed forces in Section 2 of the core-E stress, and its
shifted-circle bounds use only their actual containment, not
their tangent signs.

Define
\[
 C_\eta(v)=1+2\cos v+
       \{1+2\eta-R\sqrt{1+\eta^2}\}\sin v,
\]
\[
 V_{l,k}(v)=k(\cos v-1)
 -R\{\sqrt{k^2+l^2-2kl\sin v}-\sqrt{k^2+l^2}\}.
\tag{5}
\]
For a positive TD2 the four zero-ordinary-error pairs are
\[
 (1,n),\quad(k,l),\quad(l,m),\quad(1,k).
\tag{6}
\]
For a positive BT3 the last two are \((l,k),(1,m)\). Its
baseline is no smaller than the TD2 baseline: for m at least k
and l below 1, the increment of \(\sqrt{l^2+m^2}\) as m grows
from k is at least the increment of \(\sqrt{1+m^2}\).

All the E rotations in (3) remain among the ordinary errors.
With no E primary, their variation constraints are precisely
the angular envelope's constraints with negative-primary
magnitude s=0. Its full concentration theorem therefore gives
ordinary increment at least \(V_{l,k}(d)\). This includes
all same-block and separated positive/negative allocations.

Section 9 of the core-E stress proves strict concavity in the
entire fixed positive split x+z=d and compares its two endpoints.
It requires no E coordinate. The resulting lower baseline is
\[
\begin{split}
 B_P(d)={}&3+2l+3k+kC_\eta(d)\\
 &-R\{2\sqrt{1+k^2}+\sqrt{k^2+l^2}
                  +\sqrt{l^2+k^2f(d)^2}\}.
\end{split}
\tag{7}
\]
The PV certificate in the
[scalar companion](HAND_G5_POSITIVE_GA_CORE_E_SCALAR_CERTIFICATES.md)
proves \(B_P+V_{l,k}(d)>0\) on the complete closed interval
[0,h]. Its explicit rational numerator has whole-interval
coefficient-norm lower bound greater than .00870, after the
companion's error allowance. The positive weighted sum of the
actual witnesses requires this same expression to be
nonpositive, a contradiction.

## 4. Negative T primaries use only the original B,T,D data

For a negative TD2 in the second row of (2), first reselect TD0
if it is already an actual weak witness. For the last row,
reselect BT2 if it is already available. These cases return to
Section 3, with the original angles and states unchanged.
At zero primary error the corresponding projections coincide.

Otherwise Sections 4--5 of the core-E stress use only B,T,D,
their actual radial kinds, and their original common q. They
show that T is on its true flat core and that its genuine
negative primary has magnitude s satisfying
\[
 a_T=7/12,\qquad
 \begin{cases}
 0<s<.3,&\text{negative TD2 with BT2},\\
 0<s<.09,&\text{negative BT3 with aligned TD0}.
 \end{cases}
\tag{8}
\]
No E hypothesis occurs in either argument. The aligned TD
condition in the second case is retained exactly as stated
in (2).

Now d=x and use family N:
\[
 l=.5054+.55d-.2d^2,\qquad
 c=.863+.35d-.15d^2,\qquad
 \eta=.38,\qquad\lambda=.8888+.2d.
\tag{9}
\]
Give HG,GA,AB weights \(kf(d),k,l\), and again give both E
edges weight 1. For negative TD2 give BT2,TD2 weights
\(c,c\sec s\); for negative BT3 give BT3,TD0 weights
\(c\sec s,c\). The exact signed T tangent cancels. The
known flat radial coordinate in (8) and the support comparison
give gain at least \(\lambda s\), as proved in those same
local sections.

The actual DE2 and EH0 rotations still belong to D and H.
The modified D or B block is one of the actual blocks treated
by the angular companion. Its constraints are
\[
 N-P=d-s,\qquad P\le h-d,\qquad N\le h-s.
\tag{10}
\]
The full envelope, including the negative-primary gain, is
at least
\[
                         \min\{V_{l,k}(d),\lambda d\}.
\tag{11}
\]
This is equation (33) of the core-E stress, specialized to no
negative E primary. Its proof does not invoke the later
core-E charge bound or any E transport.

The corresponding baseline is
\[
\begin{split}
 B_N(d)={}&3+2l+3c+kC_\eta(d)\\
 &-R\{\sqrt{1+k^2f(d)^2}+\sqrt{k^2+l^2}
                 +\sqrt{l^2+c^2}+\sqrt{1+c^2}\}.
\end{split}
\tag{12}
\]
The NV and NL certificates in the scalar companion prove
\[
 B_N+V_{l,k}(d)>0,\qquad B_N+\lambda d>0
                         \quad(0\le d\le h).
\tag{13}
\]
Their rational numerator lower bounds exceed .01173 and
.00938 respectively. Equations (11)--(13) contradict the
positive weighted sum of the actual weak witnesses.

## 5. Radius, signs, and equality

The sole local preprocessing in Section 4 is same-state
reselection of an already available secondary. Its original-q
outer/core comparisons remain at q. Q is used only as an upper
support ceiling and for strict scalar estimates. No actual
outer q state is relabeled as outer at Q.

Equation (3) proves that both signs and all radial kinds of E
are covered. Both actual E rotations are retained throughout,
and no conclusion about equality is transferred from a moved
state. The contradiction is strict even when x or any permitted
T primary is zero. This closes the both-secondary E row for
all four T regimes in (2), including the reflected sign of E.
