# Exceptional negative T at an arbitrary actual EH0 contact

## 1. Extension of both negative-T endpoint theorems

Retain every hypothesis of the
[critical negative-T theorem](HAND_G5_EXCEPTIONAL_E_ALIGNED_NEGATIVE_T_CRITICAL_STRIP.md)
or the
[outside-strip negative-T theorem](HAND_G5_EXCEPTIONAL_E_ALIGNED_NEGATIVE_T_OUTSIDE_CRITICAL_STRIP.md),
except replace EH alignment and its contact by the actual weak
EH0 contact
\[
 a_H\cos\rho+b_H\sin\rho+y_E=W(\rho),\qquad
 \rho=d_{EH},\qquad y_E\ge0.
\tag{1}
\]
The signed error rho is arbitrary. It belongs to the original
cyclic error list, whose positive and negative variations are at
most h=.7. The other primary errors remain x=d_GA>=0,
e=d_DE>=0, t=x+e. Retain either negative TD2 with BT2, or negative
BT3 with aligned TD0, with its error -s<0. T retains the original
core/outer-q boundary alternative used for local secondary
reselection. No other state needs an outer-circle equality.

**Extension theorem.** Both parent conclusions remain valid.
On .1<=t<=.16 and q<=q_*, a genuine unavailable secondary T owner
is strictly impossible; after same-state secondary reselection
the sharp conclusion is x=0. On [0,.1] union [.16,.7] and q<=Q1,
every such system is strictly impossible. These statements retain
all weak contacts, both AB owners, either G sign, and either E
radial kind. They make no E-sign reflection or geometric motion.

The secondary-reselection cases use the arbitrary-contact base
extension in
[the sign-free BT2/TD0 entry](HAND_G5_COUPLED_OUTER_E_SIGN_FREE_BT2_TD0_ENTRY.md).
The proof below supplies the additional negative-T argument.

## 2. The split and secants are unchanged

Use the same positive coefficients k,l,c,eta as the appropriate
parent, and put
\[
 f(v)=\cos v+\eta\sin v,\qquad n=kf(x),\qquad p=f(e).
\tag{2}
\]
The varying EH weight p multiplies the exact zero residual in
(1), independently of rho. Thus the actual-coordinate split
x+e=t has precisely the parent second derivative. More explicitly,
write u=d_HG and
\[
 R_H=W(u)-a_H\sin u-b_H\cos u>-.065.
\]
After the original G support bound, its x-dependent part is
n R_H+kW(x)-k sigma_eta sin x. The e-dependent part, before
maximizing E, is W(e)-a_E sin e+y_E cos e. Their second derivative
along the split is at most
\[
 k\{-.435\cos x+.956\sin x\}-.5\cos e+.915\sin e
\tag{3}
\]
in the critical strip, with .957 replacing .956 outside it.
These are the already proved strict split bounds. Only the two
faces (x,e)=(0,t),(t,0) remain.

The signed T cancellation uses the identical secant weights:
(BT,TD)=(c,c sec s) in the TD case and (c sec s,c) in the aligned
BT case. Consequently both exact secant gains, the sorted D
correction, and every scalar baseline remain identical to the
parents. The local B/T/D secondary-or-flat entry uses no EH data.

## 3. Collect the two actual H rotations on one circle

The sole angular change is that H now has two ordinary arguments,
u and rho. Its actual force is
\[
 F_H=(p\cos\rho+n\sin u,\ p\sin\rho+n\cos u),
\quad
 \|F_H\|^2=p^2+n^2+2pn\sin(u+\rho).
\tag{4}
\]
This collects H's original containing circle once. With
psi(v)=cos v+(sin v)_+-1 and
N(v)=sqrt(p^2+n^2+2pn sin v), its exact ordinary increment is
\[
 p\psi(\rho)+n\psi(u)-R\{N(u+\rho)-N(0)\}.
\tag{5}
\]
Let a=min(p,n), b=max(p,n), and r=a/b. If P and N_- are the
positive and negative ordinary totals within this H block, (5)
is bounded below by the canonical mixed block
\[
 \Psi_H(P,N_-)=a\{\phi(P)-1\}+b(\cos N_- -1)
 -R\{\sqrt{a^2+b^2+2ab\sin(P-N_-)}-\sqrt{a^2+b^2}\},
 \quad \phi(v)=\cos v+\sin v.
\tag{6}
\]
For opposite signs this replaces the positive coefficient by the
smaller and the negative coefficient by the larger. For equal
signs, the additional merging follows from concavity and the zero
values at zero of phi(v)-1 and cos v-1. Hence the appropriate H
pure negative charge is V_H=V_{a,b}^{b}, not V_{p,n}^{n}.

At either split face the parent coefficient bounds give
\[
\begin{array}{c|cc}
 &a\text{ lower}&b\text{ upper}\\ \hline
 \text{critical}&.925&1.04\\
 \text{outside low}&.86265&1.05\\
 \text{outside middle/high}&.97&1.053.
\end{array}
\tag{7}
\]
In all three rows r>2/3. In particular H is a valid separately
concave mixed block under the whole-angle norm lemma. A remains
a one-angle block; B is mixed only in the TD regime; D still has
no ordinary argument. The original concentration therefore adds
only the same-block H alternative. It never assigns two signs
to the actual one-angle A block.

Here are both required H same-block comparisons, on the entire
signed domain. For a negative net d>=0, put P=h-d. The saturated
H term minus its pure V_H(d) is
\[
 a(\phi(P)-1)+b(\cos h-\cos d)\ge0.
\tag{8}
\]
Indeed replace a/b by 2/3 and divide by 2b/3. The result is
(1-(3/2)cos h)(cos P-1)+(1-(3/2)sin h)sin P, whose two terms
are nonnegative because cos h>2/3>sin h.

For a positive net d=P-N_- with 0<=N_-<=P<=h, subtract the pure
U_H(d) from (6). The difference is
\[
 b\{r[\phi(P)-\phi(P-N_-)]+\cos N_- -1\}\ge0.
\tag{9}
\]
For N_->0, put v=N_-/2 and divide by 2b sin v. The quotient is
r(cos(P-v)-sin(P-v))-sin v. It is at least
(2/3)(cos(h-v)-sin(h-v))-sin v. After division by cos v this
last expression is affine and decreasing in tan v, since
(2/3)(cos h+sin h)<1. Its far value before division is greater
than
\[
 (2/3)(15/16-7/20)-7/20=1/24>0.
\tag{10}
\]
Here cos(h/2)>15/16 and sin(h/2)<7/20. At N_-=0 the difference
is exactly zero. Thus the new H block also pays every positive-net
cancellation pattern.

## 4. The critical-strip envelope and sharp endpoint stay unchanged

Although H's negative coefficient is now b=max(p,n), its pure
and far comparisons remain valid: their proofs used only that
both H coefficients exceed .925, one is at least 1, and b<1.04.
For 0<d<=.16, the square-root tangent gives explicitly
\[
 V_H(d)\ge1.343\sin d-1.04(1-\cos d)>1.25d>V_B(d).
\tag{11}
\]
The rational reserve in the middle comparison after division by
d is 7631/1875000. At d=0 all pure charges vanish. At h,
\[
 V_H(h)>1.9787(1.3622-.8148)+1.04(.7648-1)>.83>V_B(h).
\tag{12}
\]
The displayed radical bounds follow by positive squaring for the
pair (.925,1), using sin h>.6442; the reserve above .83 is
426619/50000000. Norm-gain monotonicity on the relevant coefficient
rectangle justifies comparison to that pair.

Equations (8), (11), (12) remove the new H same-block and pure
alternatives. The existing positive cost -.545(1.04)P and all
separated comparisons are unchanged. For s<=t the full envelope
is still min(V_A(t-s),V_B(t-s)); for s>=t it is still at least
-.545(1.04)(s-t), now also using (9) for H. The exact secant
endpoint factors J_D and J_B in the critical parent are therefore
unchanged, including their strict reserves. Its hard-defect
identity and strict G/E split give the stated sharp conclusion.

## 5. The outside-strip scalars already cover the larger H coefficient

In the low family, the positive cost is still -.573P and every
H coefficient is below 1.05. With the new V_H=V_{a,b}^{b}, the
parent fixed-ratio chord comparison remains applicable: r>.82,
b>=1, so its weaker ratio .585 and scale .862 still apply.
In the middle/high families r>2/3 and b>=1 give V_H'>.674>.619.
Thus the separated comparisons and negative-net pure envelope
are unchanged after replacing H's pure charge by this new V_H.
Equations (8)--(9) handle its new same-block alternatives for
both signs of t-s. All other block estimates are identical.

At the unshifted secant endpoint s=0, the existing low-family
H comparison still dominates B: for t>0 the proof uses only
b<1.05 and gives V_H(t)>1.17t, whereas V_B(t)<1.15t; at t=0
all pure charges vanish. The middle/high pure
scalars already use the weaker H coefficient 1.06. At every capped
endpoint s=a in the negative-T proof, all 44 scalar constructions
likewise already use that same coefficient 1.06. It exceeds both
p and n, since k<=1 and
\[
 f(v)\le\sqrt{1+\eta^2}<1.053<1.06.
\tag{13}
\]
Because cos(t-a)-1<=0, this is a valid weakening after angular
concentration. Every squared norm and polynomial numerator is
unchanged. The parent uniform endpoint margin >.00014 therefore
holds, and its secant concavity/monotonicity finishes the strict
outside-strip contradiction.

The extra EH error has only enlarged the list of actual ordinary
arguments. Their exact totals remain N-P=t-s, P<=h-t, N<=h-s.
No original error has been discarded, no individual witness has
been replaced by its aligned formula, and no circle equality has
been inferred from this scalar reduction.
