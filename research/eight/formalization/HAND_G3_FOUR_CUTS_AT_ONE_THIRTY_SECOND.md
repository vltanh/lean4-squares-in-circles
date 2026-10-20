# Four tangent cuts follow at S <= 1/32 without an earlier cut

## 1. Exact theorem and dependency boundary

Assume the G0--G2 actual candidate geometry at
\[
q\le Q=9789/2500,
\]
with own-frame centers \((a_i,-y_i)\), \(a_i\ge |y_i|\), cyclic roles
\((H,G,A,B,T,D,E)\), and quarter word \(0101011\). Write
\[
S=|d_H|+|d_A|+|d_B|+|d_T|+|d_D|,
\qquad u_i=y_i/a_i.
\]
Retain the G2 normalization \(y_E\le0\). If \(S\le1/32\), then
\[
\boxed{u_G<-1/20,\qquad 1/20<u_T<4/5.}                 \tag{1}
\]
These statements assume no earlier tangent cut, prescribed sign,
quarter owner, mixed owner, radial kind, or tilt window. They use only
the G0--G2 zero-primary theorem: every original feasible witness on
HG, AB and TD belongs to axes \(\{0,2\}\).

The same hypotheses also give the fourth cut
\[
\boxed{u_D<-1/2.}                                    \tag{2}
\]
For this fourth cut, first apply the cut-free quarter-owner theorem
`HAND_G3_B_OWNER_WITHOUT_TANGENT_CUTS_AT_ONE_THIRTY_SECOND.md`.
It provides an actually feasible BT witness in \(\{2,3\}\) from exactly
the current hypotheses, using the cut-free DE theorem first. None of
the tangent cuts in this note is an input to either owner theorem.
Every witness tie is retained.

This is a reordered local capture theorem. It does not prove the
global hypothesis \(S\le1/32\), the other G3 cuts, or either remaining
mismatch contraction. Its purpose is to make explicit which tangent
premises are automatic once a sufficiently small mismatch has been
derived without assuming those same cuts.

## 2. Containment and a shared nominal error estimate

The actual farthest corner satisfies
\[
(a_i+1/2)^2+(|y_i|+1/2)^2\le Q.                        \tag{3}
\]
The entry core bound and (3) give the strict bounds
\[
a_i>L:=447/800,\qquad a_i<U:=283/200,
\qquad |y_i|<9/10,\qquad |p_i|<U.                    \tag{4}
\]
The lower bound follows from
\(a_i\ge1/2+1/(12\sqrt2)>447/800\). The primary upper bound
follows by substituting U into \((a+1/2)^2+1/4\). The transverse
bound uses \(a_i\ge|y_i|\) and \(2(7/5)^2>Q\). For the center norm,
write \(R_i=|p_i|\). Then \(a_i+|y_i|\ge R_i\) and (3) imply
\(R_i^2+R_i+1/2\le Q\), hence
\(R_i\le\sqrt{Q-1/4}-1/2<U\). See also
`HAND_G3_CENTER_NORM_AND_HIGH_TAIL_DIRECTIONS.md`.

Set
\[
\rho=1/32.
\]
For every original axis on a zero or quarter edge with absolute frame
error \(e\le\rho\), the projection changes from its nominal quarter
angle by at most \(Ue\). Its actual support width satisfies
\[
W(e)\ge1+e/2-e^2/4-e^3/12.
\]
Thus a feasible original witness obeys
\[
P^{\rm nominal}\ge1-(183/200)e-e^2/4-e^3/12\ge1-e.    \tag{5}
\]
Indeed
\[
1-183/200-e/4-e^2/12\ge1-183/200-\rho/4-\rho^2/12
=23687/307200>0.
\]
The nominal projections on the original zero axes are both
\(y_i-y_{i+1}\). On a quarter edge the original axes 0 and 1 have
nominal projection \(a_{i+1}+y_i\), and axes 2 and 3 have nominal
projection \(a_i-y_{i+1}\). These identities require no sign.

In particular, (5) on each actual zero edge gives
\[
y_i-y_{i+1}\ge1-\rho=31/32>9/10.
\]
Using (4), its source is strictly positive and its target strictly
negative. Hence all six zero-edge signs are already forced:
\[
(y_H,y_G,y_A,y_B,y_T,y_D)\in(+,-,+,-,+,-).             \tag{6}
\]
This derivation is included to keep the proof independent of the
earlier sign lemma and its stated threshold.

## 3. A complete zero-edge exclusion for a transverse coordinate near zero

Consider any actual zero edge with source \((a,-y)\), target
\((A,-Y)\), and \(|d|\le\rho\). Its two originally available
projections are
\[
P_0=y+A\sin d-Y\cos d,
\qquad P_2=a\sin d+y\cos d-Y.                         \tag{7}
\]
We prove that \(Y\ge-A/20\) is impossible.

For \(d\le0\), positivity of a and A, \(\cos d\le1\), and (4)
give
\[
P_0<9/10+U/20,
\qquad P_2<9/10+U/20.
\]
For the second bound, if \(y\ge0\) use \(y\cos d\le y\);
if \(y<0\), use \(y\cos d\le0\). The first bound similarly
uses \(-Y\cos d\le U/20\). Since
\(9/10+U/20=3883/4000<1\le W(d)\), neither original zero axis
can separate.

Suppose now \(0\le d\le\rho\), and write \(s=\sin d\),
\(c=\cos d\), so \(c\ge s\ge0\). For any contained state
with \(a\ge b\ge0\), one has \(a+b<9/5\) by Cauchy in (3).
Consequently
\[
as+bc\le\tfrac12(a+b)(s+c)<\tfrac9{10}(s+c).           \tag{8}
\]
This also bounds \(as+yc\) when y is negative, by first replacing
y with \(|y|\). From (7),
\[
P_0<9/10+U(s+c/20),
\qquad P_2<\tfrac9{10}(s+c)+U/20.                    \tag{9}
\]
Subtract \(W=(1+c+s)/2\) from the first expression. Since
\(s\le d\) and \(c\ge1-d^2/2\),
\[
\begin{aligned}
P_0-W
&<\frac25+\frac{183}{200}s-\frac{1717}{4000}c\\
&\le-\frac{117}{4000}+\frac{183}{200}d
                         +\frac{1717}{8000}d^2\\
&\le-\frac{3659}{8192000}<0.                          \tag{10}
\end{aligned}
\]
The last polynomial is increasing on \([0,\rho]\), so its upper
bound is its value at \(\rho=1/32\).
For the other axis use \(s+c\le1+d\) in (9):
\[
P_2-W<\frac25(s+c)+\frac{U}{20}-\frac12
\le\frac25(1+\rho)+\frac{U}{20}-\frac12
=-\frac{67}{4000}<0.                                \tag{11}
\]
Both full angle halves and their common endpoint are covered.
Therefore every such zero edge has \(Y<-A/20\).

Apply this to HG to obtain \(u_G<-1/20\). To obtain the source
conclusion on TD, replace the ordered signed states by
\[
(a,y),(A,Y)\longmapsto(A,-Y),(a,-y),
\]
while keeping d unchanged. This exchanges \(P_0\) and \(P_2\)
exactly, and keeps every hypothesis in (3)--(4). The target conclusion
for the exchanged pair is \(-y<-a/20\), hence \(y>a/20\).
Applying it to TD proves \(u_T>1/20\). This is an exact pair
identity, not a reflection of the full cycle or of its mismatch set.

## 4. The AB--BT path excludes the full high-T tail

Suppose \(y_T\ge(4/5)a_T\). Then containment implies
\[
a_T<1,\qquad y_T>(4/5)L=447/1000.                    \tag{12}
\]
Indeed, \(a_T\ge1\) would put its farthest corner beyond Q, since
\((3/2)^2+(13/10)^2=197/50>Q\).

Put \(e_A=|d_A|\), \(e_B=|d_B|\). A feasible original BT axis
0 or 1, together with either original AB zero axis, would give by (5)
\[
a_T+y_A\ge2-e_A-e_B\ge2-\rho=63/32.
\]
But (4) and (12) bound this sum strictly below \(19/10\), a
contradiction with reserve \(11/160\).

A feasible original BT axis 2 or 3 would instead give
\[
a_B-y_T\ge1-e_B\ge31/32.
\]
Equations (4), (12) bound its left side strictly below
\[
U-447/1000=121/125,
\]
leaving a strict reserve \(3/4000\). Every original BT witness is
therefore excluded. This proves \(u_T<4/5\), completing (1).

## 5. The cut-free BT theorem supplies the D magnitude cut

Apply the cut-free quarter-owner theorem named in Section 1, which
assumes (1)'s hypotheses and none of its conclusions. Choose an actual
BT witness; it belongs to axes 2 or 3. By (6), write
\(b_A=y_A\), \(b_B=-y_B\), \(b_T=y_T\), \(b_D=-y_D\),
all positive. Suppose \(u_D\ge-1/2\); then \(b_D\le a_D/2\).
Its corner disk forces \(b_D<29/50\), because
\[
\left(2\frac{29}{50}+\frac12\right)^2+
\left(\frac{29}{50}+\frac12\right)^2-Q=4/625>0.         \tag{13}
\]
Let \(e_A=|d_A|\), \(e_B=|d_B|\), \(e_T=|d_T|\).
The AB nominal inequality and \(b_A<9/10\) give
\[
b_B>1/10-e_A.                                       \tag{14}
\]
Add the nominal inequalities of the actual intended BT witness and
an actual TD zero witness. The T transverse coordinate cancels:
\[
a_B+b_D\ge2-e_B-e_T\ge2-(\rho-e_A).
\]
By (13),
\[
a_B+1/2>1511/800+e_A,
\qquad b_B+1/2>3/5-e_A.                              \tag{15}
\]
Both lower bounds are positive on \(0\le e_A\le\rho\). Their
squares contradict the B corner disk, because the exact polynomial is
\[
\begin{aligned}
&\left(\frac{1511}{800}+e_A\right)^2
+\left(\frac35-e_A\right)^2-Q\\
&\quad=\frac{7537}{640000}
+\frac{1031}{400}e_A+2e_A^2>0.                       \tag{16}
\end{aligned}
\]
Every coefficient is positive. Thus \(u_D<-1/2\), proving (2).
The same total \(\rho-e_A\) was used on BT and TD, which is
essential to (15); assigning an independent \(\rho\) to each edge
would not prove the stated comparison.

## 6. Coverage and remaining obligations

The proof uses original centers with their original corner inequalities.
It includes core/outer interiors and joins, all prescribed sign-zero
boundaries, both original zero axes, every original BT axis, and weak
axis ties. No boundary retraction or radius-transfer premise is hidden
inside any tangent conclusion.

The conclusion is all four cuts (1)--(2) under \(S\le1/32\).
The first three have the elementary proof in Sections 2--4; the fourth
uses the now-established cut-free quarter-owner theorem in forward
order. No statement here supplies the unrestricted G3 tangent cuts
before mismatch contraction. The bounds \(u_G>-4/5\) and
\(u_H>1/2\), and the global capture of S, remain separate obligations.

All arithmetic in (5), (10)--(16) is a displayed rational comparison or
one degree-two identity. Numerical exploration was used to identify the
short zero-edge mechanism, but no sampled configuration, angular mesh,
generated coefficient inventory, or program success status is a proof
premise. No Lean source was changed and no compilation or CI was run.
