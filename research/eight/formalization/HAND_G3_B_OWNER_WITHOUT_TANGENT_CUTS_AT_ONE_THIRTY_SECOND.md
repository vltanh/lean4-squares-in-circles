# Both quarter-owner restrictions at S <= 1/32, without tangent cuts

## 1. Statement and forward dependencies

Assume the actual G0--G2 candidate geometry at
\[
q\le Q=9789/2500,\qquad
S=|d_H|+|d_A|+|d_B|+|d_T|+|d_D|\le\rho=1/32.
\tag{1}
\]
The roles are \((H,G,A,B,T,D,E)\), the quarter word is \(0101011\),
and the original own-frame centers are \((a_i,-y_i)\), with
\(a_i\ge |y_i|\). Retain the G2 normalization \(y_E\le0\) and
the previously proved global zero-primary restriction on HG, AB, TD.
Then
\[
\boxed{\text{every actually feasible original BT and DE axis is in }
\{2,3\}.}
\tag{2}
\]

The DE conclusion is supplied first by
`HAND_G3_D_OWNER_WITHOUT_TANGENT_CUTS_AT_ONE_THIRTY_SECOND.md`.
The present note proves the BT conclusion. No tangent cut on G, T, H
or D, no prescribed sign on a zero-edge endpoint, no earlier BT owner,
no mixed owner, no tilt window and no radial-boundary label is an input.
All circle inequalities are applied to the actual original centers.

The hypothesis on S in (1) remains conditional. This theorem does not
prove a global mismatch contraction or the global G3 tangent cuts.

## 2. One strengthened nominal estimate and the derived signs

Put
\[
L=447/800,\quad U=283/200,\quad V=349/250,
\qquad K=37/40,\quad M=383/200.
\]
The entry core bound and containment give
\[
a_i>L,\qquad |p_i|<U,\qquad a_i<U,\qquad
|y_i|<9/10,\qquad a_i+|y_i|<9/5.
\tag{3}
\]
The improved center-norm estimate in (3) is proved in
`HAND_G3_CENTER_NORM_AND_HIGH_TAIL_DIRECTIONS.md`. For completeness,
if \(R_i=|p_i|\), the original corner disk and
\(a_i+|y_i|\ge R_i\) give
\(R_i^2+R_i+1/2\le Q\), hence
\(R_i\le\sqrt{Q-1/4}-1/2<U\).

For each of the five aligned edges, let \(e_i=|d_i|\). An original
projection rotates only one adjacent center, so its change from its
nominal quarter angle is at most \(Ue_i\). The original support width
is at least
\[
1+e_i/2-e_i^2/4-e_i^3/12.
\]
Every feasible original aligned witness therefore has
\[
P_i^{\rm nom}\ge1-Ke_i.
\tag{4}
\]
Indeed, on \(0\le e_i\le\rho\), the required coefficient is
\(183/200+e_i/4+e_i^2/12\), and its difference below K is at least
\[
K-183/200-\rho/4-\rho^2/12=647/307200>0.
\]

The two globally allowed zero axes both have nominal projection
\(y_i-y_{i+1}\). Since \(1-K\rho>9/10\), the three zero edges
force the six strict signs. Write
\[
(y_H,y_G,y_A,y_B,y_T,y_D)
=(b_H,-b_G,b_A,-b_B,b_T,-b_D),\qquad b_E=-y_E\ge0.
\tag{5}
\]
Thus
\[
b_H+b_G\ge1-Ke_H,\quad b_A+b_B\ge1-Ke_A,
\quad b_T+b_D\ge1-Ke_T.
\tag{6}
\]
Each of these six positive magnitudes satisfies
\[
b_i>1/10-K\rho=91/1280>7/100,
\qquad a_i<V.
\tag{7}
\]
The last assertion follows directly from its corner disk, because
\[
(V+1/2)^2+(57/100)^2-Q=1029/250000>0.
\]
No cone other than \(a_i\ge b_i\) has been used.

Normalize \(\theta_A=0\), and put
\[
t=\theta_G-\theta_A,\qquad c=\cos t,\qquad s=\sin t,
\qquad W=(1+c+|s|)/2.
\]
The concentrated real frame gives
\[
c\ge3/4,\quad |s|\le13/20,\quad c^2+s^2=1,
\quad 1-c\le(4/7)s^2.
\tag{8}
\]
For the sine bound, use \(|t|<7/10\) and the alternating-series
upper bound on \(\sin(7/10)\).

GA has its exact phase \(\pi/2-t\). The nominal EH phase is
\(\pi/2+t\); the actual phase differs by
\(-d_H-d_A-d_B-d_T-d_D\), of magnitude at most S. The support width
is globally \(1/2\)-Lipschitz. Thus every feasible original EH witness
satisfies
\[
P_E^{\rm nom}\ge W-MS.
\tag{9}
\]
Here \(M=U+1/2\). In particular, a sum with HG and EH weights at
most one has total loss at most
\[
(K+M)S\le71/800.
\tag{10}
\]
This is one shared error budget.

## 3. An all-axis negative-tilt bound, without an H cone

In fact, under (1) alone,
\[
\boxed{s>-11/20.}
\tag{11}
\]
To prove this, suppose \(s=-r\) and \(r\ge11/20\). Then
\(3/4\le c\le21/25\): the upper bound follows from
\(c^2\le279/400<(21/25)^2\).

The four nominal EH projections, in original zero-based order, are
\[
ca_H-rb_H-b_E,\quad a_H-ra_E-cb_E,
\quad ca_E-rb_E-b_H,\quad a_E-ra_H-cb_H.
\tag{12}
\]
Use \(a_H<V\), \(b_H>7/100\), \(a_E<U\),
\(a_E,a_H>L\), and \(b_E\ge0\). Subtracting the corresponding
upper bounds from W gives at least
\[
3043/50000,\qquad981/16000,\qquad191/2500,
\qquad1517/16000,
\tag{13}
\]
respectively. These are substitutions in four affine expressions:
\[
\begin{aligned}
&1/2-(112/125)c+(57/100)r,\\
&1/2-V+c/2+(847/800)r,\\
&57/100-(183/200)c+r/2,\\
&1/2-U+(57/100)c+(847/800)r.
\end{aligned}
\]
The first and third use the largest c; the other two use its smallest
value. All use the smallest r. Each number in (13) exceeds
\(M\rho=383/6400\); the smallest reserve is \(813/800000\).
Every original EH witness consequently fails (9), proving (11).

Whenever \(s=-r\le0\), we may henceforth use the closed larger
domain
\[
0\le r\le11/20,\qquad83/100\le c\le1,
\qquad1-c\le(100/183)r^2\le r/3.
\tag{14}
\]
Here \(c^2\ge279/400>(83/100)^2\); the chord estimates follow
from \((1-c)(1+c)=r^2\).

## 4. Retain a forbidden BT witness and bound A

The DE theorem quoted in Section 1 is available without using anything
that follows. Choose any feasible DE witness; it has nominal projection
\(a_D+b_E\). Suppose now that an original BT axis 0 or 1 is feasible.
Retain that witness throughout. Its nominal projection is \(a_T-b_B\).
Adding it to AB gives
\[
b_A+a_T\ge2-K(e_A+e_B).
\tag{15}
\]
Since \(a_T<V\),
\[
b_A>2-V-K\rho>23/40,
\qquad a_A<7/6.
\tag{16}
\]
The first strict reserve is \(3/32000\). For the second, substitute
\(a_A=7/6\), \(b_A=23/40\) into the corner disk; the excess over Q
is \(6409/360000\).

The actual GA projections are
\[
\begin{array}{c|l}
0&ca_A-sb_A-b_G\\
1&a_A-sa_G-cb_G\\
2&ca_G-sb_G-b_A\\
3&a_G-sa_A-cb_A.
\end{array}
\tag{17}
\]
At least one of these original witnesses must be feasible.

### 4.1 GA axis 2 is impossible

Add its actual projection to AB and the retained BT inequality.
Replacing \(-s b_G\) by \(|s|b_G\) gives
\[
ca_G+|s|b_G+a_T\ge W+2-K(e_A+e_B).
\]
The G corner completion with mass \(1/4\) gives
\[
c(a_G+1/2)+|s|(b_G+1/2)\le Q/4+1.
\]
As \(c+|s|\ge1\), these force
\[
a_T+Q/4\ge5/2-K(e_A+e_B)\ge5/2-K\rho>U+Q/4,
\]
with reserve \(12351/160000\), contradicting \(a_T<U\).

### 4.2 GA axis 3 cannot have nonnegative sine

If \(s\ge0\), (7), (16) and \(a_A>L\) give
\[
W-P_{G,3}>-112/125+(43/40)c+(847/800)s
\ge651/4000>0,
\tag{18}
\]
because both direction coefficients are at least \(847/800\) and
\(c+s\ge1\).

### 4.3 GA axes 0 and 1 force a short nonnegative arc

For G0, add HG. Its demand minus the bound supplied by (16) and
\(b_H<9/10\) is at least
\[
3/5-(2/3)c+(43/40)s\ge-1/15+(43/40)s.
\]
If \(s\ge1/10\), this is at least \(49/1200>K\rho\),
with reserve \(229/19200\), impossible.

For G1, use \(a_A<7/6\), \(a_G>L\), \(b_G>7/100\) directly
in its exact projection. On \(s\ge0\),
\[
W-P_{G,1}>-2/3+(57/100)c+(847/800)s
\ge-29/300+(847/800)s-(57/175)s^2.
\]
The last polynomial is concave. Its values at the endpoints of
\([1/10,13/20]\) are \(4999/840000\) and
\(762563/1680000\), both positive. Thus a feasible G1 also has
\(s<1/10\). In either residual case the nonnegative domain is
\[
0\le s\le1/10,\qquad99/100\le c\le1,
\qquad1-c\le(100/199)s^2.
\tag{19}
\]

## 5. One five-circle stress excludes GA axis 3 on the whole negative arc

Assume G3 and \(s=-r\le0\). All of (14) applies. Define
\[
w=2/3,\quad u=9/20,\quad d=11/20,\quad
p=c+(5/8)r.
\]
Give the seven nominal inequalities, in cyclic order, the weights
\[
(w,1,p,p,u,d,1).
\tag{20}
\]
The common demand is
\[
D=w+2p+u+d+2W.
\]
The shared error is at most
\[
\mathcal L\le(K\cdot19/16+M)S
\le9643/102400<19/200.
\tag{21}
\]
Indeed \(p\le\sqrt{1+(5/8)^2}<19/16\), and all other aligned
weights are smaller; the squared comparison has reserve \(5/256\).

Write
\[
C_\mu(x,y)=\mu Q+\frac{x^2+y^2}{4\mu}-\frac{x+y}{2}.
\]
Every original corner satisfies
\[
xa_i+yb_i\le C_\mu(x,y)\qquad(\mu>0)
\tag{22}
\]
for arbitrary real force coordinates. This is the usual completed
square at \((a_i+1/2,b_i+1/2)\), with no contact assumption.

The common G,A,T,D forces after summing (20) are
\[
(a_G+w b_G)+r(a_A+(5/8)b_A)
 +(p a_T+u b_T)+(d a_D+u b_D).
\tag{23}
\]
Their bound from (22) is
\[
F_*=
C_{3/10}(1,w)+rC_{3/10}(1,5/8)
+C_{3/10}(p,u)+C_{9/50}(d,u).
\tag{24}
\]
The A inequality has simply been multiplied by \(r\ge0\). At
\(r=0\) it is omitted; there is no zero circle mass in a denominator.

For the four actual EH alternatives, the remaining forces and their
upper bounds are
\[
\begin{array}{c|l|l}
\text{EH}&\text{remaining force}&\text{bound}\!\\\hline
0&ca_H+(w-r)b_H+(d-1)b_E&C_{4/15}(c,w-r)\\
1&a_H+w b_H-r a_E+(d-c)b_E&C_{3/10}(1,w)-Lr\\
2&ca_E+(d-r)b_E+(w-1)b_H&C_{2/9}(c,d-r)\\
3&a_E+d b_E-r a_H+(w-c)b_H&C_{3/10}(1,d)-Lr.
\end{array}
\tag{25}
\]
Each omitted term is nonpositive: \(d<1\), \(d<c\), \(w<1\),
\(w<c\), \(b_H,b_E\ge0\), and \(a_H,a_E>L\). In particular,
no H cone is used in the last row. Let \(F_j\) be (24) plus the
corresponding bound in (25).

Expanding these four displayed circle bounds and using
\(c^2=1-r^2\) gives
\[
\begin{array}{c|l}
j&D-F_j\\\hline
0&\displaystyle
4c+\frac{2149759}{1200000}r-\frac{51318053}{13500000}
+\frac{65}{128}r^2-\frac{25}{24}cr\\[2pt]
1&\displaystyle
\frac72c+\frac{1920259}{1200000}r-\frac{44298823}{13500000}
+\frac{65}{128}r^2-\frac{25}{24}cr\\[2pt]
2&\displaystyle
4c+\frac{2134759}{1200000}r-\frac{205026647}{54000000}
+\frac{65}{128}r^2-\frac{25}{24}cr\\[2pt]
3&\displaystyle
\frac72c+\frac{1920259}{1200000}r-\frac{5436181}{1687500}
+\frac{65}{128}r^2-\frac{25}{24}cr.
\end{array}
\tag{26}
\]
These are four intrinsic EH force identities. For example,
\(p^2=c^2+(5/4)cr+(25/64)r^2\), which accounts for the common
\(-25cr/24\) term; no angle or state cells are introduced.

Apply \(c\ge1-(100/183)r^2\) and \(cr\le r\). Coefficientwise
rational comparisons in (26) give the simpler lower bounds
\[
\begin{array}{ll}
j=0,2:&D-F_j\ge99/500+(737/1000)r-(839/500)r^2,\\
j=1,3:&D-F_j\ge437/2000+(1117/2000)r-(281/200)r^2.
\end{array}
\tag{27}
\]
To make the comparisons checkable, the exact coefficient triples
before the harmless rational weakenings are
\[
\begin{array}{c|ccc}
j&1&r&r^2\\\hline
0&2681947/13500000&899759/1200000&-39305/23424\\
1&2951177/13500000&670259/1200000&-32905/23424\\
2&10973353/54000000&884759/1200000&-39305/23424\\
3&470069/1687500&670259/1200000&-32905/23424.
\end{array}
\]
Both polynomials in (27) are concave on the **whole** interval
\([0,11/20]\). The even-index polynomial has endpoint values
\(99/500\) and \(19151/200000\); the odd-index polynomial has
endpoint values \(437/2000\) and \(8053/80000\). Each exceeds
\(19/200\). Consequently every original EH witness yields
\[
D-F_j-\mathcal L>19/200-9643/102400
=17/20480>0,
\]
contradicting its necessary weighted inequality. This excludes G3
without preselecting an EH owner. Together with Section 4.1, every
feasible GA witness now belongs to \(\{0,1\}\) in the retained
forbidden-BT branch.

## 6. EH axes 2 and 3 fail for both residual GA axes

The four following sums retain the actual original witnesses. Every
HG and EH weight lies in \([0,1]\), so (10) gives their complete loss.

### 6.1 G0 with E2

The sum HG+G0+E2 has demand \(1+2W\) and force
\[
c(a_A+a_E)+s(b_E-b_A).
\]
Since \(a_A+a_E<7/6+U=1549/600\) and
\(|b_E-b_A|<9/10\), its gap is at least
\[
2-(949/600)c+|s|/10\ge251/600>71/800.
\]

### 6.2 G0 with E3

Use the sum \(c\,\mathrm{HG}+c\,\mathrm{G0}+\mathrm{E3}\).
The demand is \(c+(1+c)W\), and the force is
\[
c^2a_A-cs b_A+a_E+s a_H.
\]
For \(s\ge0\), (19) gives demand at least \(59401/20000\).
The force is at most \(1549/600+U/10\). Their difference exceeds
\(1/5>71/800\).

For \(s=-r\le0\), retain the \(c^2\) term, use
\(a_H>L\), \(b_A<9/10\), and obtain the lower gap
\[
-183/200+2c-(2/3)c^2+(127/800+c/2)r.
\]
The function \(2c-(2/3)c^2\) increases on \([83/100,1]\).
Its value at \(83/100\), after subtracting \(183/200\),
exceeds \(1/4\), and the r coefficient is positive. The gap again
exceeds (10).

### 6.3 G1 with E2

Use \(c\,\mathrm{HG}+\mathrm{G1}+c\,\mathrm{E2}\).
The demand is \(c+(1+c)W\), and the force is
\[
a_A-sa_G+c^2a_E+cs b_E.
\]
For \(s\ge0\), this force is at most \(1549/600+9/100\);
the demand is at least \(59401/20000\), leaving more than \(1/4\).

For \(s=-r\le0\), use \(a_G<V\) and discard \(-crb_E\).
The gap is at least
\[
-2/3+2c-(183/200)c^2+r((1+c)/2-V).
\]
The quadratic in c increases on \([83/100,1]\). Also
\((1+c)/2-V\ge183/200-V<0\). Thus the gap is at least
\[
-2/3+2(83/100)-(183/200)(83/100)^2
+(183/200-V)(11/20)
=590639/6000000>71/800.
\tag{28}
\]

### 6.4 G1 with E3

Use \(c\,\mathrm{HG}+\mathrm{G1}+\mathrm{E3}\).
The demand is \(c+2W\), and the force is
\[
a_A+a_E+s(a_H-a_G).
\]
For \(s\ge0\), (19), \(a_H<U\), \(a_G>L\) give gap at least
\(1+2(99/100)-1549/600>1/3\); the remaining sine coefficient
\(1-U+L\) is positive.

For \(s=-r\le0\), use \(a_G<V\), \(a_H>L\) and the chord in
(8). The gap is at least
\[
251/600+(651/4000)r-(8/7)r^2.
\]
This polynomial is concave on \([0,11/20]\). Its endpoint values
are \(251/600\) and \(272381/1680000\), both greater than
\(71/800\).

Every E2/E3 witness has therefore been excluded. The only remaining
intrinsic pairs are \((G0,E0),(G0,E1),(G1,E0),(G1,E1)\).

## 7. A four-circle stress on the entire nonnegative arc and the short negative arc

Use the same geometric stress as `HAND_QUARTER_OWNER_CLOSURE.md`,
but with the stronger nominal error (4) and with the actual weaker
primary bounds derived here. The force derivation is recorded in full
to specify exactly which earlier hypotheses are unnecessary.

Set
\[
p_0=7/10,\quad u_0=1/4,\quad d_0=3/10,\quad e_0=11/10,
\]
and use cyclic weights
\[
(h,1,p_0,p_0,u_0,d_0,e_0),
\qquad h=1\text{ for G0},\quad h=c\text{ for G1}.
\tag{29}
\]
The demand is \(D=h+39/20+(21/10)W\). All aligned weights are
at most one, so the complete loss is
\[
\mathcal L\le(K+e_0M)S\le6063/64000.
\tag{30}
\]

The T and D forces are \((p_0,u_0)\) and \((d_0,u_0)\).
The A force is \((c,p_0-s)\) for G0 and \((1,p_0)\) for G1.
For E0 the H force is \((e_0c,h+e_0s)\), and the leftover
\((d_0-e_0)b_E\) is nonpositive. For E1 the H force is
\((e_0,h)\), with leftovers
\[
e_0s a_E+(d_0-e_0c)b_E\le e_0s a_E.
\]
The G1 case additionally has \(-s a_G\). The last two upper bounds
use only the signs of s and the primary bounds:
\[
\begin{array}{c|cc}
&A_E\text{ in }e_0s a_E\le e_0s A_E
&A_G\text{ in }-s a_G\le-s A_G\\\hline
s\ge0&U&L\\
s\le0&L&V.
\end{array}
\]
There is no G tangent cone in this table.

Apply (22) on A,T,D,H with masses
\[
(3/10,3/16,1/10,3/8).
\]
Their sum is \(77/80\). Put
\[
B=9281/2400-(77/80)Q=58991/600000.
\]
The demand minus the resulting force bound has the following four
identities, with subscripts denoting the actual G and E axes:
\[
\begin{aligned}
\Psi_{00}&=B+\tfrac{21}{10}(c-1)+\tfrac{21}{20}|s|-\tfrac14s,\\
\Psi_{01}&=B+\tfrac{31}{20}(c-1)+\tfrac{21}{20}|s|
+(\tfrac23-\tfrac{11}{10}A_E)s,\\
\Psi_{10}&=B+\tfrac{31}{10}(c-1)+\tfrac23s^2+\tfrac{21}{20}|s|
+(\tfrac{11}{20}+A_G-\tfrac{22}{15}c)s,\\
\Psi_{11}&=B+\tfrac{51}{20}(c-1)+\tfrac23s^2+\tfrac{21}{20}|s|
+(A_G-\tfrac{11}{10}A_E)s.
\end{aligned}
\tag{31}
\]
They follow by direct substitution of the preceding four forces in
(22); in particular \(c^2+(p_0-s)^2=1+p_0^2-2p_0s\).

### 7.1 All nonnegative s

By (19), \(0\le s\le1/10\), with
\(1-c\le(100/199)s^2\). For the first three expressions, insert
\(A_E=U,A_G=L\); the resulting lower linear coefficients are
\[
4/5,\qquad961/6000,\qquad1661/2400.
\]
In each case the negative c-chord contribution is smaller than this
coefficient times s over the complete interval, so \(\Psi\ge B\).
For the fourth expression the exact useful lower bound is
\[
\Psi_{11}\ge B+(209/4000)s-(367/597)s^2>B-1/1000.
\]
The displayed quadratic is concave, with endpoint values zero and
\(-22027/23880000>-1/1000\). Thus all four original owner pairs
satisfy \(\Psi\ge B-1/1000\), and
\[
\Psi-\mathcal L\ge B-1/1000-6063/64000
=12403/4800000>0.
\tag{32}
\]
Every nonnegative-sine possibility is excluded.

### 7.2 G0 on all nonpositive s

Put \(s=-r\) and use (14). The first two expressions in (31) are
\[
\Psi_{00}=B-\tfrac{21}{10}(1-c)+\tfrac{13}{10}r,
\qquad
\Psi_{01}=B-\tfrac{31}{20}(1-c)+\tfrac{23951}{24000}r.
\]
As \(1-c\le r/3\), both are at least B on the entire negative
arc. They exceed the loss (30).

### 7.3 G1 on the short nonpositive arc

For \(0\le r\le1/4\), use \(c\ge9/10\) and
\(1-c\le(4/7)r^2\). The last two expressions in (31), with
\(A_E=L,A_G=V\), obey
\[
\begin{aligned}
\Psi_{10}&\ge B+(53/125)r-(116/105)r^2\ge B,\\
\Psi_{11}&\ge B+(2149/8000)r-(83/105)r^2\ge B.
\end{aligned}
\]
The linear coefficient after using \(r\le1/4\) is positive in
both lines. These cases also contradict (30).

## 8. One five-circle stress on the remaining G1 negative arc

Only G1 with E0 or E1 and
\[
1/4\le r\le11/20
\tag{33}
\]
remains. Use the same actual witness on each edge, and set
\[
p=13/20,\quad u=9/40,\quad d=1/4,\quad e=17/10,
\qquad h=c+(3/5)r.
\]
Give the seven inequalities weights
\[
(h,1,p,p,u,d,e).
\tag{34}
\]
Its demand is \(D=h+2p+u+d+(1+e)W\). Since
\[
h\le\sqrt{1+(3/5)^2}<7/6
\quad\text{with squared reserve }1/900,
\]
the complete shared error is
\[
\mathcal L\le(K\cdot7/6+M\cdot17/10)S
\le3251/24000.
\tag{35}
\]

The common A,G,T,D force bound is
\[
F_*=
C_{3/10}(1,p)+rC_{3/10}(1,3/5)
+C_{7/40}(p,u)+C_{17/200}(d,u).
\tag{36}
\]
Indeed \(h-c=(3/5)r\) leaves the G force
\(r(a_G+(3/5)b_G)\); the equal A/B weights cancel the B coordinate.
The H/E forces for E0 and E1 are respectively
\[
\begin{array}{c|l|l}
\text{EH}&\text{remaining force}&\text{bound}\\\hline
0&ec a_H+(h-er)b_H+(d-e)b_E&C_{17/40}(ec,h-er)\\
1&e a_H+h b_H-er a_E+(d-ec)b_E&C_{21/40}(e,h)-eLr.
\end{array}
\tag{37}
\]
The omitted terms have their indicated signs because
\(d<e\), \(d<ec\), \(r,b_E\ge0\), and \(a_E>L\).
Let \(F_0,F_1\) be (36) plus these bounds. Direct substitution into
(22), followed by \(c^2=1-r^2\), gives
\[
\begin{aligned}
D-F_0={}&\frac{37}{10}c-\frac{8101}{75000}r
-\frac{82871557}{22312500}+\frac{134}{85}r^2+\frac{22}{17}cr,\\
D-F_1={}&\frac{57}{20}c+\frac{1015117}{600000}r
-\frac{125835229}{44625000}+\frac{32}{105}r^2-\frac47cr.
\end{aligned}
\tag{38}
\]
These two supports cover the entire remaining arc, not selected angle
points.

Use (14), with \(cr\ge(83/100)r\) in the first row and
\(cr\le r\) in the second. The resulting exact quadratic
coefficient triples are
\[
\begin{array}{c|ccc}
&1&r&r^2\\\hline
0&-315307/22312500&1231783/1275000&-6928/15555\\
1&1346021/44625000&4705819/4200000&-8023/6405.
\end{array}
\]
Coefficientwise weakening gives the particularly simple bounds
\[
\begin{aligned}
D-F_0&\ge-3/200+(24/25)r-(9/20)r^2,\\
D-F_1&\ge3/100+(28/25)r-(63/50)r^2.
\end{aligned}
\tag{39}
\]
Both polynomials are concave on (33). The first has endpoint values
\(63/320\) and \(603/1600\); the second has endpoint values
\(37/160\) and \(5297/20000\). All exceed \(19/100\).
Consequently
\[
D-F_j-\mathcal L>19/100-3251/24000
=1309/24000>0,
\]
contradicting either original EH witness. This completes the last
negative-sine possibility.

## 9. Owner quantifiers, exact coverage and remaining scope

Retain any putative feasible forbidden BT witness, including one tied
with an intended BT axis. The independently established DE theorem
supplies an intended DE witness without using BT or any tangent cut.
Select any feasible original GA witness. Section 4 excludes axis 2;
Sections 4--5 exclude axis 3 for both sine signs and all four original
EH witnesses. Hence GA must be 0 or 1. Section 6 excludes every feasible
E2/E3 witness for either GA choice. For the remaining E0/E1 choices,
Section 7 covers all nonnegative sine, all negative sine with G0, and
the complete short negative arc with G1; Section 8 covers the remaining
G1 arc. Every possibility is contradictory. The retained forbidden BT
witness therefore cannot exist. This proves (2) for every originally
feasible axis, including all ties.

The conditional theorem uses only the G0--G2 entry facts, the E sign,
the globally proved zero owners, original corner disks, and (1).
Its new negative-tilt bound uses HG and all EH axes, with no H cone.
The two five-circle stresses collect both incident forces at each
actual shared vertex before applying a corner support. All aligned
losses spend the same S; the EH error is the sum of those same five
frame increments. No subsequent sign, cut, owner, mismatch bound,
radial contact, or equality location has been inserted in reverse.

The scalar identities, rational coefficient comparisons, and endpoint
reserves were checked with exact rational arithmetic. The proof itself
is given by the displayed original-witness sums, square completions,
and concavity inequalities. There is no generated angle/state cover,
owner-certificate lookup, Bernstein row, numerical PASS, or external
acceptance premise. No Lean source, historical table, compilation,
or CI run is changed or used here.

Both quarter-owner restrictions are thus available already at
\(S\le1/32\), without any G3 tangent cut. The global bound on S and
the remaining global tangent/capture implications still require proof.
