# Every DE witness has its intended quarter direction at S <= 1/32, without tangent cuts

## 1. The theorem and its inputs

Assume the actual G0--G2 candidate geometry at
\[
q\le Q=9789/2500,
\qquad S=|d_H|+|d_A|+|d_B|+|d_T|+|d_D|\le1/32.
\tag{1}
\]
The roles are \((H,G,A,B,T,D,E)\), with quarter word \(0101011\),
own-frame centers \((a_i,-y_i)\), \(a_i\ge|y_i|\), and
\(u_E\le0\). The global zero-primary theorem is available, so
every feasible original witness on HG, AB and TD belongs to axes
\(\{0,2\}\). Then
\[
\boxed{\text{every actually feasible original DE axis belongs to }
\{2,3\}.}                                             \tag{2}
\]

This theorem assumes **none** of the G/T/H/D tangent cuts, a prescribed
sign on the six zero-edge roles, an earlier quarter owner, either mixed
owner, a tilt window, or a radial-boundary kind. It works with original
contained centers. The input (1) is still a mismatch-capture hypothesis;
this note does not prove it globally.

## 2. Elementary bounds and exact nominal statements

Write
\[
L=447/800,\qquad U=283/200,\qquad \rho=1/32.
\]
The entry core bound and actual corner containment give
\[
a_i>L,\quad |p_i|<U,\quad a_i<U,\quad |y_i|<9/10,
\quad a_i+|y_i|<9/5.                                 \tag{3}
\]
The center-norm proof and all-axis nominal estimate are in
`HAND_G3_CENTER_NORM_AND_HIGH_TAIL_DIRECTIONS.md`, Sections 1--2.
They use only the original corner disk and prove, for every original
feasible aligned witness with error \(e_i=|d_i|\le3/10\),
\[
P_i^{\rm nominal}\ge1-e_i.                            \tag{4}
\]
Both original zero axes have nominal projection \(y_i-y_{i+1}\).
Since \(1-\rho=31/32>9/10\), (3)--(4) on the three zero edges
force all six signs. Write their positive magnitudes as
\[
(y_H,y_G,y_A,y_B,y_T,y_D)
=(b_H,-b_G,b_A,-b_B,b_T,-b_D),
\qquad b_E=-y_E\ge0.                                 \tag{5}
\]
Their nominal inequalities are
\[
b_H+b_G\ge1-e_H,\quad b_A+b_B\ge1-e_A,
\quad b_T+b_D\ge1-e_T.                               \tag{6}
\]
The quarter projections at zero error are
\[
\begin{array}{c|cc}
&\text{axes 0,1}&\text{axes 2,3}\\\hline
BT&a_T-b_B&a_B-b_T\\
DE&a_E-b_D&a_D+b_E.
\end{array}                                          \tag{7}
\]
In what follows, ``forbidden'' means only the intrinsic original
indices 0 and 1 in (7); no owner has yet been excluded.

Normalize \(\theta_A=0\) and set
\[
t=\theta_G-\theta_A,\qquad c=\cos t,
\quad r=|\sin t|,\qquad W=(1+c+r)/2.
\]
The concentrated real frames give
\[
|t|<7/10,\qquad c\ge3/4,\qquad 0\le r\le13/20,
\qquad c^2+r^2=1,\qquad 1-c\le(4/7)r^2.              \tag{8}
\]
The bound on r follows from
\(\sin(7/10)\le7/10-(7/10)^3/6+(7/10)^5/120<13/20\).
The quadratic chord uses \(1+c\ge7/4\).

GA has exactly its actual phase \(\pi/2-t\). The nominal EH phase
is \(\pi/2+t\); its difference from the actual phase equals
\(-d_H-d_A-d_B-d_T-d_D\), of absolute value at most S.
The projection Lipschitz bound U and the width Lipschitz bound 1/2
therefore imply, for **every originally feasible EH witness**,
\[
P_E^{\rm nominal}\ge W-2S.                            \tag{9}
\]
The coefficient two is conservative, since \(U+1/2<2\). In each
combined HG--GA--EH inequality below, an HG weight at most one and
an EH weight at most one give total error at most
\[
e_H+2S\le3S\le3/32.                                 \tag{10}
\]

## 3. A forbidden DE witness forces both quarter directions to be forbidden

Retain a putative original forbidden DE witness. If some intended BT
witness were feasible, add its nominal inequality to TD and the
retained DE inequality. Both transverse coordinates cancel:
\[
a_B+a_E\ge3-e_B-e_T-e_D\ge3-\rho>2U.
\]
This contradicts (3), with reserve \(111/800\). Hence every feasible
BT witness is forbidden. Retain one, together with the original
forbidden DE witness, for the remainder of the proof.

The two actual nominal chains now give
\[
b_A+a_T\ge2-e_A-e_B,\qquad
b_T+a_E\ge2-e_T-e_D.                                 \tag{11}
\]
Let \(R=e_A+e_B+e_T+e_D=S-e_H\). Weight the second chain by 2/3.
The T circle completion with mass 3/10 is
\[
a_T+\frac23b_T\le\frac3{10}Q+\frac{10}{27}.
\]
Using \(a_E<U\) gives
\[
b_A>\frac{570341}{675000}-R>\frac{211}{250}-R.
\tag{12}
\]
The constant difference in the last comparison is \(641/675000\).
In particular \(b_A>211/250-1/32=3251/4000>81/100\).

One stronger A-circle support will be useful. Complete its corner
circle with force \((1,9/10)\) and mass 17/50:
\[
a_A+\frac9{10}b_A
\le\frac{17}{50}Q+\frac{181/100}{4(17/50)}-\frac{19}{20}
<\frac{137}{80}.                                    \tag{13}
\]
The final reserve is \(1333/4250000\). Combining (12)--(13),
\[
\boxed{b_A>81/100,\qquad a_A<99/100.}                  \tag{14}
\]
The first inequality and (13) actually give
\(a_A<1967/2000<99/100\).

We now exclude **each** of the four possible original GA witnesses.
The putative forbidden BT and DE witnesses remain fixed throughout.

## 4. GA axis 0: one shared error and one direction-circle support

Its actual projection is \(-b_G+a_Ac-b_A\sin t\). Replacing
\(-\sin t\) by r increases this projection. Add (6) on HG:
\[
b_H+a_Ac+b_Ar\ge W+1-e_H.                             \tag{15}
\]
On (8), \((9/10)c-r\ge27/40-13/20=1/40>0\).
Use (13) and the **shared** version of (12),
\(b_A>211/250-\rho+e_H\), in (15). With
\(C=137/80\), \(B=211/250\), it follows that
\[
\frac35
< (C-\tfrac9{10}(B-\rho)-\tfrac12)c
 +(B-\rho-\tfrac12)r
 +e_H(1-\tfrac9{10}c+r).
\]
The coefficient of \(e_H\) is nonnegative, so \(e_H\le\rho\)
gives the necessary strict inequality
\[
\frac35<\rho+\frac{4529}{10000}c+\frac{43}{125}r.
\tag{16}
\]
But a single unit-circle support gives
\[
\frac{4529}{10000}c+\frac{43}{125}r<\frac{91}{160},
\]
because the difference of squared norms is
\[
\left(\frac{91}{160}\right)^2-
\left(\frac{4529}{10000}\right)^2-
\left(\frac{43}{125}\right)^2
=\frac{8861}{400000000}>0.
\]
Since \(\rho+91/160=3/5\), this contradicts (16). Keeping
\(R=S-e_H\) in (12) is essential; spending S independently there
and on HG would lose this reserve.

## 5. GA axis 2: a rotated primary span

Add this actual GA projection to the nominal AB and forbidden BT
projections. Their A and B transverse terms cancel. Replacing the
signed sine term by its absolute upper bound gives
\[
a_Gc+b_Gr+a_T\ge W+2-e_A-e_B.
\]
The G corner completion with mass 1/4 gives
\[
c(a_G+1/2)+r(b_G+1/2)\le Q/4+1.
\]
Since \(c+r\ge1\), these imply
\[
a_T+Q/4\ge5/2-e_A-e_B\ge5/2-\rho>U+Q/4.
\]
The last reserve is \(1497/20000\), contradicting (3).

## 6. GA axis 1: all four EH witnesses on the entire negative half

If \(\sin t\ge0\), its projection
\(a_A-a_G\sin t-b_Gc\) is below one by (14). Thus
\(\sin t=-r<0\), and its actual necessary inequality is
\[
a_A+a_Gr-b_Gc\ge W.                                 \tag{17}
\]
The four nominal EH projections are
\[
\begin{array}{c|l}
0&a_Hc-b_Hr-b_E\\
1&a_H-a_Er-b_Ec\\
2&a_Ec-b_Er-b_H\\
3&a_E-a_Hr-b_Hc.
\end{array}                                          \tag{18}
\]
Because the retained DE witness is forbidden,
\(a_E-b_D\ge1-e_D\) gives \(a_E\ge1-\rho>19/20\).
All four original EH axes must obey (9).

Add HG with weight c to (17). Add EH with weight one, except that
EH axis 2 has weight c. This cancels the G transverse coordinate.
The exact forces and demands before error are
\[
\begin{array}{c|l|l}
\text{EH axis}&\text{force}&\text{demand}\\\hline
0&a_A+a_Gr+c a_H+(c-r)b_H-b_E&2W+c\\
1&a_A+a_H+c b_H+(a_G-a_E)r-b_Ec&2W+c\\
2&a_A+a_Gr+c^2a_E-crb_E&(1+c)W+c\\
3&a_A+a_E+(a_G-a_H)r&2W+c.
\end{array}                                          \tag{19}
\]
All weights lie in \([0,1]\), so (10) supplies the complete loss.

### 6.1 EH axis 0

For \(0\le r\le9/20\), use the H circle with mass 1/3 and
force \((c,c-r)\), together with \(a_A<99/100\), \(a_G<U\).
Demand minus the resulting force bound is at least
\[
3c-\frac{183}{200}r+\frac34r^2+\frac32cr
-\frac{149}{100}-\frac Q3.                            \tag{20}
\]
Here \(c\ge7/8\) and \(1-c\le(8/15)r^2\). Therefore the
four direction terms in (20) are at least
\[
3+\frac{159}{400}r-\frac{17}{20}r^2
\ge3+\frac3{200}r\ge3.
\]
The gap is consequently at least \(151/100-Q/3=128/625\).

For the entire complementary interval
\(9/20\le r\le13/20\), use mass 1/4 on the same H force.
The exact lower gap is
\[
3c-\frac{183}{200}r+r^2+2cr-\frac{199}{100}-\frac Q4.
\]
By (8) and \(cr\ge3r/4\), it is at least
\[
J(r)=\frac{311}{10000}+\frac{117}{200}r-\frac57r^2
>\frac1{10}.                                        \tag{21}
\]
Indeed J is concave and its endpoint reserves above 1/10 are
\(6959/140000\) and \(1339/140000\). Thus this one original
EH owner is excluded on both complete ranges, since
\(1/10>3/32\). The two circle choices are explicit full-interval
supports, with no subdivision into angle or state cells.

### 6.2 EH axis 1

Use the H force \((1,c)\) with mass 1/3, and
\(a_G-a_E<U-19/20=93/200\). The lower gap is
\[
\frac52c+\frac34r^2+\frac{107}{200}r
-\frac{99}{100}-\frac Q3.
\]
Using (8), its first three terms are at least
\[
\frac52+\left(\frac{107}{200}-\frac{19}{28}r\right)r
\ge\frac52,
\]
because \(r\le13/20\). The resulting gap is again at least
\(128/625>3/32\).

### 6.3 EH axis 2

The force in (19) is at most
\[
99/100+U(r+c^2)\le99/100+5U/4=2207/800,
\]
because \(r+c^2=1+r-r^2\le5/4\) and \(-crb_E\le0\).
Its demand is
\[
(1+c)W+c=1+2c-r^2/2+r/2+cr/2
\ge3+\frac78r-\frac{23}{14}r^2>287/100.
\]
The last concave quadratic has its minimum at an endpoint of
\([0,13/20]\); at 13/20 its reserve above 287/100 is 13/2800.
The gap therefore exceeds \(89/800>3/32\).

### 6.4 EH axis 3

The last force in (19) is at most
\(99/100+U+(U-L)r\). Its demand minus this bound is at least
\[
1-99/100-U+2c+(1-U+L)r
\ge19/200>3/32,
\]
using \(c\ge3/4\) and \(1-U+L=23/160>0\).
The exact final reserve is \(1/800\).

All four original EH witnesses are impossible. This excludes GA
axis 1 throughout its complete negative-tilt domain.

## 7. GA axis 3: direct short-tilt bounds and four large-tilt sums

If \(\sin t\ge0\), (14), \(a_G<U\), and \(c\ge3/4\)
give
\[
W-(a_G-a_A\sin t-b_Ac)\ge27/400>0.
\]
If \(\sin t=-r\le0\) and \(0\le r\le9/20\), then
\(c\ge89/100\) and
\[
W-(a_G+a_Ar-b_Ac)
\ge-\frac{183}{200}+\frac{131}{100}\frac{89}{100}
-\frac{49}{100}\frac9{20}=\frac{19}{625}>0.            \tag{22}
\]
It remains to treat the whole interval
\(9/20\le r\le13/20\), where the actual GA inequality is
\[
a_G+a_Ar-b_Ac\ge W.                                 \tag{23}
\]
Keep all four EH axes from (18), each obeying (9).

For EH axis 0, add HG with weight r to (23) and EH with weight one.
The force is
\[
(a_G+r b_G)+c a_H+a_Ar-b_Ac-b_E,
\]
and the demand is \(2W+r\). Complete the G circle with mass 1/4
and force \((1,r)\); bound the other terms by (3), (14), and
\(b_E\ge0\). The gap is at least
\[
-\frac{3653}{20000}+\frac{151}{100}r-r^2>29/100.
\tag{24}
\]
This concave quadratic has endpoint reserves above 29/100 equal to
\(87/20000\) and \(1727/20000\). It exceeds the complete error
\(r e_H+2S\le3S\).

For EH axis 1, no combination is needed. Since \(a_E>19/20\),
\[
W-P_{E1}^{\rm nominal}
\ge-27/50+(29/20)r\ge9/80>2S.                        \tag{25}
\]

For EH axis 2, add HG with weight one to (23) and EH with weight
one. The H transverse term cancels; the force is
\[
(a_G+b_G)+c a_E-rb_E+a_Ar-b_Ac,
\]
with demand \(2W+1\). Its gap is at least
\[
\frac15+\frac{79}{200}c+\frac1{100}r
\ge397/800>3S.                                      \tag{26}
\]
This uses \(a_G+b_G<9/5\), \(a_E<U\), (14), and the signs
of the discarded E term.

For EH axis 3, add HG with weight c. The force is
\[
(a_G+c b_G)+a_E-r a_H+a_Ar-b_Ac,
\]
with demand \(2W+c\). Bound \(a_G+c b_G<9/5\),
\(a_E<U\), \(a_H>L\), and use (14). The gap is at least
\[
-\frac{443}{200}+\frac{281}{100}c+\frac{91}{160}r
\ge19/128>3S,                                       \tag{27}
\]
using \(c\ge3/4\), \(r\ge9/20\).
Thus all four original EH axes fail on the complementary interval.
This completes the exclusion of GA axis 3.

## 8. Assembly, quantifiers and remaining global work

A putative original forbidden DE witness forced every BT witness to
be forbidden in Section 3. With one such actual BT witness retained,
Sections 4--7 exclude each of the four original GA axes. In each
branch requiring an EH witness, every one of its original four axes
is covered, including ties. Actual neighboring-square separation
guarantees a feasible GA witness and a feasible EH witness, giving
the contradiction. Therefore the putative DE witness does not exist,
which proves (2) for **every** originally feasible DE axis.

Only the signs (5), derived in the forward direction from (1), and
the weak E normalization were used. No H cone, D cone, G/T tangent
range, prescribed GA/EH witness, radial label, or future contraction
was inserted. The whole A coordinate estimate retains the shared
HG error in the one branch where that dependence is essential.
All centers in the supports remain the actual original centers.

This closes the full DE-owner component under \(S\le1/32\), earlier
and with fewer assumptions than its previous capture interface. It
does not prove the global mismatch hypothesis (1), intended BT
owners, every G3 tangent cut, or the unrestricted sharp theorem.
The intrinsic owner alternatives and the two explicit circle choices
in Section 6 are finite geometric cases, not a numerical variable
cover. All displayed reserves and force coefficients were checked
with exact rational arithmetic. No generated table, numerical PASS,
Lean compilation, or CI run is a proof premise or was introduced.
