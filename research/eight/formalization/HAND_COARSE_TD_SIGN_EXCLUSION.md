# The D sign is forced already at the coarse mismatch threshold

## 1. The precise theorem

Assume the established G0--G2 candidate geometry at
\(q\le Q=9789/2500\), with cyclic roles H,G,A,B,T,D,E and quarter
word 0101011. Retain every originally feasible signed separator. Write
an own-frame center as \((a_i,-y_i)\), where
\(a_i\ge |y_i|\), and put
\[
 I=\{H,A,B,T,D\},\qquad S=\sum_{i\in I}|d_i|.
\]
Assume only the additional conditions
\[
             S\le13/50,\qquad 0\le y_T\le(4/5)a_T.
\tag{1}
\]
Then
\[
                            \boxed{y_D<0.}           \tag{2}
\]
In particular the already-required T tangent cut supplies the second
hypothesis of (1). No G tangent cut, H/D tangent cut, E sign, mixed owner,
quarter owner, positive tilt, or contraction to S<=1/10 is an input.

This is a complete conditional sign theorem at the earlier G4 boundary.
It does not prove S<=13/50, the stronger D cut u_D<-1/2, or either G5
contraction. It must not be used to assume (1) in the global caller.

The only owner restriction used is the global G0--G2 theorem
`HAND_ZERO_PRIMARY_CYCLIC_EXCLUSION.md`: on each actual zero-quarter
edge, every feasible original axis is 0 or 2. The proof below retains
both original zero axes and all four original BT axes until they are
excluded. It works for original contained centers and every radial
chart, including chart joins and zero-coordinate ties.

## 2. Uniform containing-disk bounds

The actual farthest corner gives
\[
              (a_i+1/2)^2+(|y_i|+1/2)^2\le Q.
\tag{3}
\]
Consequently
\[
 a_i<U:=283/200,\qquad |y_i|<9/10,
 \qquad a_i+|y_i|<9/5,
 \qquad |p_i|<3/2.                                   \tag{4}
\]
For the first inequality, \((U+1/2)^2+1/4>Q\). For the next two,
use \(a_i\ge |y_i|\), \(2(7/5)^2>Q\), and Cauchy,
\((a_i+|y_i|+1)^2\le2Q<(14/5)^2\). The last inequality follows
because the square's radius-1/2 inscribed disk lies in a containing
disk of radius less than 2.

Write \(b=y_T\ge0\). The T cone in (1) improves its transverse bound:
\[
                            b<797/1000.              \tag{5}
\]
Indeed, otherwise \(a_T\ge(5/4)b\), and the corner in (3) would have
squared norm exceeding Q by at least
\[
 ((797/1000)/(4/5)+1/2)^2+(797/1000+1/2)^2-Q
                       =85969/16000000>0.
\]

## 3. A putative nonnegative D consumes more than 1/5 of S

Suppose, for contradiction, that \(y_D=B\ge0\), and put
\(A=a_D\), \(\delta=d_T\). The physical center-angle gap is
\[
 g_T=\delta+\arctan(b/a_T)-\arctan(B/A)>19/25.
\]
If \(\delta\le0\), its left side is at most \(\arctan(4/5)<7/10\),
a contradiction. The last comparison follows from the alternating bound
\[
 \arctan(4/5)\le4/5-(4/5)^3/3+(4/5)^5/5
                   =32572/46875<7/10.
\]
Thus \(0<\delta\le13/50\). Set \(c=\cos\delta\),
\(s=\sin\delta\), and \(W=(1+c+s)/2\).

The two remaining original TD projections are
\[
 P_0=b+A s-B c,\qquad P_2=a_Ts+bc-B.                 \tag{6}
\]
At least one is at least W.

The second one is impossible on the entire interval. Since c>=s,
\(b\le(4/5)a_T\), and \(a_T+b<9/5\),
\[
 a_Ts+bc\le\frac{a_T+b}{9}(5s+4c)<s+(4/5)c.
\]
Consequently
\[
 P_2-W<\tfrac12s+\tfrac3{10}c-\tfrac12
       \le\tfrac12(13/50)+\tfrac3{10}-\tfrac12
       =-7/100<0.                                   \tag{7}
\]
Therefore the originally feasible TD witness must be axis 0.
If \(\delta\le1/5\), (4)--(6) and the elementary bounds
\(s\le\delta\), \(c\ge1-\delta^2/2\) give
\[
\begin{aligned}
 P_0-W
 &<297/1000+(183/200)\sin\delta-(1/2)\cos\delta\\
 &\le297/1000+(183/200)(1/5)
                     -(1/2)(1-(1/5)^2/2)=-1/100.
\end{aligned}
\]
This too is impossible. Hence
\[
 \boxed{\delta>1/5,\qquad
 R:=S-\delta<3/50.}                                 \tag{8}
\]
Here R is the sum of the other four actual aligned errors, not a new
independent error allowance for each edge.

## 4. The same TD witness localizes T in two coordinates

Feasibility of axis 0 and B>=0 imply
\[
\begin{aligned}
 b&\ge W-As+Bc>W-Us\\
  &\ge1-(183/200)\delta-\delta^2/4\\
  &\ge1-(183/200)(13/50)-(13/50)^2/4
     =1863/2500.                                    \tag{9}
\end{aligned}
\]
The final quadratic decreases throughout the displayed interval.
Using (3) once more gives
\[
                            a_T<519/500.             \tag{10}
\]
Indeed the opposite inequality together with (9) would imply
\[
 (519/500+1/2)^2+(1863/2500+1/2)^2-Q
                         =1147/3125000>0.
\]

## 5. Use the remaining error sum only once on AB and BT

Let \(e_A=|d_A|\) and \(e_B=|d_B|\). Equation (8) gives
\(e_A+e_B\le R<3/50\). For any originally feasible axis on either
edge, its projection changes from the nominal quarter angle by at most
\(3e/2\), using the center norm in (4). Its width is at least
\[
                 1+e/2-e^2/4-e^3/12.
\]
Thus its nominal projection is at least
\[
 1-e-e^2/4-e^3/12\ge1-ke,
 \qquad k=127/125,                                  \tag{11}
\]
since, for \(0\le e\le3/50\),
\[
 k-(1+e/4+e^2/12)\ge7/10000>0.
\]

Both originally allowed AB axes have nominal projection y_A-y_B.
It follows that
\[
 y_A-y_B\ge1-ke_A>1-k(3/50)>9/10.
\]
By (4), this forces \(y_A>0\) and \(y_B<0\), including exclusion
of either zero coordinate. Write \(b_A=y_A\), \(b_B=-y_B\). Then
\[
                         b_A+b_B\ge1-ke_A.           \tag{12}
\]
This derives the needed A/B signs locally; it does not import the
later S<=1/10 sign theorem.

With these actual B and T signs, the four original BT axes have just
two nominal projections:
\[
 \begin{array}{c|c}
 \text{axes 0 and 1}&a_T-b_B\\
 \text{axes 2 and 3}&a_B-b.
 \end{array}
\tag{13}
\]
Neither high-index BT axis can be feasible. Its nominal projection is
strictly below \(U-1863/2500\) by (4),(9), whereas (11) requires it
to be greater than \(1-k(3/50)\). The exact reserve is
\[
 1-k(3/50)-(U-1863/2500)=6731/25000>0.
\]
Therefore any actually feasible BT witness must be axis 0 or 1. Add
its nominal bound from (11) to (12):
\[
 b_A+a_T\ge2-k(e_A+e_B)>2-k(3/50).
\tag{14}
\]
But (4),(10) give \(b_A+a_T<9/10+519/500\), and
\[
 \boxed{2-k(3/50)-(9/10+519/500)=13/12500>0.}          \tag{15}
\]
This is the required contradiction.

## 6. Coverage and effect on the remaining gates

The contradiction started with an arbitrary nonnegative D coordinate.
Both zero-quarter TD witnesses were included in (6), both zero-quarter
AB witnesses in (12), and all four BT witnesses in (13). A forbidden
witness tied with another feasible axis is excluded by the same strict
inequalities. All other centers, signs, radial kinds, and quarter/mixed
witnesses remain unrestricted.

The decisive mechanism is shared error allocation: a nonnegative D
forces d_T>1/5, leaving less than 3/50 for the AB--BT chain. Spending the
full 13/50 again on those two edges would invalidate the contradiction.
The containing-circle comparisons then force simultaneously
b_T>1863/2500 and a_T<519/500, which neither BT owner alternative can
accommodate.

This adds an earlier D-sign exclusion to G3--G5 work. The global T cut,
S<=13/50, the magnitude cut u_D<-1/2, and the two mismatch contractions
remain separate obligations. It is not a closure claim for an entire
remaining global gate. No Lean source or historical data was changed,
no Lean compilation or CI was run, and no numerical search result is a
premise of the proof.
