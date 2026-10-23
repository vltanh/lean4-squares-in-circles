# Exact prefix comparisons for a negative BT1 error

## 1. Scope: necessary caps and charge comparisons are distinct

Work on the actual G0--G2 boundary cycle at
\[
 Q=9789/2500,\quad c_0=\sqrt{Q/2}-1/2,\quad
 a_0=\sqrt{Q-1/4}-1/2,\quad K=7/12,\quad \kappa=49/50.
\tag{1}
\]
An outer state is on its Q-circle; a core state has primary
at most K. All states are sorted and have center norm less
than \(U=283/200\). The true core says that \(b\le1/2\)
implies \(a\ge K\). Retain the proved signs \(y_A=b_A>0\)
and \(y_T=b_T>0\), allowing either sign at B.

Let v be the AB error and let the BT1 error be \(-z\), with
\(0\le z<7/10\), \(|v|<7/10\). The original inequalities are
\[
\begin{aligned}
 AB0:\quad &b_A+a_B\sin v-y_B\cos v\ge W(|v|),\\
 AB2:\quad &a_A\sin v+b_A\cos v-y_B\ge W(|v|),\\
 BT1:\quad &a_T-a_B\sin z+y_B\cos z\ge W(z),
\end{aligned}
\quad W(r)=\frac{1+\cos r+\sin r}{2}.
\tag{2}
\]
Put
\[
 R_1(r)=1+\sec r\,W(r)+K\tan r
       =\frac32+\frac12\sec r+\frac{13}{12}\tan r.
\tag{3}
\]

For either AB owner with \(v\le0\), and for AB0 with
\(0\le v\le z\), the proof below gives an exact necessary cap
\[
                         b_A+\sec r\,a_T\ge R_1(r)
\tag{4}
\]
at the same actual centers, with the effective r specified
below. Consequently \(b_A\le c_0\) gives a stronger lower
bound on the actual T primary.

The other two branches admit charge comparisons, but those
comparisons alone do **not** imply (4). They cannot be used
to assume its stronger T-primary bound. Every construction
below is an inequality on the original centers; no new
feasible packing is asserted.

## 2. Elementary sign and primary bounds

If B has negative sign and BT1 is feasible, then \(b_B<1/2\).
Otherwise sorting gives
\[
 a_T\ge W(z)+a_B\sin z+b_B\cos z
       \ge\frac12+\cos z+\sin z\ge\frac32>U.
\tag{5}
\]
Thus \(a_B\ge K\) in this case.
For an AB2 witness with positive B sign, its projection
is at most \(|(a_A,b_A)|-b_B<U-b_B\). Feasibility gives
\(b_B<U-1<1/2\). Therefore
\[
                    a_B\ge K\quad\hbox{in every AB2 case}.
\tag{6}
\]

If \(v\le0\), either AB owner forces B negative: for
\(y_B\ge0\) its projection is at most \(b_A<.9<1\).
Its projection is at most \(b_A+b_B\), whereas BT1 is at
most \(a_T-b_B\), using sorting and \(\sin z\ge1-\cos z\).
Adding the contacts gives
\[
 b_A+a_T\ge2,\qquad b_A>2-U=.585>K.
\tag{7}
\]
A is therefore outer. Its sorted Q-circle gives
\[
                              a_A\ge c_0>.899.
\tag{8}
\]
The outer-boundary premise is explicit; (8) is not asserted
for an arbitrary interior point of the corner disk.

## 3. AB0 with nonpositive error

Put \(v=-w\le0\). Multiply AB0 by \(\sec w\) and BT1 by
\(\sec z\); the signed B tangent cancels. Equations (5)--(6)
give
\[
 b_A\sec w+a_T\sec z\ge
 \sec w\,W(w)+\sec z\,W(z)+K(\tan w+\tan z).
\]
Equivalently,
\[
 b_A+a_T\sec z\ge R_1(z)+J(w),\qquad
 J(w)=\frac{13}{12}\tan w+
                 (\tfrac12-b_A)(\sec w-1).
\tag{9}
\]
Since \(b_A<.9\),
\[
 J(w)\ge\frac{13}{12}\tan w-\frac25(\sec w-1)
                         \ge\frac{41}{40}w.
\tag{10}
\]
For the last inequality, multiply the derivative difference
by \(\cos^2w\). Its lower bound is the positive quadratic
\[
 \frac{41}{40}\sin^2w-\frac25\sin w+\frac7{120}
 =\frac{41}{40}\left(\sin w-\frac8{41}\right)^2
                         +\frac{19}{984}>0.
\tag{11}
\]
Thus (4) holds with \(r=z\), and
\[
 v-z+\kappa b_A\ge
 -z+\kappa\{R_1(z)-\sec z\,a_T\}+\frac9{2000}|v|.
\tag{12}
\]

## 4. AB0 with 0<=v<=z

First \(|y_B|<1/2\). The negative case is (5).
If instead \(y_B=b_B\ge1/2\), its circle gives \(a_B<1.208\).
For \(v\le.41\), AB0 is strictly below
\[
 .9+1.208(.41)-\tfrac12\{1-(.41)^2/2\}
                     =\frac{187461}{200000}<1.
\tag{13}
\]
Hence \(v>.41\). Adding AB0 and BT1, using \(z\ge v\), gives
\[
\begin{aligned}
 b_A+a_T&\ge W(v)+W(z)+a_B(\sin z-\sin v)
                              +b_B(\cos v-\cos z)\\
         &\ge2W(v)>2W(.41)>2.315.
\end{aligned}
\tag{14}
\]
This contradicts \(b_A+a_T<c_0+U<2.315\).
The degree-6 lower cosine and degree-3 lower sine polynomials
at .41 give the last comparison with exact reserve
\(456458195759/720000000000000>0\).
Thus \(a_B\ge K\).

Set \(r=z-v\), multiply BT1 by \(\sec r\), and add AB0.
Their B force is \(-\tan r(a_B\cos v+y_B\sin v)\).
Consequently
\[
 b_A+\sec r\,a_T\ge N(v),
\quad
 N(v)=W(v)+\sec r\,W(v+r)
                   +\tan r(K\cos v-\tfrac12\sin v).
\tag{15}
\]
At fixed r, throughout the segment to the original v,
\[
\begin{aligned}
 N'(v)
 &=\cos v-\sin v-\tan r\{\cos v+(13/12)\sin v\}\\
 &=\frac{\cos(v+r)-\sin(v+r)
                     -(1/12)\sin r\sin v}{\cos r}
 >\frac1{60}.
\end{aligned}
\tag{16}
\]
Here \(\cos(v+r)>.75\), \(\sin(v+r)<.65\), and
\(\sin r\sin v\le1\). Since \(N(0)=R_1(r)\), this proves
\[
 \boxed{b_A+\sec r\,a_T\ge R_1(r)+v/60,\qquad r=z-v.}
\tag{17}
\]
The prefix angle already equals \(-r\), so
\[
 v-z+\kappa b_A\ge
 -r+\kappa\{R_1(r)-\sec r\,a_T\}+\kappa v/60.
\tag{18}
\]

## 5. AB2 at either sign

Eliminating \(y_B\) and using (6) gives
\[
 b_A+\sec z\,a_T\ge R_1(z)+J_2(v),
\quad
 J_2(v)=W(|v|)-1-a_A\sin v+b_A(1-\cos v).
\tag{19}
\]
For \(v=-w\le0\), (8) yields
\[
 J_2(-w)=(a_A+\tfrac12)\sin w+
                     (b_A-\tfrac12)(1-\cos w)
 \ge1.399\sin w-\tfrac12(1-\cos w).
\]
Taylor bounds therefore give
\[
 -w+\kappa J_2(-w)\ge
 w\{-1+\kappa(1.399)-\kappa w/4-\kappa(1.399)w^2/6\}
 >\frac2{25}w.
\tag{20}
\]
The brace decreases on \([0,.7]\) and has endpoint value
\(2626601/30000000>2/25\). Thus this branch supplies (4)
with \(r=z\), and a strict charge improvement when \(v<0\).

For \(v\ge0\), however,
\[
 J_2(v)=-(a_A-\tfrac12)\sin v+
                    (b_A-\tfrac12)(1-\cos v)
 \ge-.915\sin v-\tfrac12(1-\cos v).
\tag{21}
\]
The degree-5 upper sine polynomial and quadratic cosine
bound give
\[
 v+\kappa J_2(v)\ge
 v\{1-\kappa(.915)-\kappa v/4
          +\kappa(.915)(1/6-.49/120)v^2\}
 >\frac3{1000}v\quad(v>0).
\tag{22}
\]
The quadratic in braces decreases on \([0,.7]\); its endpoint
value is \(12945411/4000000000>3/1000\).
This is a valid charge comparison. The remainder \(J_2(v)\)
itself can be negative, so (4) does not follow in this branch.

## 6. AB0 with v>=z: compare to the aligned-prefix charge

Put \(\eta=v-z\ge0\), and give both contacts weight kappa.
Their force on the signed B coordinates is
\[
 \kappa(\sin v-\sin z,-\cos v+\cos z)
 =2\kappa\sin(\eta/2)
          (\cos(z+\eta/2),\sin(z+\eta/2)).
\tag{23}
\]
Both components are nonnegative. Since
\(z+\eta/2\le.7<\pi/4\), their sum is at least its value
at z=0, so shifted-circle support is at most its z=0 value.
Also \(W(v)+W(z)\ge W(\eta)+1\). It follows that
\[
 \eta+\kappa(b_A+a_T-2)\ge
 f_\kappa(\eta):=\eta+\kappa\sin\eta
                         -2\kappa\sqrt Q\sin(\eta/2)\ge0.
\tag{24}
\]
Section 3.1 of HAND_G3_GLOBAL_BT0_DE2_PATH_EXCLUSION.md
proves the last inequality on the whole interval: the
function is concave, vanishes at zero, and has an explicitly
positive rational lower bound at .7.

This prefix is therefore at least the aligned-prefix charge
\(\kappa(2-a_T)\). A subsequent full-circle T support bound
may be used. In contrast, (24) does not imply
\(b_A+a_T\ge2\) at the unchanged centers.

## 7. The stronger T cap in exactly the necessary-cap branches

Sections 3--4 and the nonpositive branch of Section 5 give
\[
 \boxed{a_T\ge A(r):=\frac12+
              (\frac32-c_0)\cos r+\frac{13}{12}\sin r.}
\tag{25}
\]
This follows from (4) and \(b_A\le c_0\). T is outer because
\(A(0)=2-c_0>1.1>K\). The function A increases on \([0,.7]\):
its derivative exceeds \((13/12)(3/4)-.601(13/20)>0\).
Moreover
\[
                              r<13/40=.325.
\tag{26}
\]
Use \(c_0<179843/200000\) and the degree-6 lower cosine and
degree-3 lower sine polynomials at \(13/40\); they give
\[
 A(13/40)-283/200>
          \frac{14387738667443}{65536000000000000}>0,
\]
contradicting the universal primary bound if (26) failed.

The actual T circle may be supported on its restricted arc
\(a_T\ge A(r)\) precisely in these branches. This supplies
the exact entry hypothesis of
HAND_G3_NEGATIVE_BT1_HIGH_PRIMARY_DUAL_TRANSPORT.md.
The charge-only comparisons have deliberately been kept
separate. A complete BT1 exclusion still needs the T--D--E
tail bounds and a treatment of positive AB2 with its
retained remainder. No sampled minimum is a premise here.
